# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

using Test
using InteractiveUtils: code_llvm
using FastIdentifiers: FastIdentifiers, AbstractIdentifier, MalformedIdentifier,
    ChecksumViolation, shortcode, purl, purlprefix, idcode, idchecksum, parsebytes, @defid
using FastIdentifiers.DefId.Checksums: mod10, mod11_2

# --- AST complexity analysis utilities ---
# Clean raw @macroexpand output: strip hygiene wrappers, line numbers,
# gensym mangling, and GlobalRefs to produce a readable AST.
function exprclean!(expr::Expr)
    if expr.head == :.
        return last(expr.args).value
    elseif expr.head == :toplevel
        return exprclean!(Expr(:block, expr.args...))
    elseif expr.head == Symbol("hygienic-scope")
        return exprclean!(first(expr.args))
    elseif expr.head == :escape
        return if first(expr.args) isa Expr
            exprclean!(first(expr.args))
        else
            first(expr.args)
        end
    end
    delat = Int[]
    for (i, arg) in enumerate(expr.args)
        if arg isa Symbol && '#' in String(arg)
            segs = split(String(arg), '#')
            expr.args[i] = if all(isdigit, last(segs)) && length(segs) > 1
                Symbol(segs[end-1] * '_' * segs[end])
            else
                Symbol(last(split(String(arg), '#')))
            end
        elseif arg isa Expr
            expr.args[i] = exprclean!(arg)
        elseif arg isa GlobalRef
            expr.args[i] = arg.name
        elseif arg isa LineNumberNode
            if expr.head === :macrocall
                expr.args[i] = LineNumberNode(0, Symbol(""))
            else
                push!(delat, i)
            end
        end
    end
    deleteat!(expr.args, delat)
    expr
end

# Walk a cleaned AST to find the parsebytes function body.
function extract_parsebytes(expr::Expr)
    if expr.head == :function
        sig = expr.args[1]
        if sig isa Expr && any(a -> a === :parsebytes, sig.args)
            return expr.args[2]
        end
    end
    for a in expr.args
        a isa Expr || continue
        r = extract_parsebytes(a)
        !isnothing(r) && return r
    end
    nothing
end

# --- Control-flow-aware AST cost walker ---
#
# Walks all real execution paths through an expression, accumulating
# (min, max, total) costs. `cost_fn(expr) -> (lo, hi, total)` provides
# per-node weights. The walker handles control flow:
#   - if/elseif: condition always runs, then min/max over then/else arms
#   - &&/||: left always runs, right is conditional
#   - @goto/@label: when a path hits @goto L it continues from @label L
#   - blocks: statements run sequentially, with @label indexing for gotos
#
# Continuation-passing: each branch receives the "rest of the block" as
# its continuation, so a @goto inside an if-body correctly resolves to
# the post-label code rather than the sequential next statement.

is_goto_expr(e) = e isa Expr && e.head === :macrocall && !isempty(e.args) &&
    e.args[1] in (Symbol("@goto"), GlobalRef(Base, Symbol("@goto")))
is_label_expr(e) = e isa Expr && e.head === :macrocall && !isempty(e.args) &&
    e.args[1] in (Symbol("@label"), GlobalRef(Base, Symbol("@label")))
goto_label_sym(e) = e.args[end]

# Label context: maps label symbols to (stmts, index) so @goto can
# resolve to the right position in the right block.
const LabelCtx = Dict{Symbol, @NamedTuple{stmts::AbstractVector, pos::Int}}

"""
    walk_expr(cost_fn, expr; labels, cont) -> (lo, hi)

Walk `expr` then its continuation `cont`, computing min/max costs across
all real execution paths. `cost_fn(expr) -> Int` gives the per-node weight.

- `labels`: maps label symbols to their block position, for @goto resolution
- `cont`: `() -> (lo, hi)` representing the cost of everything after this
  expression on the current path
"""
function walk_expr(cost_fn, expr; labels::LabelCtx=LabelCtx(), cont=() -> (0, 0))
    expr isa Expr || return cont()
    if is_goto_expr(expr)
        sym = goto_label_sym(expr)
        target = get(labels, sym, nothing)
        if !isnothing(target)
            return walk_stmts(cost_fn, target.stmts, target.pos + 1, labels)
        end
        return cont()
    end
    is_label_expr(expr) && return cont()
    n = cost_fn(expr)
    clo, chi = if expr.head in (:if, :elseif) && !(expr.args[1] isa Bool)
        walk_branch(cost_fn, expr, labels, cont)
    elseif expr.head in (:&&, :||)
        walk_shortcircuit(cost_fn, expr, labels, cont)
    elseif expr.head === :block
        walk_block(cost_fn, expr.args, labels, cont)
    else
        walk_children(cost_fn, expr.args, labels, cont)
    end
    (n + clo, n + chi)
end

function walk_children(cost_fn, args, labels, cont)
    lo, hi = 0, 0
    for a in args
        alo, ahi = walk_expr(cost_fn, a; labels, cont=() -> (0, 0))
        lo += alo; hi += ahi
    end
    clo, chi = cont()
    (lo + clo, hi + chi)
end

# if/elseif: condition always runs, then min/max over then/else arms.
# Each arm receives the same continuation (code after the if).
function walk_branch(cost_fn, expr, labels, cont)
    cond_lo, cond_hi = walk_expr(cost_fn, expr.args[1]; labels)
    then_lo, then_hi = walk_expr(cost_fn, expr.args[2]; labels, cont)
    else_lo, else_hi = if length(expr.args) >= 3
        walk_expr(cost_fn, expr.args[3]; labels, cont)
    else
        cont()
    end
    (cond_lo + min(then_lo, else_lo),
     cond_hi + max(then_hi, else_hi))
end

# &&/||: left always runs, right is conditional.
function walk_shortcircuit(cost_fn, expr, labels, cont)
    left_lo, left_hi = walk_expr(cost_fn, expr.args[1]; labels)
    skip_lo, skip_hi = cont()
    right_lo, right_hi = walk_expr(cost_fn, expr.args[2]; labels, cont)
    (left_lo + min(skip_lo, right_lo),
     left_hi + max(skip_hi, right_hi))
end

function walk_block(cost_fn, stmts, labels, cont)
    local_labels = copy(labels)
    for (i, s) in enumerate(stmts)
        if is_label_expr(s)
            local_labels[goto_label_sym(s)] = (; stmts, pos=i)
        end
    end
    walk_stmts(cost_fn, stmts, 1, local_labels, cont)
end

function walk_stmts(cost_fn, stmts, start::Int, labels::LabelCtx, cont=() -> (0, 0))
    start > length(stmts) && return cont()
    rest = () -> walk_stmts(cost_fn, stmts, start + 1, labels, cont)
    walk_expr(cost_fn, stmts[start]; labels, cont=rest)
end

# Total unique cost: simple recursive sum over all AST nodes, no path sensitivity.
function walk_total(cost_fn, expr)
    expr isa Expr || return 0
    n = cost_fn(expr)
    for a in expr.args
        n += walk_total(cost_fn, a)
    end
    n
end

# Branch counter: (min, max, total).
function count_branches(expr)
    cost_fn = e -> begin
        if e.head in (:if, :elseif)
            Int(!(e.args[1] isa Bool))
        elseif e.head in (:&&, :||)
            Int(!(e.args[1] isa Bool))
        else
            0
        end
    end
    lo, hi = walk_expr(cost_fn, expr)
    tot = walk_total(cost_fn, expr)
    (lo, hi, tot)
end

const COUNTED_OPS = Set{Symbol}([
    :+, :-, :*, :div, :%, :&, :|, :xor, :⊻,
    :<<, :>>, :>>>,
    :or_int, :shl_int, :lshr_int, :zext_int, :trunc_int, :bitcast, :ult_int,
])

const COMPOUND_ASSIGN_OPS = Dict{Symbol, Symbol}(
    :+= => :+, :-= => :-, :*= => :*,
    :<<= => :<<, :>>= => :>>, :>>>= => :>>>,
    :&= => :&, :|= => :|, :⊻= => :⊻,
)

# Operation counter: (min, max).
function count_ops(expr)
    walk_expr(expr) do e
        n = 0
        if e.head == :call && length(e.args) >= 1
            op = first(e.args)
            if op isa Symbol && op in COUNTED_OPS
                n += 1
            end
        end
        implicit_op = get(COMPOUND_ASSIGN_OPS, e.head, nothing)
        if !isnothing(implicit_op) && implicit_op in COUNTED_OPS
            n += 1
        end
        n
    end
end

# Macroexpand a @defid expression, clean, extract parsebytes, and return
# complexity counts. Branches and ops are UnitRanges (min:max), plus total
# unique branch points in the AST.
function parsebytes_complexity(defid_expr::Expr)
    expanded = macroexpand(@__MODULE__, defid_expr)
    cleaned = exprclean!(expanded)
    body = extract_parsebytes(cleaned)
    isnothing(body) && return nothing
    blo, bhi, btot = count_branches(body)
    olo, ohi = count_ops(body)
    (; branches=blo:bhi, branch_total=btot, ops=olo:ohi)
end

function check_roundtrips(T, inputs)
    for input in inputs
        id = parse(T, input)
        @test parse(T, shortcode(id)) == id
    end
end

"""
    @test_neverthrow f(arg1, ::Type, ...)

Test that the LLVM IR for the given method signature contains no `throw` calls
(bounds errors, type errors, etc). Arguments can be `::Type` annotations to
specify types directly, or value expressions (resolved via `ttypeof` at expansion time).

# Example

    @test_neverthrow parsebytes(MyId, ::Vector{UInt8})
"""
macro test_neverthrow(expr)
    Meta.isexpr(expr, :call) || error("@test_neverthrow expects a call expression, got: $expr")
    func = expr.args[1]
    argtypes = map(expr.args[2:end]) do arg
        if Meta.isexpr(arg, :(::), 1)
            esc(arg.args[1])
        else
            :(ttypeof($(esc(arg))))
        end
    end
    typetup = Expr(:curly, :Tuple, argtypes...)
    quote
        let ir = sprint(code_llvm, $(esc(func)), $typetup; context=:debuginfo => :none)
            throws = filter(contains("ijl_throw"), split(ir, '\n'))
            @test isempty(throws)
        end
    end
end
ttypeof(::Type{T}) where {T} = Type{T}
ttypeof(x) = typeof(x)

# @testset "@defid" begin
    @testset "digits" begin
        @testset "SimpleNum" begin
            iddef = :(@defid SimpleNum ("SN", :id(digits(max=9999, pad=4))))
            @test parsebytes_complexity(iddef) == (branches=5:9, branch_total=9, ops=24:49)
            eval(iddef)
            # Parsing
            @test parse(SimpleNum, "SN42") isa SimpleNum
            @test parse(SimpleNum, "SN42").id == 42
            @test parse(SimpleNum, "SN0042").id == 42
            # Properties
            @test propertynames(parse(SimpleNum, "SN1")) == (:id,)
            @test parse(SimpleNum, "SN42").id isa Integer
            @test_throws Exception parse(SimpleNum, "SN1").nonexistent
            # Shortcode
            @test shortcode(parse(SimpleNum, "SN42")) == "SN0042"
            @test shortcode(parse(SimpleNum, "SN0")) == "SN0000"
            @test shortcode(parse(SimpleNum, "SN9999")) == "SN9999"
            # Equality
            @test parse(SimpleNum, "SN42") == parse(SimpleNum, "SN0042")
            @test hash(parse(SimpleNum, "SN42")) == hash(parse(SimpleNum, "SN0042"))
            @test parse(SimpleNum, "SN1") != parse(SimpleNum, "SN2")
            # Comparison
            a, b, c = parse.(SimpleNum, ("SN1", "SN2", "SN9999"))
            @test a < b < c
            @test sort([c, a, b]) == [a, b, c]
            # Errors
            @test tryparse(SimpleNum, "") === nothing
            @test tryparse(SimpleNum, "WRONG42") === nothing
            @test tryparse(SimpleNum, "SN") === nothing
            @test tryparse(SimpleNum, "SN99999") === nothing
            @test tryparse(SimpleNum, "SN42EXTRA") === nothing
            @test_throws MalformedIdentifier parse(SimpleNum, "")
            @test_throws MalformedIdentifier parse(SimpleNum, "WRONG42")
            @test_throws MalformedIdentifier parse(SimpleNum, "SN42EXTRA")
            # Edge cases
            @test parse(SimpleNum, "SN0").id == 0
            @test shortcode(parse(SimpleNum, "SN0")) == "SN0000"
            @test parse(SimpleNum, "SN9999").id == 9999
            @test tryparse(SimpleNum, "SN10000") === nothing
            # Round-trips
            check_roundtrips(SimpleNum, ("SN0", "SN1", "SN9999"))
            @test_neverthrow parsebytes(SimpleNum, ::Vector{UInt8})
        end

        @testset "BareDigits" begin
            iddef = :(@defid BareDigits :id(digits(5)))
            @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=27:27)
            eval(iddef)
            @test sizeof(BareDigits) >= 1
            # Parsing
            @test parse(BareDigits, "12345") isa BareDigits
            @test parse(BareDigits, "12345").id == 12345
            # Single-character digit strings
            for d in 0:9
                id = parse(BareDigits, "0000$d")
                @test id.id == d
            end
            # Round-trips
            check_roundtrips(BareDigits, ("00001", "99999"))
            @test_neverthrow parsebytes(BareDigits, ::Vector{UInt8})
        end

        @testset "VarDigits" begin
            iddef = :(@defid VarDigits :id(digits(1:5)))
            @test parsebytes_complexity(iddef) == (branches=5:8, branch_total=8, ops=25:55)
            eval(iddef)
            @test sizeof(VarDigits) >= 1
            # Variable width: accepts 1 to 5 digits
            @test parse(VarDigits, "1").id == 1
            @test parse(VarDigits, "42").id == 42
            @test parse(VarDigits, "12345").id == 12345
            # Rejects 0 or >5 digits
            @test tryparse(VarDigits, "") === nothing
            @test tryparse(VarDigits, "123456") === nothing
            # Shortcode uses minimal width (no zero-padding)
            @test shortcode(parse(VarDigits, "1")) == "1"
            @test shortcode(parse(VarDigits, "00042")) == "42"
            # Round-trips
            check_roundtrips(VarDigits, ("1", "42", "99999"))
            @test_neverthrow parsebytes(VarDigits, ::Vector{UInt8})
        end

        @testset "VarHexDigits" begin
            iddef = :(@defid VarHexDigits ("0x", :id(digits(1:4, base=16))))
            @test parsebytes_complexity(iddef) == (branches=5:9, branch_total=9, ops=29:75)
            eval(iddef)
            # Variable width: accepts 1 to 4 hex digits
            @test parse(VarHexDigits, "0xf").id == 0xf
            @test parse(VarHexDigits, "0xff").id == 0xff
            @test parse(VarHexDigits, "0xffff").id == 0xffff
            # Rejects empty or >4 hex digits
            @test tryparse(VarHexDigits, "0x") === nothing
            @test tryparse(VarHexDigits, "0xfffff") === nothing
            # Shortcode uses minimal width
            @test shortcode(parse(VarHexDigits, "0xff")) == "0xff"
            @test shortcode(parse(VarHexDigits, "0x00ff")) == "0xff"
            # Round-trips
            check_roundtrips(VarHexDigits, ("0xf", "0xff", "0xffff"))
            @test_neverthrow parsebytes(VarHexDigits, ::Vector{UInt8})
        end

        @testset "ZFilled" begin
            iddef = :(@defid ZFilled ("ZF-", :id(digits(4:4))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=20:20)
            eval(iddef)
            # Parsing
            @test parse(ZFilled, "ZF-0042") isa ZFilled
            @test parse(ZFilled, "ZF-0042").id == 42
            # Must be exactly 4 digits
            @test tryparse(ZFilled, "ZF-42") === nothing
            # Shortcode
            @test shortcode(parse(ZFilled, "ZF-0001")) == "ZF-0001"
            @test shortcode(parse(ZFilled, "ZF-0000")) == "ZF-0000"
            # Errors
            @test tryparse(ZFilled, "ZF-12") === nothing
            # Round-trips
            check_roundtrips(ZFilled, ("ZF-0000", "ZF-0042", "ZF-9999"))
            @test_neverthrow parsebytes(ZFilled, ::Vector{UInt8})
        end

        @testset "HexId" begin
            iddef = :(@defid HexId ("0x", :id(digits(4, base=16))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=32:32)
            eval(iddef)
            # Parsing
            @test parse(HexId, "0x00ff") isa HexId
            @test parse(HexId, "0x00ff").id == 0xff
            # Must be exactly 4 hex digits
            @test tryparse(HexId, "0xff") === nothing
            # Shortcode
            sc = shortcode(parse(HexId, "0x00ff"))
            @test occursin("00ff", sc)
            @test startswith(sc, "0x")
            # Errors
            @test tryparse(HexId, "0xGGGG") === nothing
            # Round-trips
            check_roundtrips(HexId, ("0x0000", "0x00ff", "0xffff"))
            @test_neverthrow parsebytes(HexId, ::Vector{UInt8})
        end

        @testset "TinyId" begin
            iddef = :(@defid TinyId :id(digits(max=1)))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=9:9)
            eval(iddef)
            @test sizeof(TinyId) == 1
            # Parsing
            z = parse(TinyId, "0")
            o = parse(TinyId, "1")
            @test z.id == 0
            @test o.id == 1
            @test z != o
            # Padding bits don't affect equality
            a = parse(TinyId, "1")
            b = parse(TinyId, "1")
            @test a == b
            @test hash(a) == hash(b)
            # Round-trips
            check_roundtrips(TinyId, ("0", "1"))
            @test_neverthrow parsebytes(TinyId, ::Vector{UInt8})
        end

        @testset "Ranged" begin
            iddef = :(@defid Ranged :id(digits(max=255, min=100)))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=24:24)
            eval(iddef)
            # Parsing
            @test parse(Ranged, "100").id == 100
            @test parse(Ranged, "255").id == 255
            # Below min / above max
            @test tryparse(Ranged, "99") === nothing
            @test tryparse(Ranged, "256") === nothing
            # Round-trips
            check_roundtrips(Ranged, ("100", "200", "255"))
            @test_neverthrow parsebytes(Ranged, ::Vector{UInt8})
        end

        @testset "VarWidth range checks" begin
            # Regression: variable-width SWAR digits truncated to the target
            # type before the range check, so overflow values silently wrapped.
            # (a) max only — 255 fills UInt8, must reject 256
            iddef = :(@defid RangeMax ("M", :id(digits(max=255))))
            @test parsebytes_complexity(iddef) == (branches=6:8, branch_total=8, ops=23:43)
            eval(iddef)
            @test parse(RangeMax, "M255").id == 255
            @test parse(RangeMax, "M0").id == 0
            @test tryparse(RangeMax, "M256") === nothing
            @test tryparse(RangeMax, "M999") === nothing
            check_roundtrips(RangeMax, ("M0", "M128", "M255"))
            @test_neverthrow parsebytes(RangeMax, ::Vector{UInt8})
            # (b) min only
            iddef = :(@defid RangeMin ("M", :id(digits(max=999, min=100))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=22:22)
            eval(iddef)
            @test parse(RangeMin, "M100").id == 100
            @test parse(RangeMin, "M999").id == 999
            @test tryparse(RangeMin, "M99") === nothing
            @test tryparse(RangeMin, "M0") === nothing
            check_roundtrips(RangeMin, ("M100", "M500", "M999"))
            @test_neverthrow parsebytes(RangeMin, ::Vector{UInt8})
            # (c) both min and max
            iddef = :(@defid RangeBoth ("M", :id(digits(max=200, min=50))))
            @test parsebytes_complexity(iddef) == (branches=7:9, branch_total=9, ops=23:43)
            eval(iddef)
            @test parse(RangeBoth, "M50").id == 50
            @test parse(RangeBoth, "M200").id == 200
            @test tryparse(RangeBoth, "M49") === nothing
            @test tryparse(RangeBoth, "M201") === nothing
            @test tryparse(RangeBoth, "M999") === nothing
            check_roundtrips(RangeBoth, ("M50", "M125", "M200"))
            @test_neverthrow parsebytes(RangeBoth, ::Vector{UInt8})
        end

        @testset "LargeId" begin
            iddef = :(@defid LargeId (:a(digits(max=2^16-1)), "-",
                                      :b(digits(max=2^16-1))))
            @test parsebytes_complexity(iddef) == (branches=12:19, branch_total=19, ops=52:112)
            eval(iddef)
            @test sizeof(LargeId) >= 4
            # All zeros
            id = parse(LargeId, "0-0")
            @test id.a == 0
            @test id.b == 0
            # All max values
            id = parse(LargeId, "65535-65535")
            @test id.a == 65535
            @test id.b == 65535
            # Round-trips
            check_roundtrips(LargeId, ("0-0", "1-65535", "65535-0", "65535-65535"))
            @test_neverthrow parsebytes(LargeId, ::Vector{UInt8})
        end

        @testset "VarWidth" begin
            iddef = :(@defid VarWidth ("VW", :id(digits(3:5))))
            @test parsebytes_complexity(iddef) == (branches=6:9, branch_total=9, ops=27:57)
            eval(iddef)
            # Accepts valid widths
            @test parse(VarWidth, "VW123").id == 123
            @test parse(VarWidth, "VW1234").id == 1234
            @test parse(VarWidth, "VW12345").id == 12345
            # Rejects too few / too many digits
            @test tryparse(VarWidth, "VW12") === nothing
            @test tryparse(VarWidth, "VW123456") === nothing
            # Round-trips
            check_roundtrips(VarWidth, ("VW123", "VW1234", "VW12345"))
            @test_neverthrow parsebytes(VarWidth, ::Vector{UInt8})
        end

        @testset "DirectValDigits" begin
            iddef = :(@defid DirectValDigits ("DV", :id(digits(max=255, min=100))))
            @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=22:22)
            eval(iddef)
            # Parsing
            @test parse(DirectValDigits, "DV100").id == 100
            @test parse(DirectValDigits, "DV255").id == 255
            # Errors
            @test tryparse(DirectValDigits, "DV99") === nothing
            @test tryparse(DirectValDigits, "DV256") === nothing
            # Round-trips
            check_roundtrips(DirectValDigits, ("DV100", "DV255"))
            @test_neverthrow parsebytes(DirectValDigits, ::Vector{UInt8})
        end

        @testset "OptDirectValDigits" begin
            iddef = :(@defid OptDirectValDigits (:base(digits(max=99)),
                       optional("-", :ext(digits(max=255, min=1)))))
            @test parsebytes_complexity(iddef) == (branches=6:16, branch_total=16, ops=20:80)
            eval(iddef)
            # Present
            @test parse(OptDirectValDigits, "42-1").base == 42
            @test parse(OptDirectValDigits, "42-1").ext == 1
            @test parse(OptDirectValDigits, "42-255").ext == 255
            # Absent
            @test parse(OptDirectValDigits, "42").base == 42
            @test parse(OptDirectValDigits, "42").ext === nothing
            # Absent is distinct from minimum value
            present_min = parse(OptDirectValDigits, "42-1")
            absent = parse(OptDirectValDigits, "42")
            @test present_min != absent
            @test present_min.ext == 1
            @test absent.ext === nothing
            # Round-trips
            check_roundtrips(OptDirectValDigits, ("42", "42-1", "42-255"))
            @test_neverthrow parsebytes(OptDirectValDigits, ::Vector{UInt8})
        end

        # ── SWAR code path coverage ──
        # These tests exercise the various SWAR paths in gen_digit_parse:
        # backward vs forward load, fixed vs variable width, power-of-2 vs odd
        # digit counts, optional fields, hex, and different register sizes.

        @testset "SWAR fixed backward 2:2 (UInt16)" begin
            iddef = :(@defid SwarBack2 ("PFX", :id(digits(2:2, base=10))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=17:17)
            eval(iddef)
            @test parse(SwarBack2, "PFX00").id == 0
            @test parse(SwarBack2, "PFX42").id == 42
            @test parse(SwarBack2, "PFX99").id == 99
            # Invalid: too short, too long, non-digit, empty
            @test tryparse(SwarBack2, "") === nothing
            @test tryparse(SwarBack2, "PFX") === nothing
            @test tryparse(SwarBack2, "PFX1") === nothing
            @test tryparse(SwarBack2, "PFX100") === nothing
            @test tryparse(SwarBack2, "PFXab") === nothing
            check_roundtrips(SwarBack2, ("PFX00", "PFX42", "PFX99"))
            @test_neverthrow parsebytes(SwarBack2, ::Vector{UInt8})
        end

        @testset "SWAR fixed backward 4:4 (UInt32)" begin
            iddef = :(@defid SwarBack4 ("X-", :id(digits(4:4, base=10))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=20:20)
            eval(iddef)
            @test parse(SwarBack4, "X-0000").id == 0
            @test parse(SwarBack4, "X-1234").id == 1234
            @test parse(SwarBack4, "X-9999").id == 9999
            @test tryparse(SwarBack4, "") === nothing
            @test tryparse(SwarBack4, "X-") === nothing
            @test tryparse(SwarBack4, "X-123") === nothing
            @test tryparse(SwarBack4, "X-12345") === nothing
            @test tryparse(SwarBack4, "X-abcd") === nothing
            @test tryparse(SwarBack4, "X-12x4") === nothing
            check_roundtrips(SwarBack4, ("X-0000", "X-1234", "X-9999"))
            @test_neverthrow parsebytes(SwarBack4, ::Vector{UInt8})
        end

        @testset "SWAR fixed backward 8:8 (UInt64)" begin
            iddef = :(@defid SwarBack8 ("ID:", :id(digits(8:8, base=10))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=23:23)
            eval(iddef)
            @test parse(SwarBack8, "ID:00000000").id == 0
            @test parse(SwarBack8, "ID:12345678").id == 12345678
            @test parse(SwarBack8, "ID:99999999").id == 99999999
            @test tryparse(SwarBack8, "") === nothing
            @test tryparse(SwarBack8, "ID:") === nothing
            @test tryparse(SwarBack8, "ID:1234567") === nothing
            @test tryparse(SwarBack8, "ID:123456789") === nothing
            @test tryparse(SwarBack8, "ID:abcdefgh") === nothing
            check_roundtrips(SwarBack8, ("ID:00000000", "ID:12345678", "ID:99999999"))
            @test_neverthrow parsebytes(SwarBack8, ::Vector{UInt8})
        end

        @testset "SWAR fixed backward 3:3 (UInt32, odd, padded)" begin
            iddef = :(@defid SwarBack3 ("ABCD", :id(digits(3:3, base=10))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=22:22)
            eval(iddef)
            @test parse(SwarBack3, "ABCD000").id == 0
            @test parse(SwarBack3, "ABCD042").id == 42
            @test parse(SwarBack3, "ABCD999").id == 999
            @test tryparse(SwarBack3, "ABCD") === nothing
            @test tryparse(SwarBack3, "ABCD42") === nothing
            @test tryparse(SwarBack3, "ABCD1234") === nothing
            @test tryparse(SwarBack3, "ABCDxyz") === nothing
            check_roundtrips(SwarBack3, ("ABCD000", "ABCD042", "ABCD999"))
            @test_neverthrow parsebytes(SwarBack3, ::Vector{UInt8})
        end

        @testset "SWAR fixed backward 5:5 (UInt64, odd, padded)" begin
            iddef = :(@defid SwarBack5 ("HDR---", :id(digits(5:5, base=10))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=25:25)
            eval(iddef)
            @test parse(SwarBack5, "HDR---00000").id == 0
            @test parse(SwarBack5, "HDR---12345").id == 12345
            @test parse(SwarBack5, "HDR---99999").id == 99999
            @test tryparse(SwarBack5, "HDR---") === nothing
            @test tryparse(SwarBack5, "HDR---1234") === nothing
            @test tryparse(SwarBack5, "HDR---123456") === nothing
            @test tryparse(SwarBack5, "HDR---hello") === nothing
            check_roundtrips(SwarBack5, ("HDR---00000", "HDR---12345", "HDR---99999"))
            @test_neverthrow parsebytes(SwarBack5, ::Vector{UInt8})
        end

        @testset "SWAR fixed backward 7:7 (UInt64, odd, padded)" begin
            iddef = :(@defid SwarBack7 ("V", :id(digits(7:7, base=10))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=25:25)
            eval(iddef)
            @test parse(SwarBack7, "V0000000").id == 0
            @test parse(SwarBack7, "V1234567").id == 1234567
            @test parse(SwarBack7, "V9999999").id == 9999999
            @test tryparse(SwarBack7, "V") === nothing
            @test tryparse(SwarBack7, "V123456") === nothing
            @test tryparse(SwarBack7, "V12345678") === nothing
            @test tryparse(SwarBack7, "Vabcdefg") === nothing
            check_roundtrips(SwarBack7, ("V0000000", "V1234567", "V9999999"))
            @test_neverthrow parsebytes(SwarBack7, ::Vector{UInt8})
        end

        @testset "SWAR fixed forward 3:3 (no preceding text)" begin
            iddef = :(@defid SwarFwd3 :id(digits(3:3, base=10)))
            @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=24:24)
            eval(iddef)
            @test parse(SwarFwd3, "000").id == 0
            @test parse(SwarFwd3, "042").id == 42
            @test parse(SwarFwd3, "999").id == 999
            @test tryparse(SwarFwd3, "") === nothing
            @test tryparse(SwarFwd3, "1") === nothing
            @test tryparse(SwarFwd3, "42") === nothing
            @test tryparse(SwarFwd3, "1234") === nothing
            @test tryparse(SwarFwd3, "abc") === nothing
            @test tryparse(SwarFwd3, "12c") === nothing
            check_roundtrips(SwarFwd3, ("000", "042", "999"))
            @test_neverthrow parsebytes(SwarFwd3, ::Vector{UInt8})
        end

        @testset "SWAR fixed forward 5:5 (no preceding text)" begin
            iddef = :(@defid SwarFwd5 :id(digits(5:5, base=10)))
            @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=27:27)
            eval(iddef)
            @test parse(SwarFwd5, "00000").id == 0
            @test parse(SwarFwd5, "12345").id == 12345
            @test parse(SwarFwd5, "99999").id == 99999
            @test tryparse(SwarFwd5, "") === nothing
            @test tryparse(SwarFwd5, "1234") === nothing
            @test tryparse(SwarFwd5, "123456") === nothing
            @test tryparse(SwarFwd5, "abcde") === nothing
            check_roundtrips(SwarFwd5, ("00000", "12345", "99999"))
            @test_neverthrow parsebytes(SwarFwd5, ::Vector{UInt8})
        end

        @testset "SWAR fixed hex 4:4 (UInt32, backward)" begin
            iddef = :(@defid SwarHex4 ("0x", :id(digits(4:4, base=16))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=32:32)
            eval(iddef)
            @test parse(SwarHex4, "0x0000").id == 0
            @test parse(SwarHex4, "0x00ff").id == 0xff
            @test parse(SwarHex4, "0xffff").id == 0xffff
            @test parse(SwarHex4, "0xABCD").id == 0xabcd
            @test tryparse(SwarHex4, "0x") === nothing
            @test tryparse(SwarHex4, "0xfff") === nothing
            @test tryparse(SwarHex4, "0xfffff") === nothing
            @test tryparse(SwarHex4, "0xGGGG") === nothing
            @test tryparse(SwarHex4, "0xfg12") === nothing
            check_roundtrips(SwarHex4, ("0x0000", "0x00ff", "0xabcd", "0xffff"))
            @test_neverthrow parsebytes(SwarHex4, ::Vector{UInt8})
        end

        @testset "SWAR fixed hex 8:8 (UInt64, backward)" begin
            iddef = :(@defid SwarHex8 ("H:", :id(digits(8:8, base=16))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=35:35)
            eval(iddef)
            @test parse(SwarHex8, "H:00000000").id == 0
            @test parse(SwarHex8, "H:deadbeef").id == 0xdeadbeef
            @test parse(SwarHex8, "H:DEADBEEF").id == 0xdeadbeef
            @test parse(SwarHex8, "H:ffffffff").id == 0xffffffff
            @test tryparse(SwarHex8, "H:") === nothing
            @test tryparse(SwarHex8, "H:fffffff") === nothing
            @test tryparse(SwarHex8, "H:fffffffff") === nothing
            @test tryparse(SwarHex8, "H:ghijklmn") === nothing
            check_roundtrips(SwarHex8, ("H:00000000", "H:deadbeef", "H:ffffffff"))
            @test_neverthrow parsebytes(SwarHex8, ::Vector{UInt8})
        end

        @testset "SWAR fixed hex 2:2 forward (no preceding text)" begin
            iddef = :(@defid SwarHexFwd2 :id(digits(2:2, base=16)))
            @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=27:27)
            eval(iddef)
            @test parse(SwarHexFwd2, "00").id == 0
            @test parse(SwarHexFwd2, "ff").id == 0xff
            @test parse(SwarHexFwd2, "FF").id == 0xff
            @test tryparse(SwarHexFwd2, "") === nothing
            @test tryparse(SwarHexFwd2, "f") === nothing
            @test tryparse(SwarHexFwd2, "fff") === nothing
            @test tryparse(SwarHexFwd2, "GG") === nothing
            @test tryparse(SwarHexFwd2, "g1") === nothing
            check_roundtrips(SwarHexFwd2, ("00", "0f", "ff"))
            @test_neverthrow parsebytes(SwarHexFwd2, ::Vector{UInt8})
        end

        @testset "SWAR variable with prefix (backward-safe region)" begin
            iddef = :(@defid SwarVarPfx ("DATA-", :id(digits(2:4, base=10))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=35:36)
            eval(iddef)
            @test parse(SwarVarPfx, "DATA-12").id == 12
            @test parse(SwarVarPfx, "DATA-123").id == 123
            @test parse(SwarVarPfx, "DATA-1234").id == 1234
            @test tryparse(SwarVarPfx, "") === nothing
            @test tryparse(SwarVarPfx, "DATA-") === nothing
            @test tryparse(SwarVarPfx, "DATA-1") === nothing
            @test tryparse(SwarVarPfx, "DATA-12345") === nothing
            @test tryparse(SwarVarPfx, "DATA-ab") === nothing
            check_roundtrips(SwarVarPfx, ("DATA-12", "DATA-123", "DATA-9999"))
            @test_neverthrow parsebytes(SwarVarPfx, ::Vector{UInt8})
        end

        @testset "SWAR variable backward (UInt64, padding>0)" begin
            iddef = :(@defid SwarVarBack ("ABCDEFGH-", :id(digits(2:5, base=10))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=39:40)
            eval(iddef)
            # sT=UInt64, maxdigits=5, padding=3, parsed_bytes_min=9 >= 7
            @test parse(SwarVarBack, "ABCDEFGH-12").id == 12
            @test parse(SwarVarBack, "ABCDEFGH-123").id == 123
            @test parse(SwarVarBack, "ABCDEFGH-1234").id == 1234
            @test parse(SwarVarBack, "ABCDEFGH-99999").id == 99999
            @test tryparse(SwarVarBack, "ABCDEFGH-") === nothing
            @test tryparse(SwarVarBack, "ABCDEFGH-1") === nothing
            @test tryparse(SwarVarBack, "ABCDEFGH-123456") === nothing
            @test tryparse(SwarVarBack, "ABCDEFGH-ab") === nothing
            check_roundtrips(SwarVarBack, ("ABCDEFGH-12", "ABCDEFGH-999", "ABCDEFGH-99999"))
            @test_neverthrow parsebytes(SwarVarBack, ::Vector{UInt8})
        end

        @testset "SWAR variable backward hex" begin
            iddef = :(@defid SwarVarBackHex ("ABCDEFGH-", :id(digits(2:6, base=16))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=47:48)
            eval(iddef)
            # sT=UInt64, maxdigits=6, padding=2, parsed_bytes_min=9 >= 7
            @test parse(SwarVarBackHex, "ABCDEFGH-ff").id == 0xff
            @test parse(SwarVarBackHex, "ABCDEFGH-abc").id == 0xabc
            @test parse(SwarVarBackHex, "ABCDEFGH-DEAD").id == 0xdead
            @test parse(SwarVarBackHex, "ABCDEFGH-fffff").id == 0xfffff
            @test parse(SwarVarBackHex, "ABCDEFGH-ffffff").id == 0xffffff
            @test tryparse(SwarVarBackHex, "ABCDEFGH-") === nothing
            @test tryparse(SwarVarBackHex, "ABCDEFGH-f") === nothing
            @test tryparse(SwarVarBackHex, "ABCDEFGH-GG") === nothing
            @test tryparse(SwarVarBackHex, "ABCDEFGH-fffffff") === nothing
            check_roundtrips(SwarVarBackHex, ("ABCDEFGH-ff", "ABCDEFGH-abc", "ABCDEFGH-ffffff"))
            @test_neverthrow parsebytes(SwarVarBackHex, ::Vector{UInt8})
        end

        @testset "SWAR variable backward optional" begin
            iddef = :(@defid SwarVarBackOpt ("ABCDEFGH-", :a(digits(4:4)),
                       optional(".", :b(digits(1:4)))))
            @test parsebytes_complexity(iddef) == (branches=6:8, branch_total=8, ops=22:61)
            eval(iddef)
            # :b has sT=UInt32, parsed_bytes_min>=13 (prefix+4digits+".") >= 3
            @test parse(SwarVarBackOpt, "ABCDEFGH-1234.5").a == 1234
            @test parse(SwarVarBackOpt, "ABCDEFGH-1234.5").b == 5
            @test parse(SwarVarBackOpt, "ABCDEFGH-1234.5678").b == 5678
            @test parse(SwarVarBackOpt, "ABCDEFGH-1234").a == 1234
            @test parse(SwarVarBackOpt, "ABCDEFGH-1234").b === nothing
            @test parse(SwarVarBackOpt, "ABCDEFGH-1234.5") != parse(SwarVarBackOpt, "ABCDEFGH-1234")
            check_roundtrips(SwarVarBackOpt,
                ("ABCDEFGH-1234", "ABCDEFGH-0001.1", "ABCDEFGH-9999.9999"))
            @test_neverthrow parsebytes(SwarVarBackOpt, ::Vector{UInt8})
        end

        @testset "SWAR variable backward full-width" begin
            iddef = :(@defid SwarVarBackFull ("ABCDEFGH-", :id(digits(1:8, base=10))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=38:39)
            eval(iddef)
            # sT=UInt64, maxdigits=8, padding=0, parsed_bytes_min=9 >= 7
            @test parse(SwarVarBackFull, "ABCDEFGH-1").id == 1
            @test parse(SwarVarBackFull, "ABCDEFGH-12").id == 12
            @test parse(SwarVarBackFull, "ABCDEFGH-12345678").id == 12345678
            @test parse(SwarVarBackFull, "ABCDEFGH-99999999").id == 99999999
            @test tryparse(SwarVarBackFull, "ABCDEFGH-") === nothing
            @test tryparse(SwarVarBackFull, "ABCDEFGH-123456789") === nothing
            @test tryparse(SwarVarBackFull, "ABCDEFGH-ab") === nothing
            check_roundtrips(SwarVarBackFull,
                ("ABCDEFGH-1", "ABCDEFGH-42", "ABCDEFGH-12345678", "ABCDEFGH-99999999"))
            @test_neverthrow parsebytes(SwarVarBackFull, ::Vector{UInt8})
        end

        @testset "SWAR variable no prefix (forward only)" begin
            iddef = :(@defid SwarVarBare :id(digits(1:5, base=10)))
            @test parsebytes_complexity(iddef) == (branches=5:8, branch_total=8, ops=25:55)
            eval(iddef)
            @test parse(SwarVarBare, "1").id == 1
            @test parse(SwarVarBare, "12").id == 12
            @test parse(SwarVarBare, "12345").id == 12345
            @test parse(SwarVarBare, "99999").id == 99999
            @test tryparse(SwarVarBare, "") === nothing
            @test tryparse(SwarVarBare, "123456") === nothing
            @test tryparse(SwarVarBare, "abcde") === nothing
            @test tryparse(SwarVarBare, "12x") === nothing
            check_roundtrips(SwarVarBare, ("1", "12", "123", "1234", "99999"))
            @test_neverthrow parsebytes(SwarVarBare, ::Vector{UInt8})
        end

        @testset "SWAR variable hex (forward)" begin
            iddef = :(@defid SwarVarHex ("0x", :id(digits(1:4, base=16))))
            @test parsebytes_complexity(iddef) == (branches=5:9, branch_total=9, ops=29:75)
            eval(iddef)
            @test parse(SwarVarHex, "0xf").id == 0xf
            @test parse(SwarVarHex, "0xff").id == 0xff
            @test parse(SwarVarHex, "0xabc").id == 0xabc
            @test parse(SwarVarHex, "0xffff").id == 0xffff
            @test parse(SwarVarHex, "0xABCD").id == 0xabcd
            @test tryparse(SwarVarHex, "0x") === nothing
            @test tryparse(SwarVarHex, "0xfffff") === nothing
            @test tryparse(SwarVarHex, "0xGG") === nothing
            check_roundtrips(SwarVarHex, ("0xf", "0xff", "0xabc", "0xffff"))
            @test_neverthrow parsebytes(SwarVarHex, ::Vector{UInt8})
        end

        # ── Forward-overread paths (trailing content provides safety) ──
        # These test the __ifelse_length_exceeds optimisation that replaces
        # sub-load decomposition with a single full-width load + shift when
        # trailing pattern nodes guarantee enough bytes.

        @testset "SWAR fixed forward-overread 3:3 (UInt32, trailing literal)" begin
            # sT=UInt32, maxdigits=3 < sizeof(UInt32)=4, trailing "end" provides byte 4
            iddef = :(@defid SwarFwdOr3 (:id(digits(3:3)), "end"))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=22:24)
            eval(iddef)
            @test parse(SwarFwdOr3, "000end").id == 0
            @test parse(SwarFwdOr3, "042end").id == 42
            @test parse(SwarFwdOr3, "999end").id == 999
            @test tryparse(SwarFwdOr3, "end") === nothing
            @test tryparse(SwarFwdOr3, "42end") === nothing
            @test tryparse(SwarFwdOr3, "1234end") === nothing
            @test tryparse(SwarFwdOr3, "abcend") === nothing
            check_roundtrips(SwarFwdOr3, ("000end", "042end", "999end"))
            @test_neverthrow parsebytes(SwarFwdOr3, ::Vector{UInt8})
        end

        @testset "SWAR fixed forward-overread 5:5 (UInt64, trailing literal)" begin
            # sT=UInt64, maxdigits=5, trailing "test" (4 bytes) → 5+4=9 ≥ 8
            iddef = :(@defid SwarFwdOr5 (:id(digits(5:5)), "test"))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=25:25)
            eval(iddef)
            @test parse(SwarFwdOr5, "00000test").id == 0
            @test parse(SwarFwdOr5, "12345test").id == 12345
            @test parse(SwarFwdOr5, "99999test").id == 99999
            @test tryparse(SwarFwdOr5, "test") === nothing
            @test tryparse(SwarFwdOr5, "1234test") === nothing
            @test tryparse(SwarFwdOr5, "123456test") === nothing
            @test tryparse(SwarFwdOr5, "hellotest") === nothing
            check_roundtrips(SwarFwdOr5, ("00000test", "12345test", "99999test"))
            @test_neverthrow parsebytes(SwarFwdOr5, ::Vector{UInt8})
        end

        @testset "SWAR fixed forward-overread 7:7 (UInt64, trailing byte)" begin
            # sT=UInt64, maxdigits=7, trailing "X" (1 byte) → 7+1=8 ≥ 8
            iddef = :(@defid SwarFwdOr7 (:id(digits(7:7)), "X"))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=25:25)
            eval(iddef)
            @test parse(SwarFwdOr7, "0000000X").id == 0
            @test parse(SwarFwdOr7, "1234567X").id == 1234567
            @test parse(SwarFwdOr7, "9999999X").id == 9999999
            @test tryparse(SwarFwdOr7, "X") === nothing
            @test tryparse(SwarFwdOr7, "123456X") === nothing
            @test tryparse(SwarFwdOr7, "12345678X") === nothing
            @test tryparse(SwarFwdOr7, "abcdefgX") === nothing
            check_roundtrips(SwarFwdOr7, ("0000000X", "1234567X", "9999999X"))
            @test_neverthrow parsebytes(SwarFwdOr7, ::Vector{UInt8})
        end

        @testset "SWAR variable forward-overread 1:4 (UInt32, trailing literal)" begin
            # sT=UInt32, maxdigits=4, trailing "test" (4 bytes) → 1+4=5 ≥ 4
            iddef = :(@defid SwarVarFwdOr4 (:id(digits(1:4)), "test"))
            @test parsebytes_complexity(iddef) == (branches=3:4, branch_total=4, ops=29:30)
            eval(iddef)
            @test parse(SwarVarFwdOr4, "1test").id == 1
            @test parse(SwarVarFwdOr4, "42test").id == 42
            @test parse(SwarVarFwdOr4, "999test").id == 999
            @test parse(SwarVarFwdOr4, "9999test").id == 9999
            @test tryparse(SwarVarFwdOr4, "test") === nothing
            @test tryparse(SwarVarFwdOr4, "12345test") === nothing
            @test tryparse(SwarVarFwdOr4, "abtest") === nothing
            check_roundtrips(SwarVarFwdOr4, ("1test", "42test", "999test", "9999test"))
            @test_neverthrow parsebytes(SwarVarFwdOr4, ::Vector{UInt8})
        end

        @testset "SWAR variable forward-overread 2:3 (UInt32, trailing literal)" begin
            # sT=UInt32, maxdigits=3, trailing "XYZ" (3 bytes) → 2+3=5 ≥ 4
            iddef = :(@defid SwarVarFwdOr3 (:id(digits(2:3)), "XYZ"))
            @test parsebytes_complexity(iddef) == (branches=3:5, branch_total=5, ops=30:33)
            eval(iddef)
            @test parse(SwarVarFwdOr3, "12XYZ").id == 12
            @test parse(SwarVarFwdOr3, "999XYZ").id == 999
            @test tryparse(SwarVarFwdOr3, "XYZ") === nothing
            @test tryparse(SwarVarFwdOr3, "1XYZ") === nothing
            @test tryparse(SwarVarFwdOr3, "1234XYZ") === nothing
            check_roundtrips(SwarVarFwdOr3, ("12XYZ", "99XYZ", "999XYZ"))
            @test_neverthrow parsebytes(SwarVarFwdOr3, ::Vector{UInt8})
        end

        @testset "SWAR variable forward-overread hex (UInt32, trailing literal)" begin
            # Hex digits 1:4 with non-hex trailing content
            iddef = :(@defid SwarVarFwdOrHex (:id(digits(1:4, base=16)), "XYZ"))
            @test parsebytes_complexity(iddef) == (branches=3:5, branch_total=5, ops=37:40)
            eval(iddef)
            @test parse(SwarVarFwdOrHex, "fXYZ").id == 0xf
            @test parse(SwarVarFwdOrHex, "ffXYZ").id == 0xff
            @test parse(SwarVarFwdOrHex, "abcXYZ").id == 0xabc
            @test parse(SwarVarFwdOrHex, "ffffXYZ").id == 0xffff
            @test parse(SwarVarFwdOrHex, "ABCDXYZ").id == 0xabcd
            @test tryparse(SwarVarFwdOrHex, "XYZ") === nothing
            @test tryparse(SwarVarFwdOrHex, "fffffXYZ") === nothing
            check_roundtrips(SwarVarFwdOrHex, ("fXYZ", "ffXYZ", "abcXYZ", "ffffXYZ"))
            @test_neverthrow parsebytes(SwarVarFwdOrHex, ::Vector{UInt8})
        end

        @testset "SWAR variable forward-overread optional (trailing literal)" begin
            # Optional variable digits before a mandatory trailing literal
            iddef = :(@defid SwarVarFwdOrOpt (:a(digits(max=99)),
                       optional(".", :b(digits(1:4))), "END"))
            @test parsebytes_complexity(iddef) == (branches=5:15, branch_total=15, ops=26:81)
            eval(iddef)
            @test parse(SwarVarFwdOrOpt, "42.1END").a == 42
            @test parse(SwarVarFwdOrOpt, "42.1END").b == 1
            @test parse(SwarVarFwdOrOpt, "42.9999END").b == 9999
            @test parse(SwarVarFwdOrOpt, "42END").a == 42
            @test parse(SwarVarFwdOrOpt, "42END").b === nothing
            @test parse(SwarVarFwdOrOpt, "42.1END") != parse(SwarVarFwdOrOpt, "42END")
            check_roundtrips(SwarVarFwdOrOpt, ("42END", "42.1END", "42.9999END"))
            @test_neverthrow parsebytes(SwarVarFwdOrOpt, ::Vector{UInt8})
        end

        @testset "SWAR fixed optional (backward)" begin
            iddef = :(@defid SwarOptBack ("P", :a(digits(max=99)),
                       optional("-", :b(digits(4:4, base=10)))))
            @test parsebytes_complexity(iddef) == (branches=5:7, branch_total=7, ops=34:57)
            eval(iddef)
            # Present
            @test parse(SwarOptBack, "P42-1234").a == 42
            @test parse(SwarOptBack, "P42-1234").b == 1234
            @test parse(SwarOptBack, "P42-0000").b == 0
            # Absent
            @test parse(SwarOptBack, "P42").a == 42
            @test parse(SwarOptBack, "P42").b === nothing
            # Distinct
            @test parse(SwarOptBack, "P42-0000") != parse(SwarOptBack, "P42")
            # Invalid
            @test tryparse(SwarOptBack, "") === nothing
            @test tryparse(SwarOptBack, "P42-") === nothing
            @test tryparse(SwarOptBack, "P42-123") === nothing
            @test tryparse(SwarOptBack, "P42-12345") === nothing
            @test tryparse(SwarOptBack, "P42-abcd") === nothing
            check_roundtrips(SwarOptBack, ("P42", "P42-0000", "P42-1234", "P42-9999"))
            @test_neverthrow parsebytes(SwarOptBack, ::Vector{UInt8})
        end

        @testset "SWAR fixed optional (forward, no prefix)" begin
            iddef = :(@defid SwarOptFwd (:a(digits(max=9)),
                       optional("-", :b(digits(3:3, base=10)))))
            @test parsebytes_complexity(iddef) == (branches=4:6, branch_total=6, ops=11:36)
            eval(iddef)
            # Present
            @test parse(SwarOptFwd, "5-042").a == 5
            @test parse(SwarOptFwd, "5-042").b == 42
            @test parse(SwarOptFwd, "5-000").b == 0
            # Absent
            @test parse(SwarOptFwd, "5").a == 5
            @test parse(SwarOptFwd, "5").b === nothing
            @test parse(SwarOptFwd, "5-000") != parse(SwarOptFwd, "5")
            # Invalid
            @test tryparse(SwarOptFwd, "") === nothing
            @test tryparse(SwarOptFwd, "5-") === nothing
            @test tryparse(SwarOptFwd, "5-12") === nothing
            @test tryparse(SwarOptFwd, "5-1234") === nothing
            @test tryparse(SwarOptFwd, "5-abc") === nothing
            check_roundtrips(SwarOptFwd, ("5", "5-000", "5-042", "5-999"))
            @test_neverthrow parsebytes(SwarOptFwd, ::Vector{UInt8})
        end

        @testset "SWAR variable optional (forward)" begin
            iddef = :(@defid SwarOptVar ("T-", :a(digits(max=99)),
                       optional(".", :b(digits(2:4, base=10)))))
            @test parsebytes_complexity(iddef) == (branches=5:7, branch_total=7, ops=34:72)
            eval(iddef)
            # Present
            @test parse(SwarOptVar, "T-42.12").a == 42
            @test parse(SwarOptVar, "T-42.12").b == 12
            @test parse(SwarOptVar, "T-42.1234").b == 1234
            # Absent
            @test parse(SwarOptVar, "T-42").a == 42
            @test parse(SwarOptVar, "T-42").b === nothing
            @test parse(SwarOptVar, "T-42.12") != parse(SwarOptVar, "T-42")
            # Invalid
            @test tryparse(SwarOptVar, "") === nothing
            @test tryparse(SwarOptVar, "T-42.") === nothing
            @test tryparse(SwarOptVar, "T-42.1") === nothing
            @test tryparse(SwarOptVar, "T-42.12345") === nothing
            @test tryparse(SwarOptVar, "T-42.ab") === nothing
            check_roundtrips(SwarOptVar, ("T-42", "T-42.12", "T-42.1234"))
            @test_neverthrow parsebytes(SwarOptVar, ::Vector{UInt8})
        end

        @testset "SWAR multi-field backward chain" begin
            iddef = :(@defid SwarChain ("AB-", :x(digits(4:4, base=10)),
                       "-", :y(digits(4:4, base=10))))
            @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=38:38)
            eval(iddef)
            @test parse(SwarChain, "AB-1234-5678").x == 1234
            @test parse(SwarChain, "AB-1234-5678").y == 5678
            @test parse(SwarChain, "AB-0000-0000").x == 0
            @test parse(SwarChain, "AB-0000-0000").y == 0
            @test tryparse(SwarChain, "") === nothing
            @test tryparse(SwarChain, "AB-1234") === nothing
            @test tryparse(SwarChain, "AB-1234-") === nothing
            @test tryparse(SwarChain, "AB-1234-567") === nothing
            @test tryparse(SwarChain, "AB-abcd-efgh") === nothing
            check_roundtrips(SwarChain, ("AB-0000-0000", "AB-1234-5678", "AB-9999-9999"))
            @test_neverthrow parsebytes(SwarChain, ::Vector{UInt8})
        end

        @testset "SWAR fixed backward base 8 (UInt32)" begin
            iddef = :(@defid SwarOct4 ("O", :id(digits(4:4, base=8))))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=20:20)
            eval(iddef)
            @test parse(SwarOct4, "O0000").id == 0
            @test parse(SwarOct4, "O0177").id == 0o0177
            @test parse(SwarOct4, "O7777").id == 0o7777
            @test tryparse(SwarOct4, "O") === nothing
            @test tryparse(SwarOct4, "O012") === nothing
            @test tryparse(SwarOct4, "O01234") === nothing
            @test tryparse(SwarOct4, "O8000") === nothing
            @test tryparse(SwarOct4, "O9abc") === nothing
            check_roundtrips(SwarOct4, ("O0000", "O0177", "O7777"))
            @test_neverthrow parsebytes(SwarOct4, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk 9:9 (8+1)" begin
            iddef = :(@defid Swar2C9 ("N", :id(digits(9:9))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=29:29)
            eval(iddef)
            @test parse(Swar2C9, "N000000000").id == 0
            @test parse(Swar2C9, "N000000042").id == 42
            @test parse(Swar2C9, "N123456789").id == 123456789
            @test parse(Swar2C9, "N999999999").id == 999999999
            @test tryparse(Swar2C9, "N") === nothing
            @test tryparse(Swar2C9, "N12345678") === nothing
            @test tryparse(Swar2C9, "N1234567890") === nothing
            @test tryparse(Swar2C9, "Nabcdefghi") === nothing
            check_roundtrips(Swar2C9, ("N000000000", "N123456789", "N999999999"))
            @test_neverthrow parsebytes(Swar2C9, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk 10:10 (8+2)" begin
            iddef = :(@defid Swar2C10 ("ID-", :id(digits(10:10))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=34:34)
            eval(iddef)
            @test parse(Swar2C10, "ID-0000000000").id == 0
            @test parse(Swar2C10, "ID-0000000042").id == 42
            @test parse(Swar2C10, "ID-1234567890").id == 1234567890
            @test parse(Swar2C10, "ID-9999999999").id == 9999999999
            @test tryparse(Swar2C10, "ID-") === nothing
            @test tryparse(Swar2C10, "ID-123456789") === nothing
            @test tryparse(Swar2C10, "ID-12345678901") === nothing
            @test tryparse(Swar2C10, "ID-abcdefghij") === nothing
            check_roundtrips(Swar2C10, ("ID-0000000000", "ID-1234567890", "ID-9999999999"))
            @test_neverthrow parsebytes(Swar2C10, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk 12:12 (8+4)" begin
            iddef = :(@defid Swar2C12 ("X", :id(digits(12:12))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=37:37)
            eval(iddef)
            @test parse(Swar2C12, "X000000000000").id == 0
            @test parse(Swar2C12, "X000000000042").id == 42
            @test parse(Swar2C12, "X123456789012").id == 123456789012
            @test parse(Swar2C12, "X999999999999").id == 999999999999
            @test tryparse(Swar2C12, "X") === nothing
            @test tryparse(Swar2C12, "X12345678901") === nothing
            @test tryparse(Swar2C12, "X1234567890123") === nothing
            @test tryparse(Swar2C12, "Xabcdefghijkl") === nothing
            check_roundtrips(Swar2C12, ("X000000000000", "X123456789012", "X999999999999"))
            @test_neverthrow parsebytes(Swar2C12, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk 13:13 (8+5)" begin
            iddef = :(@defid Swar2C13 :id(digits(13:13)))
            @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=39:39)
            eval(iddef)
            @test parse(Swar2C13, "0000000000000").id == 0
            @test parse(Swar2C13, "0000000000042").id == 42
            @test parse(Swar2C13, "1234567890123").id == 1234567890123
            @test parse(Swar2C13, "9999999999999").id == 9999999999999
            @test tryparse(Swar2C13, "") === nothing
            @test tryparse(Swar2C13, "123456789012") === nothing
            @test tryparse(Swar2C13, "12345678901234") === nothing
            @test tryparse(Swar2C13, "abcdefghijklm") === nothing
            check_roundtrips(Swar2C13, ("0000000000000", "1234567890123", "9999999999999"))
            @test_neverthrow parsebytes(Swar2C13, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk 16:16 (8+8)" begin
            iddef = :(@defid Swar2C16 ("G", :id(digits(16:16))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=40:40)
            eval(iddef)
            @test parse(Swar2C16, "G0000000000000000").id == 0
            @test parse(Swar2C16, "G0000000000000042").id == 42
            @test parse(Swar2C16, "G1234567890123456").id == 1234567890123456
            @test parse(Swar2C16, "G9999999999999999").id == 9999999999999999
            @test tryparse(Swar2C16, "G") === nothing
            @test tryparse(Swar2C16, "G123456789012345") === nothing
            @test tryparse(Swar2C16, "G12345678901234567") === nothing
            @test tryparse(Swar2C16, "Gabcdefghijklmnop") === nothing
            check_roundtrips(Swar2C16, ("G0000000000000000", "G1234567890123456", "G9999999999999999"))
            @test_neverthrow parsebytes(Swar2C16, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk hex 10:10 (8+2)" begin
            iddef = :(@defid Swar2CHex10 ("H", :id(digits(10:10, base=16))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=58:58)
            eval(iddef)
            @test parse(Swar2CHex10, "H0000000000").id == 0
            @test parse(Swar2CHex10, "H00000000ff").id == 0xff
            @test parse(Swar2CHex10, "H00000000FF").id == 0xff
            @test parse(Swar2CHex10, "H00abcdef01").id == 0xabcdef01
            @test parse(Swar2CHex10, "Hffffffffff").id == 0xffffffffff
            @test tryparse(Swar2CHex10, "H") === nothing
            @test tryparse(Swar2CHex10, "H123456789") === nothing
            @test tryparse(Swar2CHex10, "H12345678901") === nothing
            @test tryparse(Swar2CHex10, "Hgggggggggx") === nothing
            check_roundtrips(Swar2CHex10, ("H0000000000", "H00abcdef01", "Hffffffffff"))
            @test_neverthrow parsebytes(Swar2CHex10, ::Vector{UInt8})
        end

        @testset "SWAR two-chunk optional 10:10 (8+2)" begin
            iddef = :(@defid Swar2COpt ("V", :a(digits(2:2)),
                       optional(".", :b(digits(10:10)))))
            @test parsebytes_complexity(iddef) == (branches=5:8, branch_total=8, ops=19:56)
            eval(iddef)
            @test parse(Swar2COpt, "V42.0000000000").a == 42
            @test parse(Swar2COpt, "V42.0000000000").b == 0
            @test parse(Swar2COpt, "V42.1234567890").b == 1234567890
            @test parse(Swar2COpt, "V42").a == 42
            @test parse(Swar2COpt, "V42").b === nothing
            @test tryparse(Swar2COpt, "V42.123456789") === nothing
            @test tryparse(Swar2COpt, "V42.12345678901") === nothing
            check_roundtrips(Swar2COpt, ("V42", "V42.0000000000", "V42.1234567890"))
            @test_neverthrow parsebytes(Swar2COpt, ::Vector{UInt8})
        end
    end # digits

    @testset "literals" begin
        @testset "Compound" begin
            iddef = :(@defid Compound ("ID:", :major(digits(max=99)), ".",
                       :minor(digits(max=99))))
            @test parsebytes_complexity(iddef) == (branches=6:6, branch_total=6, ops=62:62)
            eval(iddef)
            # Parsing
            @test parse(Compound, "ID:3.14") isa Compound
            @test parse(Compound, "ID:3.14").major == 3
            @test parse(Compound, "ID:3.14").minor == 14
            # Properties
            @test propertynames(parse(Compound, "ID:1.2")) == (:major, :minor)
            # Shortcode
            @test shortcode(parse(Compound, "ID:3.14")) == "ID:3.14"
            # Comparison: sorting is consistent and deterministic
            ids = [parse(Compound, "ID:$i.$j") for i in 0:3 for j in 0:3]
            s1 = sort(ids)
            s2 = sort(ids)
            @test s1 == s2
            @test s1[1].major <= s1[end].major
            # Round-trips
            check_roundtrips(Compound, ("ID:0.0", "ID:1.2", "ID:99.99"))
            @test_neverthrow parsebytes(Compound, ::Vector{UInt8})
        end

        @testset "MultiFieldProp" begin
            iddef = :(@defid MultiFieldProp (:compound("v", digits(max=9), ".", digits(max=9))))
            @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=20:20)
            eval(iddef)
            id = parse(MultiFieldProp, "v3.7")
            @test id.compound == "v3.7"
            # Round-trips
            check_roundtrips(MultiFieldProp, ("v0.0", "v3.7", "v9.9"))
            @test_neverthrow parsebytes(MultiFieldProp, ::Vector{UInt8})
        end
        @testset "TrailingLit" begin
            # 3-byte trailing literal: widening candidate but can't use
            # the wide path (no subsequent content guarantees safe overread)
            iddef = :(@defid TrailingLit (:id(digits(1:3)), "end"))
            @test parsebytes_complexity(iddef) == (branches=3:5, branch_total=5, ops=30:33)
            eval(iddef)
            @test parse(TrailingLit, "1end") isa TrailingLit
            @test parse(TrailingLit, "42end").id == 42
            @test parse(TrailingLit, "999end").id == 999
            @test shortcode(parse(TrailingLit, "42end")) == "42end"
            @test tryparse(TrailingLit, "42") === nothing
            @test tryparse(TrailingLit, "42END") == parse(TrailingLit, "42end")
            @test tryparse(TrailingLit, "42enx") === nothing
            @test tryparse(TrailingLit, "42endX") === nothing
            @test tryparse(TrailingLit, "1234end") === nothing
            check_roundtrips(TrailingLit, ("1end", "42end", "999end"))
            @test_neverthrow parsebytes(TrailingLit, ::Vector{UInt8})
        end
    end # literals

    @testset "choice" begin
        @testset "PrefixChoice" begin
            iddef = :(@defid PrefixChoice (choice("alpha/", "beta/"), :id(digits(max=255))))
            @test parsebytes_complexity(iddef) == (branches=6:9, branch_total=9, ops=43:48)
            eval(iddef)
            # Parsing
            a = parse(PrefixChoice, "alpha/42")
            b = parse(PrefixChoice, "beta/42")
            @test a isa PrefixChoice
            @test b isa PrefixChoice
            # Same numeric id but different choice → different identifiers
            @test a != b
            @test a.id == b.id == 42
            # Case-insensitive choice matching
            lo = parse(PrefixChoice, "alpha/1")
            up = parse(PrefixChoice, "ALPHA/1")
            mx = parse(PrefixChoice, "Alpha/1")
            @test lo == up == mx
            # Shortcode
            @test startswith(shortcode(parse(PrefixChoice, "alpha/1")), "alpha/")
            @test startswith(shortcode(parse(PrefixChoice, "beta/1")), "beta/")
            # Errors
            @test tryparse(PrefixChoice, "gamma/1") === nothing
            @test_throws MalformedIdentifier parse(PrefixChoice, "gamma/1")
            # Round-trips
            check_roundtrips(PrefixChoice, ("alpha/0", "alpha/255", "beta/0", "beta/255"))
            @test_neverthrow parsebytes(PrefixChoice, ::Vector{UInt8})
        end

        @testset "ChoiceField" begin
            iddef = :(@defid ChoiceField (:kind(choice("A", "B", "C")), "-",
                       :id(digits(max=999))))
            @test parsebytes_complexity(iddef) == (branches=7:9, branch_total=9, ops=29:50)
            eval(iddef)
            # Properties
            @test propertynames(parse(ChoiceField, "A-1")) == (:kind, :id)
            @test parse(ChoiceField, "B-99").kind === :B
            @test parse(ChoiceField, "A-1").kind === :A
            @test parse(ChoiceField, "C-0").kind === :C
            # Different choices are not equal
            @test parse(ChoiceField, "A-1") != parse(ChoiceField, "B-1")
            # Round-trips
            check_roundtrips(ChoiceField, ("A-0", "B-500", "C-999"))
            @test_neverthrow parsebytes(ChoiceField, ::Vector{UInt8})
        end

        @testset "EmptyChoice" begin
            iddef = :(@defid EmptyChoice (:prefix(choice("v.", "")), :num(digits(4:4))))
            @test parsebytes_complexity(iddef) == (branches=4:5, branch_total=5, ops=27:29)
            eval(iddef)
            # Parsing with prefix
            wpfx = parse(EmptyChoice, "v.1234")
            @test wpfx isa EmptyChoice
            @test wpfx.prefix === Symbol("v.")
            @test wpfx.num == 1234
            # Parsing without prefix (empty option)
            bare = parse(EmptyChoice, "1234")
            @test bare isa EmptyChoice
            @test bare.prefix === nothing
            @test bare.num == 1234
            # Different representations are not equal
            @test wpfx != bare
            # Bounds reflect both paths
            @test FastIdentifiers.parsebounds(EmptyChoice) == (4, 6)
            @test FastIdentifiers.printbounds(EmptyChoice) == (4, 6)
            # Case folding on prefix
            @test parse(EmptyChoice, "V.5678") == parse(EmptyChoice, "v.5678")
            # Errors
            @test tryparse(EmptyChoice, "v.12") === nothing
            @test tryparse(EmptyChoice, "123") === nothing
            @test tryparse(EmptyChoice, "v.12345") === nothing
            @test tryparse(EmptyChoice, "12345") === nothing
            @test_throws MalformedIdentifier parse(EmptyChoice, "x.1234")
            # Round-trips
            check_roundtrips(EmptyChoice, ("v.0000", "v.9999", "0000", "9999"))
            @test_neverthrow parsebytes(EmptyChoice, ::Vector{UInt8})
        end

        @testset "OptionalChoice" begin
            iddef = :(@defid OptionalChoice (:id(digits(max=999)),
                       optional("-", :suffix(choice("x", "y")))))
            @test parsebytes_complexity(iddef) == (branches=6:11, branch_total=11, ops=23:56)
            eval(iddef)
            # Absent
            plain = parse(OptionalChoice, "42")
            @test plain.suffix === nothing
            # Present
            withx = parse(OptionalChoice, "42-x")
            @test withx.suffix === :x
            withy = parse(OptionalChoice, "42-y")
            @test withy.suffix === :y
            @test plain != withx
            @test withx != withy
            # Round-trips
            check_roundtrips(OptionalChoice, ("42", "42-x", "42-y"))
            @test_neverthrow parsebytes(OptionalChoice, ::Vector{UInt8})
        end
        # ── Extended choice coverage: table hash, linear scan, many options ──

        @testset "ManyChoiceVar (table hash, multi-tail verify)" begin
            # 7 variable-length options → table-tier hash lookup + codeunit-loop tail verify
            iddef = :(@defid ManyChoiceVar (:method(choice("get", "put", "post", "head",
                                                           "delete", "patch", "options")),
                       "/", :id(digits(max=999))))
            @test parsebytes_complexity(iddef) == (branches=7:13, branch_total=13, ops=49:57)
            eval(iddef)
            # All options parse correctly
            for m in ("get", "put", "post", "head", "delete", "patch", "options")
                id = parse(ManyChoiceVar, "$m/42")
                @test id.method === Symbol(m)
                @test id.id == 42
            end
            # Properties
            @test propertynames(parse(ManyChoiceVar, "get/1")) == (:method, :id)
            # Case folding
            @test parse(ManyChoiceVar, "GET/1") == parse(ManyChoiceVar, "get/1")
            @test parse(ManyChoiceVar, "DeLeTe/0") == parse(ManyChoiceVar, "delete/0")
            # Different choices are not equal
            @test parse(ManyChoiceVar, "get/1") != parse(ManyChoiceVar, "put/1")
            # Shortcode
            @test startswith(shortcode(parse(ManyChoiceVar, "options/5")), "options/")
            @test shortcode(parse(ManyChoiceVar, "get/42")) == "get/42"
            # Errors
            @test tryparse(ManyChoiceVar, "trace/1") === nothing
            @test tryparse(ManyChoiceVar, "ge/1") === nothing
            @test tryparse(ManyChoiceVar, "") === nothing
            @test_throws MalformedIdentifier parse(ManyChoiceVar, "trace/1")
            # Round-trips
            check_roundtrips(ManyChoiceVar, (
                "get/0", "put/1", "post/42", "head/100",
                "delete/500", "patch/999", "options/0"))
            @test_neverthrow parsebytes(ManyChoiceVar, ::Vector{UInt8})
        end

        @testset "ManyChoiceFixed (non-injective direct hash)" begin
            # 5 same-length options → non-injective mod-family direct hash, full verification
            iddef = :(@defid ManyChoiceFixed (:kind(choice("alpha", "bravo", "delta",
                                                           "gamma", "sigma")),
                       "-", :id(digits(max=999))))
            @test parsebytes_complexity(iddef) == (branches=5:7, branch_total=7, ops=44:48)
            eval(iddef)
            # All options parse correctly
            for k in ("alpha", "bravo", "delta", "gamma", "sigma")
                id = parse(ManyChoiceFixed, "$k-99")
                @test id.kind === Symbol(k)
                @test id.id == 99
            end
            # Properties
            @test propertynames(parse(ManyChoiceFixed, "alpha-0")) == (:kind, :id)
            # Case folding
            @test parse(ManyChoiceFixed, "ALPHA-1") == parse(ManyChoiceFixed, "alpha-1")
            @test parse(ManyChoiceFixed, "Sigma-0") == parse(ManyChoiceFixed, "sigma-0")
            # Different choices are not equal
            @test parse(ManyChoiceFixed, "alpha-1") != parse(ManyChoiceFixed, "bravo-1")
            # Errors
            @test tryparse(ManyChoiceFixed, "omega-1") === nothing
            @test tryparse(ManyChoiceFixed, "") === nothing
            @test_throws MalformedIdentifier parse(ManyChoiceFixed, "omega-1")
            # Round-trips
            check_roundtrips(ManyChoiceFixed, (
                "alpha-0", "bravo-42", "delta-500", "gamma-999", "sigma-1"))
            @test_neverthrow parsebytes(ManyChoiceFixed, ::Vector{UInt8})
        end

        @testset "LinearChoice (linear scan fallback)" begin
            # Options share prefix up to shortest → no discriminating byte window → linear scan
            iddef = :(@defid LinearChoice (:pfx(choice("ab", "abc", "abcd", "abcde")),
                       :id(digits(max=99))))
            @test parsebytes_complexity(iddef) == (branches=7:7, branch_total=7, ops=42:44)
            eval(iddef)
            # All options parse correctly
            for p in ("ab", "abc", "abcd", "abcde")
                id = parse(LinearChoice, "$(p)42")
                @test id.pfx === Symbol(p)
                @test id.id == 42
            end
            # Properties
            @test propertynames(parse(LinearChoice, "ab1")) == (:pfx, :id)
            # Case folding
            @test parse(LinearChoice, "AB42") == parse(LinearChoice, "ab42")
            @test parse(LinearChoice, "ABCDE1") == parse(LinearChoice, "abcde1")
            # Different choices are not equal
            @test parse(LinearChoice, "ab1") != parse(LinearChoice, "abc1")
            # Errors
            @test tryparse(LinearChoice, "a1") === nothing
            @test tryparse(LinearChoice, "abcdef1") === nothing
            @test tryparse(LinearChoice, "") === nothing
            @test_throws MalformedIdentifier parse(LinearChoice, "xyz1")
            # Round-trips
            check_roundtrips(LinearChoice, ("ab0", "abc42", "abcd99", "abcde1"))
            @test_neverthrow parsebytes(LinearChoice, ::Vector{UInt8})
        end

        @testset "ManyChoiceOpt (many options in optional)" begin
            # 5 options inside optional(...) — exercises choice + optional interaction
            iddef = :(@defid ManyChoiceOpt (:id(digits(max=999)),
                       optional("-", :tag(choice("draft", "final", "void",
                                                 "open", "shut")))))
            @test parsebytes_complexity(iddef) == (branches=6:15, branch_total=15, ops=23:64)
            eval(iddef)
            # All tags present
            for t in ("draft", "final", "void", "open", "shut")
                id = parse(ManyChoiceOpt, "42-$t")
                @test id.tag === Symbol(t)
                @test id.id == 42
            end
            # Absent
            plain = parse(ManyChoiceOpt, "42")
            @test plain.tag === nothing
            @test plain.id == 42
            # Present is distinct from absent
            @test parse(ManyChoiceOpt, "42-draft") != parse(ManyChoiceOpt, "42")
            # Different tags are not equal
            @test parse(ManyChoiceOpt, "42-open") != parse(ManyChoiceOpt, "42-shut")
            # Case folding
            @test parse(ManyChoiceOpt, "42-DRAFT") == parse(ManyChoiceOpt, "42-draft")
            # Errors
            @test tryparse(ManyChoiceOpt, "42-unknown") === nothing
            # Round-trips
            check_roundtrips(ManyChoiceOpt, (
                "42", "42-draft", "42-final", "42-void", "42-open", "42-shut"))
            @test_neverthrow parsebytes(ManyChoiceOpt, ::Vector{UInt8})
        end
        @testset "BackwardChoice (backward-aligned verify)" begin
            # 7-byte prefix gives parsed_min=7 >= 3 (padding for 5-byte opts in UInt64)
            iddef = :(@defid BackwardChoice ("PREFIX-",
                       :kind(choice("alpha", "bravo", "delta", "gamma", "sigma")),
                       "-", :id(digits(max=99))))
            @test parsebytes_complexity(iddef) == (branches=6:7, branch_total=7, ops=42:45)
            eval(iddef)
            for k in ("alpha", "bravo", "delta", "gamma", "sigma")
                id = parse(BackwardChoice, "PREFIX-$k-99")
                @test id.kind === Symbol(k)
                @test id.id == 99
            end
            @test parse(BackwardChoice, "PREFIX-ALPHA-1") == parse(BackwardChoice, "PREFIX-alpha-1")
            @test parse(BackwardChoice, "PREFIX-alpha-1") != parse(BackwardChoice, "PREFIX-bravo-1")
            @test tryparse(BackwardChoice, "PREFIX-omega-1") === nothing
            @test tryparse(BackwardChoice, "") === nothing
            check_roundtrips(BackwardChoice, (
                "PREFIX-alpha-0", "PREFIX-bravo-42", "PREFIX-delta-50",
                "PREFIX-gamma-99", "PREFIX-sigma-1"))
            @test_neverthrow parsebytes(BackwardChoice, ::Vector{UInt8})
        end

        @testset "SuffixChoice (common suffix optimisation)" begin
            # Variable-length options sharing trailing "/" — suffix check replaces tail verify
            iddef = :(@defid SuffixChoice (:kind(choice("alpha/", "beta/", "delta/")),
                       :id(digits(max=999))))
            @test parsebytes_complexity(iddef) == (branches=5:9, branch_total=9, ops=45:51)
            eval(iddef)
            for k in ("alpha/", "beta/", "delta/")
                id = parse(SuffixChoice, "$(k)42")
                @test id.kind === Symbol(k)
                @test id.id == 42
            end
            @test parse(SuffixChoice, "ALPHA/1") == parse(SuffixChoice, "alpha/1")
            @test parse(SuffixChoice, "alpha/1") != parse(SuffixChoice, "beta/1")
            @test tryparse(SuffixChoice, "gamma/1") === nothing
            @test tryparse(SuffixChoice, "") === nothing
            check_roundtrips(SuffixChoice, ("alpha/0", "alpha/999", "beta/42", "delta/1"))
            @test_neverthrow parsebytes(SuffixChoice, ::Vector{UInt8})
        end
    end # choice

    @testset "skip" begin
        @testset "Skippable" begin
            iddef = :(@defid Skippable (:a(digits(3)), skip(print="-"), :b(digits(3))))
            @test parsebytes_complexity(iddef) == (branches=6:6, branch_total=6, ops=43:44)
            eval(iddef)
            # Separator present
            id = parse(Skippable, "123-456")
            @test id.a == 123
            @test id.b == 456
            # Separator absent
            id = parse(Skippable, "123456")
            @test id.a == 123
            @test id.b == 456
            # With or without separator are equal
            @test parse(Skippable, "123-456") == parse(Skippable, "123456")
            # Properties
            @test propertynames(parse(Skippable, "123456")) == (:a, :b)
            # Round-trips
            check_roundtrips(Skippable, ("123456", "000000"))
            @test_neverthrow parsebytes(Skippable, ::Vector{UInt8})
        end

        @testset "MultiSkip" begin
            iddef = :(@defid MultiSkip (:a(digits(2)),
                       skip(" ", "/", print="-"), :b(digits(2))))
            @test parsebytes_complexity(iddef) == (branches=5:8, branch_total=8, ops=33:34)
            eval(iddef)
            # All skip targets produce the same result
            a = parse(MultiSkip, "12-34")
            b = parse(MultiSkip, "12 34")
            c = parse(MultiSkip, "12/34")
            d = parse(MultiSkip, "1234")
            @test a == b == c == d
            # Round-trips
            check_roundtrips(MultiSkip, ("1234",))
            @test_neverthrow parsebytes(MultiSkip, ::Vector{UInt8})
        end
    end # skip

    @testset "optional" begin
        @testset "WithOptional" begin
            iddef = :(@defid WithOptional (:id(digits(max=9999)),
                       optional(".v", :version(digits(max=255)))))
            @test parsebytes_complexity(iddef) == (branches=6:13, branch_total=13, ops=24:89)
            eval(iddef)
            # Present
            id = parse(WithOptional, "42.v3")
            @test id.id == 42
            @test id.version == 3
            # Absent
            id = parse(WithOptional, "42")
            @test id.id == 42
            @test id.version === nothing
            # Properties
            @test propertynames(parse(WithOptional, "1")) == (:id, :version)
            @test_throws Exception parse(WithOptional, "1").missing_field
            # Shortcode
            @test shortcode(parse(WithOptional, "5.v1")) == "5.v1"
            @test shortcode(parse(WithOptional, "5")) == "5"
            # Zero-valued optional (distinct from absent)
            present = parse(WithOptional, "1.v0")
            absent = parse(WithOptional, "1")
            @test present.version == 0
            @test absent.version === nothing
            @test present != absent
            # Usable in Sets
            s = Set{WithOptional}()
            push!(s, parse(WithOptional, "1"))
            push!(s, parse(WithOptional, "1.v0"))
            push!(s, parse(WithOptional, "1"))  # duplicate
            @test length(s) == 2
            # Round-trips
            check_roundtrips(WithOptional, ("0", "42", "42.v0", "42.v255"))
            @test_neverthrow parsebytes(WithOptional, ::Vector{UInt8})
        end

        @testset "DoubleOptional" begin
            iddef = :(@defid DoubleOptional (:id(digits(max=9999)),
                       optional(".v", :version(digits(max=255)),
                                optional(".p", :patch(digits(max=65535))))))
            @test parsebytes_complexity(iddef) == (branches=6:25, branch_total=25, ops=24:152)
            eval(iddef)
            # All present
            full = parse(DoubleOptional, "100.v2.p500")
            @test full.id == 100
            @test full.version == 2
            @test full.patch == 500
            # Inner absent
            partial = parse(DoubleOptional, "100.v2")
            @test partial.version == 2
            @test partial.patch === nothing
            # Both absent
            bare = parse(DoubleOptional, "100")
            @test bare.version === nothing
            @test bare.patch === nothing
            # Properties
            @test propertynames(parse(DoubleOptional, "1")) == (:id, :version, :patch)
            # Round-trips
            check_roundtrips(DoubleOptional, ("100", "100.v2", "100.v2.p0", "100.v2.p500"))
            @test_neverthrow parsebytes(DoubleOptional, ::Vector{UInt8})
        end

        @testset "TrailingOpt" begin
            iddef = :(@defid TrailingOpt (:id(digits(max=999)),
                       optional("-", :tag(choice("alpha", "beta", "rc")),
                                :rev(digits(max=99)))))
            @test parsebytes_complexity(iddef) == (branches=6:18, branch_total=18, ops=23:94)
            eval(iddef)
            # Bare
            bare = parse(TrailingOpt, "42")
            @test bare.id == 42
            @test bare.tag === nothing
            @test bare.rev === nothing
            # Tagged
            tagged = parse(TrailingOpt, "42-alpha3")
            @test tagged.id == 42
            @test tagged.tag === :alpha
            @test tagged.rev == 3
            # Properties
            @test propertynames(parse(TrailingOpt, "1")) == (:id, :tag, :rev)
            # Mid-optional failure: exercises pos-rewind when early nodes
            # in the optional succeed but a later node fails. Without rewind,
            # pos would advance past the partial match and the parse would
            # incorrectly accept (e.g. "42-alpha" accepted as id=42).
            @test tryparse(TrailingOpt, "42-alpha") === nothing  # choice ok, digits missing
            @test tryparse(TrailingOpt, "42-beta") === nothing
            @test tryparse(TrailingOpt, "42-") === nothing       # separator ok, choice missing
            # Round-trips
            check_roundtrips(TrailingOpt, ("42", "42-alpha0", "42-beta99", "42-rc1"))
            @test_neverthrow parsebytes(TrailingOpt, ::Vector{UInt8})
        end

        @testset "OptRewind" begin
            # Exercises pos-rewind for a successful parse: the optional's leading
            # literal "x" overlaps with the trailing "xy", so when the optional's
            # value node fails, pos must rewind for "xy" to match.
            iddef = :(@defid OptRewind (:id(digits(max=99)),
                       optional("x", :extra(digits(max=9))), "xy"))
            @test parsebytes_complexity(iddef) == (branches=5:8, branch_total=8, ops=26:42)
            eval(iddef)
            # Optional absent, trailing literal matches after rewind
            @test parse(OptRewind, "42xy").id == 42
            @test parse(OptRewind, "42xy").extra === nothing
            # Optional present
            @test parse(OptRewind, "42x5xy").id == 42
            @test parse(OptRewind, "42x5xy").extra == 5
            # Mid-optional failure still rejects malformed input
            @test_broken tryparse(OptRewind, "42x") === nothing
            @test tryparse(OptRewind, "42") === nothing
            check_roundtrips(OptRewind, ("42xy", "42x0xy", "42x9xy"))
            @test_neverthrow parsebytes(OptRewind, ::Vector{UInt8})
        end
        @testset "OptSentinelHoist" begin
            # Two digits at a 2^k-1 boundary in one optional: hoisting saves 1 bit
            # digits(max=126) → range=127=2^7-1. +1 crosses to 8 bits.
            # Old: +1 each → 8+8=16 optional bits.
            # New: first claims (8 bits), second skips (7 bits) → 15. Saves 1 bit.
            iddef = :(@defid OptSentinelHoist (:id(digits(max=99)),
                       optional("-", :a(digits(3:3, max=126)), ".", :b(digits(3:3, max=126)))))
            @test parsebytes_complexity(iddef) == (branches=6:14, branch_total=14, ops=20:80)
            eval(iddef)
            @test FastIdentifiers.nbits(OptSentinelHoist) == 7 + 8 + 6  # 22, not 23
            @test parse(OptSentinelHoist, "42-050.100").a == 50
            @test parse(OptSentinelHoist, "42-050.100").b == 100
            @test parse(OptSentinelHoist, "42").a === nothing
            @test parse(OptSentinelHoist, "42").b === nothing
            @test parse(OptSentinelHoist, "42-050.100") != parse(OptSentinelHoist, "42")
            @test parse(OptSentinelHoist, "42-000.000") != parse(OptSentinelHoist, "42")
            check_roundtrips(OptSentinelHoist, ("42", "42-000.000", "42-050.100", "42-126.126"))
            @test_neverthrow parsebytes(OptSentinelHoist, ::Vector{UInt8})
        end
    end # optional

    @testset "letters" begin
        @testset "LettersFolded" begin
            iddef = :(@defid LettersFolded ("R-",
                       :code(letters(3, upper=true, casefold=true)),
                       "-", :id(digits(max=999))))
            @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=43:43)
            eval(iddef)
            id = parse(LettersFolded, "R-HSA-42")
            @test id.code == "HSA"
            @test id.id == 42
            # Case folding
            @test parse(LettersFolded, "R-hsa-42") == id
            # Round-trips
            check_roundtrips(LettersFolded, ("R-HSA-42", "R-ABC-0"))
            @test_neverthrow parsebytes(LettersFolded, ::Vector{UInt8})
        end

        @testset "LettersUpper" begin
            iddef = :(@defid LettersUpper ("R-",
                       :code(letters(3, upper=true, casefold=false)),
                       "-", :id(digits(max=999))))
            @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=43:43)
            eval(iddef)
            id = parse(LettersUpper, "R-HSA-42")
            @test id.code == "HSA"
            # Rejects lowercase
            @test tryparse(LettersUpper, "R-hsa-42") === nothing
            # Round-trips
            check_roundtrips(LettersUpper, ("R-HSA-42",))
            @test_neverthrow parsebytes(LettersUpper, ::Vector{UInt8})
        end

        @testset "LettersVar" begin
            iddef = :(@defid LettersVar (:prefix(letters(3:5, lower=true, casefold=false)),
                       :id(digits(max=9999))))
            @test parsebytes_complexity(iddef) == (branches=4:4, branch_total=4, ops=50:50)
            eval(iddef)
            # Variable lengths
            id3 = parse(LettersVar, "abc1")
            id5 = parse(LettersVar, "abcde1")
            @test id3.prefix == "abc"
            @test id5.prefix == "abcde"
            # Rejects too short
            @test tryparse(LettersVar, "ab1") === nothing
            # Rejects uppercase
            @test tryparse(LettersVar, "ABC1") === nothing
            # Round-trips
            check_roundtrips(LettersVar, ("abc1", "abcde9999"))
            @test_neverthrow parsebytes(LettersVar, ::Vector{UInt8})
        end

        @testset "LettersSens" begin
            iddef = :(@defid LettersSens :code(letters(4, casefold=false)))
            @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
            eval(iddef)
            # Mixed case preserved
            a = parse(LettersSens, "ABcd")
            b = parse(LettersSens, "abCD")
            @test a != b
            @test a.code == "ABcd"
            @test b.code == "abCD"
            # Round-trips
            check_roundtrips(LettersSens, ("ABcd", "abCD"))
            @test_neverthrow parsebytes(LettersSens, ::Vector{UInt8})
        end

        @testset "LettersDirectLen" begin
            iddef = :(@defid LettersDirectLen ("D-",
                       :code(letters(1:3, upper=true, casefold=true)),
                       :id(digits(max=99))))
            @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=48:48)
            eval(iddef)
            # Various lengths
            id1 = parse(LettersDirectLen, "D-A1")
            id2 = parse(LettersDirectLen, "D-AB1")
            id3 = parse(LettersDirectLen, "D-ABC1")
            @test id1.code == "A"
            @test id2.code == "AB"
            @test id3.code == "ABC"
            @test id1.id == id2.id == id3.id == 1
            @test id1 != id2 != id3
            # Case folding
            @test parse(LettersDirectLen, "D-abc42") == parse(LettersDirectLen, "D-ABC42")
            # Round-trips
            check_roundtrips(LettersDirectLen, ("D-A1", "D-AB42", "D-ABC99"))
            @test_neverthrow parsebytes(LettersDirectLen, ::Vector{UInt8})
        end

        @testset "OptLettersFixed" begin
            iddef = :(@defid OptLettersFixed (:id(digits(max=999)),
                       optional("-", :suffix(letters(2, upper=true, casefold=true)))))
            @test parsebytes_complexity(iddef) == (branches=6:10, branch_total=10, ops=23:54)
            eval(iddef)
            # Present
            id = parse(OptLettersFixed, "42-AB")
            @test id.id == 42
            @test id.suffix == "AB"
            # Absent
            id = parse(OptLettersFixed, "42")
            @test id.id == 42
            @test id.suffix === nothing
            # Case folding
            @test parse(OptLettersFixed, "42-ab") == parse(OptLettersFixed, "42-AB")
            # Boundary char 'A' (index 0) round-trips
            id = parse(OptLettersFixed, "42-AA")
            @test id.suffix == "AA"
            @test parse(OptLettersFixed, shortcode(id)) == id
            # Present is distinct from absent
            @test parse(OptLettersFixed, "42-AA") != parse(OptLettersFixed, "42")
            # Round-trips
            check_roundtrips(OptLettersFixed, ("42", "42-AA", "42-ZZ"))
            @test_neverthrow parsebytes(OptLettersFixed, ::Vector{UInt8})
        end

        @testset "OptLettersVar" begin
            iddef = :(@defid OptLettersVar (:id(digits(max=999)),
                       optional("-", :tag(letters(2:4, lower=true, casefold=false)))))
            @test parsebytes_complexity(iddef) == (branches=6:10, branch_total=10, ops=23:63)
            eval(iddef)
            # Present
            id = parse(OptLettersVar, "42-abc")
            @test id.id == 42
            @test id.tag == "abc"
            # Absent
            id = parse(OptLettersVar, "42")
            @test id.id == 42
            @test id.tag === nothing
            # Various lengths
            @test parse(OptLettersVar, "1-ab").tag == "ab"
            @test parse(OptLettersVar, "1-abc").tag == "abc"
            @test parse(OptLettersVar, "1-abcd").tag == "abcd"
            # Round-trips
            check_roundtrips(OptLettersVar, ("42", "42-ab", "42-abcd"))
            @test_neverthrow parsebytes(OptLettersVar, ::Vector{UInt8})
        end

        @testset "OptLettersZero" begin
            iddef = :(@defid OptLettersZero (:id(digits(max=999)),
                       optional("-", :tag(letters(0:3, lower=true, casefold=false)))))
            @test parsebytes_complexity(iddef) == (branches=6:10, branch_total=10, ops=23:62)
            eval(iddef)
            # Present
            id = parse(OptLettersZero, "42-abc")
            @test id.id == 42
            @test id.tag == "abc"
            # Absent
            id = parse(OptLettersZero, "42")
            @test id.id == 42
            @test id.tag === nothing
            # Round-trips
            check_roundtrips(OptLettersZero, ("42", "42-a", "42-abc"))
            @test_neverthrow parsebytes(OptLettersZero, ::Vector{UInt8})
        end
    end # letters

@testset "alphnum" begin
    @testset "AlphnumFolded" begin
        iddef = :(@defid AlphnumFolded :code(alphnum(4, upper=true, casefold=true)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        id = parse(AlphnumFolded, "1ABC")
        @test id.code == "1ABC"
        # Case folding
        @test parse(AlphnumFolded, "1abc") == id
        # Round-trips
        check_roundtrips(AlphnumFolded, ("1ABC", "9ZZZ"))
        @test_neverthrow parsebytes(AlphnumFolded, ::Vector{UInt8})
    end

    @testset "AlphnumFixed" begin
        iddef = :(@defid AlphnumFixed :code(alphnum(4, upper=true, casefold=false)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        id = parse(AlphnumFixed, "1ABC")
        @test id.code == "1ABC"
        # Rejects lowercase
        @test tryparse(AlphnumFixed, "1abc") === nothing
        # Round-trips
        check_roundtrips(AlphnumFixed, ("1ABC",))
        @test_neverthrow parsebytes(AlphnumFixed, ::Vector{UInt8})
    end

    @testset "AlphnumVar" begin
        iddef = :(@defid AlphnumVar :code(alphnum(2:4, casefold=false)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=16:16)
        eval(iddef)
        id = parse(AlphnumVar, "aB3")
        @test id.code == "aB3"
        # Rejects too short
        @test tryparse(AlphnumVar, "a") === nothing
        # Round-trips
        check_roundtrips(AlphnumVar, ("aB", "aB3Z"))
        @test_neverthrow parsebytes(AlphnumVar, ::Vector{UInt8})
    end

    @testset "AlphnumDirectLen" begin
        iddef = :(@defid AlphnumDirectLen ("A-",
                   :code(alphnum(1:3, upper=true, casefold=true)),
                   "-", :id(digits(max=99))))
        @test parsebytes_complexity(iddef) == (branches=6:7, branch_total=7, ops=49:49)
        eval(iddef)
        # Various lengths
        id1 = parse(AlphnumDirectLen, "A-1-2")
        id2 = parse(AlphnumDirectLen, "A-1X-42")
        id3 = parse(AlphnumDirectLen, "A-AB3-99")
        @test id1.code == "1"
        @test id2.code == "1X"
        @test id3.code == "AB3"
        @test id1.id == 2
        @test id2.id == 42
        @test id3.id == 99
        # Case folding
        @test parse(AlphnumDirectLen, "A-ab3-99") == parse(AlphnumDirectLen, "A-AB3-99")
        # Round-trips
        check_roundtrips(AlphnumDirectLen, ("A-1-0", "A-1X-42", "A-AB3-99"))
        @test_neverthrow parsebytes(AlphnumDirectLen, ::Vector{UInt8})
    end

    @testset "OptAlphnumFixed" begin
        iddef = :(@defid OptAlphnumFixed (:id(digits(max=99)),
                   optional(".", :code(alphnum(3, upper=true, casefold=true)))))
        @test parsebytes_complexity(iddef) == (branches=6:10, branch_total=10, ops=20:46)
        eval(iddef)
        # Present
        id = parse(OptAlphnumFixed, "42.A1B")
        @test id.id == 42
        @test id.code == "A1B"
        # Absent
        id = parse(OptAlphnumFixed, "42")
        @test id.id == 42
        @test id.code === nothing
        # Case folding
        @test parse(OptAlphnumFixed, "42.a1b") == parse(OptAlphnumFixed, "42.A1B")
        # Round-trips
        check_roundtrips(OptAlphnumFixed, ("42", "42.0A0", "42.Z9Z"))
        @test_neverthrow parsebytes(OptAlphnumFixed, ::Vector{UInt8})
    end

    @testset "NestedOptCharseq" begin
        iddef = :(@defid NestedOptCharseq (:id(digits(max=999)),
                   optional("-", :prefix(letters(2, upper=true, casefold=true)),
                            optional(".", :extra(digits(max=99))))))
        @test parsebytes_complexity(iddef) == (branches=6:15, branch_total=15, ops=23:91)
        eval(iddef)
        # All present
        id = parse(NestedOptCharseq, "42-AB.5")
        @test id.id == 42
        @test id.prefix == "AB"
        @test id.extra == 5
        # Inner absent
        id = parse(NestedOptCharseq, "42-AB")
        @test id.prefix == "AB"
        @test id.extra === nothing
        # Both absent
        id = parse(NestedOptCharseq, "42")
        @test id.prefix === nothing
        @test id.extra === nothing
        # Round-trips
        check_roundtrips(NestedOptCharseq, ("42", "42-AB", "42-AB.5", "42-AB.99"))
        @test_neverthrow parsebytes(NestedOptCharseq, ::Vector{UInt8})
    end
end # alphnum

@testset "hex" begin
    @testset "HexFolded" begin
        iddef = :(@defid HexFolded ("0x", :code(hex(8, casefold=true))))
        @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=9:9)
        eval(iddef)
        id = parse(HexFolded, "0xDEADBEEF")
        @test id.code == "DEADBEEF"
        # 16 values → 4 bits/char, 8 chars = 32 bits
        @test sizeof(HexFolded) == 4
        # Case folding
        @test parse(HexFolded, "0xdeadbeef") == id
        @test parse(HexFolded, "0xDeAdBeEf") == id
        # Round-trips
        check_roundtrips(HexFolded, ("0x00000000", "0xDEADBEEF", "0xFFFFFFFF"))
        @test_neverthrow parsebytes(HexFolded, ::Vector{UInt8})
    end
    @testset "HexUpper" begin
        iddef = :(@defid HexUpper :code(hex(4, upper=true, casefold=false)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        id = parse(HexUpper, "1A2B")
        @test id.code == "1A2B"
        # Rejects lowercase
        @test tryparse(HexUpper, "1a2b") === nothing
        # Round-trips
        check_roundtrips(HexUpper, ("0000", "1A2B", "FFFF"))
        @test_neverthrow parsebytes(HexUpper, ::Vector{UInt8})
    end
    @testset "HexLower" begin
        iddef = :(@defid HexLower :code(hex(4, lower=true, casefold=false)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        id = parse(HexLower, "1a2b")
        @test id.code == "1a2b"
        # Rejects uppercase
        @test tryparse(HexLower, "1A2B") === nothing
        # Round-trips
        check_roundtrips(HexLower, ("0000", "1a2b", "ffff"))
        @test_neverthrow parsebytes(HexLower, ::Vector{UInt8})
    end
    @testset "HexVar" begin
        iddef = :(@defid HexVar :code(hex(2:4, casefold=true)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=16:16)
        eval(iddef)
        # Variable lengths
        id2 = parse(HexVar, "AB")
        id3 = parse(HexVar, "ABC")
        id4 = parse(HexVar, "ABCD")
        @test id2.code == "AB"
        @test id3.code == "ABC"
        @test id4.code == "ABCD"
        # Rejects too short
        @test tryparse(HexVar, "A") === nothing
        # Case folding
        @test parse(HexVar, "ab") == id2
        # Round-trips
        check_roundtrips(HexVar, ("AB", "ABC", "ABCD"))
        @test_neverthrow parsebytes(HexVar, ::Vector{UInt8})
    end
    @testset "OptHex" begin
        iddef = :(@defid OptHex (:id(digits(max=999)),
                   optional("-", :tag(hex(2, casefold=true)))))
        @test parsebytes_complexity(iddef) == (branches=6:10, branch_total=10, ops=23:54)
        eval(iddef)
        # Present
        id = parse(OptHex, "42-FF")
        @test id.id == 42
        @test id.tag == "FF"
        # Absent
        id = parse(OptHex, "42")
        @test id.id == 42
        @test id.tag === nothing
        # Case folding
        @test parse(OptHex, "42-ff") == parse(OptHex, "42-FF")
        # Boundary '0' (index 0) round-trips when present
        id = parse(OptHex, "42-00")
        @test id.tag == "00"
        @test parse(OptHex, shortcode(id)) == id
        # Present is distinct from absent
        @test parse(OptHex, "42-00") != parse(OptHex, "42")
        # Round-trips
        check_roundtrips(OptHex, ("42", "42-00", "42-FF"))
        @test_neverthrow parsebytes(OptHex, ::Vector{UInt8})
    end
    @testset "HexWithDigits" begin
        iddef = :(@defid HexWithDigits ("H-",
                   :hash(hex(6, casefold=true)),
                   "-", :ver(digits(max=99))))
        @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=39:39)
        eval(iddef)
        id = parse(HexWithDigits, "H-A1B2C3-7")
        @test id.hash == "A1B2C3"
        @test id.ver == 7
        # Case folding
        @test parse(HexWithDigits, "H-a1b2c3-7") == id
        # Round-trips
        check_roundtrips(HexWithDigits, ("H-000000-0", "H-A1B2C3-7", "H-FFFFFF-99"))
        @test_neverthrow parsebytes(HexWithDigits, ::Vector{UInt8})
    end
    # Reject non-hex letters
    @testset "HexRejectsNonHex" begin
        eval(:(@defid HexReject :code(hex(4, casefold=true))))
        @test tryparse(HexReject, "ABCG") === nothing
        @test tryparse(HexReject, "GHIJ") === nothing
        @test tryparse(HexReject, "abcg") === nothing
        # Valid hex boundary chars
        @test parse(HexReject, "0000").code == "0000"
        @test parse(HexReject, "9999").code == "9999"
        @test parse(HexReject, "AAAA").code == "AAAA"
        @test parse(HexReject, "FFFF").code == "FFFF"
    end
end # hex

@testset "charset" begin
    @testset "CharsetFixed" begin
        # Crockford-like: digits + uppercase letters (no I, L, O, U)
        iddef = :(@defid CharsetFixed :code(charset(4,
            '0':'9', 'A':'H', 'J':'K', 'M':'N', 'P':'T', 'V':'Z', casefold=true)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        id = parse(CharsetFixed, "A1B2")
        @test id.code == "A1B2"
        # Case folding
        @test parse(CharsetFixed, "a1b2") == id
        @test parse(CharsetFixed, "z1b2") == parse(CharsetFixed, "Z1B2")
        # Range boundary: first and last of each range
        @test parse(CharsetFixed, "0000").code == "0000"  # first of '0':'9'
        @test parse(CharsetFixed, "9999").code == "9999"  # last of '0':'9'
        @test parse(CharsetFixed, "AAAA").code == "AAAA"  # first of 'A':'H'
        @test parse(CharsetFixed, "HHHH").code == "HHHH"  # last of 'A':'H'
        @test parse(CharsetFixed, "JJJJ").code == "JJJJ"  # first of 'J':'K'
        @test parse(CharsetFixed, "KKKK").code == "KKKK"  # last of 'J':'K'
        @test parse(CharsetFixed, "VVVV").code == "VVVV"  # first of 'V':'Z'
        @test parse(CharsetFixed, "ZZZZ").code == "ZZZZ"  # last of 'V':'Z'
        # Excluded characters (gaps in the Crockford alphabet)
        @test tryparse(CharsetFixed, "IIII") === nothing  # 'I' excluded
        @test tryparse(CharsetFixed, "LLLL") === nothing  # 'L' excluded
        @test tryparse(CharsetFixed, "OOOO") === nothing  # 'O' excluded
        @test tryparse(CharsetFixed, "UUUU") === nothing  # 'U' excluded
        # Adjacent invalid: byte before '0' and after 'Z'
        @test tryparse(CharsetFixed, "////") === nothing  # '/' = '0' - 1
        @test tryparse(CharsetFixed, "[[[[") === nothing  # '[' = 'Z' + 1
        # Too short / too long
        @test tryparse(CharsetFixed, "ABC") === nothing
        @test tryparse(CharsetFixed, "ABCDE") === nothing
        # Round-trips
        check_roundtrips(CharsetFixed, ("0000", "A1B2", "ZZZZ", "HJKM"))
        @test_neverthrow parsebytes(CharsetFixed, ::Vector{UInt8})
    end
    @testset "CharsetSingleChars" begin
        # Charset with single characters mixed with ranges
        iddef = :(@defid CharsetSingleChars :code(charset(3, '0':'9', '-')))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        id = parse(CharsetSingleChars, "1-2")
        @test id.code == "1-2"
        # Boundary chars of '0':'9'
        @test parse(CharsetSingleChars, "000").code == "000"
        @test parse(CharsetSingleChars, "999").code == "999"
        # Single char '-' works
        @test parse(CharsetSingleChars, "---").code == "---"
        # Adjacent invalid bytes
        @test tryparse(CharsetSingleChars, "///") === nothing  # '/' = '0' - 1
        @test tryparse(CharsetSingleChars, ":::") === nothing  # ':' = '9' + 1
        @test tryparse(CharsetSingleChars, "...") === nothing  # '.' = '-' + 1 (not in set)
        @test tryparse(CharsetSingleChars, ",,,") === nothing  # ',' = '-' - 1
        # Letters rejected
        @test tryparse(CharsetSingleChars, "abc") === nothing
        @test tryparse(CharsetSingleChars, "ABC") === nothing
        # Length boundaries
        @test tryparse(CharsetSingleChars, "00") === nothing
        @test tryparse(CharsetSingleChars, "0000") === nothing
        # Round-trips
        check_roundtrips(CharsetSingleChars, ("000", "1-2", "---", "999"))
        @test_neverthrow parsebytes(CharsetSingleChars, ::Vector{UInt8})
    end
    @testset "CharsetVar" begin
        iddef = :(@defid CharsetVar :code(charset(2:4, 'A':'F', '0':'9', casefold=true)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=16:16)
        eval(iddef)
        # Exact length boundaries: min, middle, max
        id2 = parse(CharsetVar, "AB")
        id3 = parse(CharsetVar, "1F3")
        id4 = parse(CharsetVar, "DEAD")
        @test id2.code == "AB"
        @test id3.code == "1F3"
        @test id4.code == "DEAD"
        # Too short (1 char, below min=2)
        @test tryparse(CharsetVar, "A") === nothing
        # Too long is not rejected (parser stops at maxlen), but 5 chars won't match
        @test tryparse(CharsetVar, "ABCDE") === nothing
        # Range boundaries
        @test parse(CharsetVar, "AA").code == "AA"  # first of 'A':'F'
        @test parse(CharsetVar, "FF").code == "FF"  # last of 'A':'F'
        @test parse(CharsetVar, "00").code == "00"  # first of '0':'9'
        @test parse(CharsetVar, "99").code == "99"  # last of '0':'9'
        # Adjacent invalid (just outside ranges)
        @test tryparse(CharsetVar, "GG") === nothing  # 'G' = 'F' + 1
        @test tryparse(CharsetVar, "@@") === nothing  # '@' = 'A' - 1
        # Case folding
        @test parse(CharsetVar, "ab") == id2
        @test parse(CharsetVar, "dead") == id4
        # Round-trips
        check_roundtrips(CharsetVar, ("AB", "1F3", "DEAD", "00", "FF", "9999"))
        @test_neverthrow parsebytes(CharsetVar, ::Vector{UInt8})
    end
    @testset "OptCharset" begin
        iddef = :(@defid OptCharset (:id(digits(max=999)),
                   optional(".", :tag(charset(2, 'A':'Z', '0':'9', casefold=true)))))
        @test parsebytes_complexity(iddef) == (branches=6:10, branch_total=10, ops=23:54)
        eval(iddef)
        # Present
        id = parse(OptCharset, "42.AB")
        @test id.id == 42
        @test id.tag == "AB"
        # Absent
        id = parse(OptCharset, "42")
        @test id.id == 42
        @test id.tag === nothing
        # Case folding
        @test parse(OptCharset, "42.ab") == parse(OptCharset, "42.AB")
        # Present is distinct from absent
        @test parse(OptCharset, "42.00") != parse(OptCharset, "42")
        # Boundary: first/last valid chars in tag
        @test parse(OptCharset, "42.AA").tag == "AA"
        @test parse(OptCharset, "42.ZZ").tag == "ZZ"
        @test parse(OptCharset, "42.00").tag == "00"
        @test parse(OptCharset, "42.99").tag == "99"
        # Invalid chars after '.' cause overall parse failure (trailing content)
        @test tryparse(OptCharset, "42.[[") === nothing  # '[' = 'Z' + 1
        @test tryparse(OptCharset, "42.//") === nothing  # '/' = '0' - 1
        # Round-trips
        check_roundtrips(OptCharset, ("42", "42.00", "42.A0", "42.9Z", "42.ZZ"))
        @test_neverthrow parsebytes(OptCharset, ::Vector{UInt8})
    end
    @testset "CharsetNoCasefold" begin
        # No casefold, both cases provided as separate ranges
        iddef = :(@defid CharsetNoCasefold :code(charset(3, 'A':'Z', 'a':'z', casefold=false)))
        @test parsebytes_complexity(iddef) == (branches=2:2, branch_total=2, ops=7:7)
        eval(iddef)
        a = parse(CharsetNoCasefold, "ABc")
        b = parse(CharsetNoCasefold, "abC")
        @test a != b
        @test a.code == "ABc"
        @test b.code == "abC"
        # Range boundaries
        @test parse(CharsetNoCasefold, "AAA").code == "AAA"
        @test parse(CharsetNoCasefold, "ZZZ").code == "ZZZ"
        @test parse(CharsetNoCasefold, "aaa").code == "aaa"
        @test parse(CharsetNoCasefold, "zzz").code == "zzz"
        # Adjacent invalid
        @test tryparse(CharsetNoCasefold, "@@@") === nothing  # '@' = 'A' - 1
        @test tryparse(CharsetNoCasefold, "[[[") === nothing  # '[' = 'Z' + 1
        @test tryparse(CharsetNoCasefold, "```") === nothing  # '`' = 'a' - 1
        @test tryparse(CharsetNoCasefold, "{{{") === nothing  # '{' = 'z' + 1
        # Digits not in charset
        @test tryparse(CharsetNoCasefold, "123") === nothing
        # Round-trips
        check_roundtrips(CharsetNoCasefold, ("ABc", "abC", "AAA", "zzz"))
        @test_neverthrow parsebytes(CharsetNoCasefold, ::Vector{UInt8})
    end
    @testset "CharsetWithLiteral" begin
        iddef = :(@defid CharsetWithLiteral ("X-",
                   :hash(charset(4, '0':'9', 'A':'F', casefold=true)),
                   "-", :ver(digits(max=99))))
        @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=39:39)
        eval(iddef)
        id = parse(CharsetWithLiteral, "X-A1B2-7")
        @test id.hash == "A1B2"
        @test id.ver == 7
        # Case folding on hex part
        @test parse(CharsetWithLiteral, "X-a1b2-7") == id
        # Boundary chars in hex field
        @test parse(CharsetWithLiteral, "X-0000-0").hash == "0000"
        @test parse(CharsetWithLiteral, "X-9999-0").hash == "9999"
        @test parse(CharsetWithLiteral, "X-AAAA-0").hash == "AAAA"
        @test parse(CharsetWithLiteral, "X-FFFF-0").hash == "FFFF"
        # Invalid hex chars in hash field
        @test tryparse(CharsetWithLiteral, "X-GHIJ-1") === nothing
        @test tryparse(CharsetWithLiteral, "X-////-1") === nothing
        # Round-trips
        check_roundtrips(CharsetWithLiteral, ("X-0000-0", "X-A1B2-7", "X-FFFF-99"))
        @test_neverthrow parsebytes(CharsetWithLiteral, ::Vector{UInt8})
    end
end # charset

@testset "embed" begin
    # --- Inner types at various bit widths ---
    # <8 bits: 2-bit value (max=3) → 2 data bits, 1-byte primitive
    eval(:(@defid EmbTiny :id(digits(max=3))))
    # =8 bits: 8-bit value (max=255) → 8 data bits, 1-byte primitive
    eval(:(@defid Emb8 ("X", :id(digits(max=255)))))
    # >8 bits: 14-bit value (max=9999) → 14 data bits, 2-byte primitive
    eval(:(@defid Emb16 ("P", :id(digits(max=9999, pad=4)))))
    @testset "single embed <8 bits" begin
        iddef = :(@defid EmbedTinyOuter ("T-", :inner(embed(EmbTiny)), "-", :extra(digits(max=99))))
        @test parsebytes_complexity(iddef) == (branches=5:5, branch_total=5, ops=41:41)
        eval(iddef)
        @test sizeof(EmbedTinyOuter) >= 1
        # Parsing
        id = parse(EmbedTinyOuter, "T-3-42")
        @test id.inner isa EmbTiny
        @test id.inner.id == 3
        @test id.extra == 42
        @test parse(EmbedTinyOuter, "T-0-0").inner.id == 0
        @test parse(EmbedTinyOuter, "T-0-0").extra == 0
        # Properties
        @test propertynames(parse(EmbedTinyOuter, "T-1-2")) == (:inner, :extra)
        # Shortcode
        @test shortcode(parse(EmbedTinyOuter, "T-3-42")) == "T-3-42"
        # Equality
        @test parse(EmbedTinyOuter, "T-2-5") == parse(EmbedTinyOuter, "T-2-5")
        @test parse(EmbedTinyOuter, "T-2-5") != parse(EmbedTinyOuter, "T-2-6")
        @test parse(EmbedTinyOuter, "T-2-5") != parse(EmbedTinyOuter, "T-3-5")
        @test hash(parse(EmbedTinyOuter, "T-1-1")) == hash(parse(EmbedTinyOuter, "T-1-1"))
        # Errors
        @test tryparse(EmbedTinyOuter, "") === nothing
        @test tryparse(EmbedTinyOuter, "T-") === nothing
        @test tryparse(EmbedTinyOuter, "T-4-1") === nothing  # inner max is 3
        @test tryparse(EmbedTinyOuter, "T-1-100") === nothing  # extra max is 99
        @test tryparse(EmbedTinyOuter, "T-1") === nothing  # missing extra
        # Round-trips
        check_roundtrips(EmbedTinyOuter, ("T-0-0", "T-3-99", "T-1-50"))
        @test_neverthrow parsebytes(EmbedTinyOuter, ::Vector{UInt8})
    end
    @testset "single embed =8 bits" begin
        iddef = :(@defid Embed8Outer ("E-", :inner(embed(Emb8)), "-", :id(digits(max=9))))
        @test parsebytes_complexity(iddef) == (branches=6:7, branch_total=7, ops=24:24)
        eval(iddef)
        # Parsing
        id = parse(Embed8Outer, "E-X255-9")
        @test id.inner isa Emb8
        @test id.inner.id == 255
        @test id.id == 9
        @test parse(Embed8Outer, "E-X0-0").inner.id == 0
        # Shortcode roundtrip
        @test shortcode(parse(Embed8Outer, "E-X42-7")) == "E-X42-7"
        # Equality
        @test parse(Embed8Outer, "E-X1-2") == parse(Embed8Outer, "E-X1-2")
        @test parse(Embed8Outer, "E-X1-2") != parse(Embed8Outer, "E-X1-3")
        # Errors
        @test tryparse(Embed8Outer, "E-X256-1") === nothing  # inner overflow
        @test tryparse(Embed8Outer, "E-Y1-1") === nothing  # wrong inner prefix
        @test tryparse(Embed8Outer, "E-X1") === nothing  # missing separator+extra
        @test tryparse(Embed8Outer, "E-X-1") === nothing  # inner has no digits
        # Round-trips
        check_roundtrips(Embed8Outer, ("E-X0-0", "E-X255-9", "E-X128-5"))
        @test_neverthrow parsebytes(Embed8Outer, ::Vector{UInt8})
    end
    @testset "single embed >8 bits" begin
        iddef = :(@defid Embed16Outer ("R:", :inner(embed(Emb16)), "/", :tag(digits(max=99))))
        @test parsebytes_complexity(iddef) == (branches=6:7, branch_total=7, ops=45:45)
        eval(iddef)
        @test sizeof(Embed16Outer) >= 3
        # Parsing
        id = parse(Embed16Outer, "R:P9999/42")
        @test id.inner isa Emb16
        @test id.inner.id == 9999
        @test id.tag == 42
        @test parse(Embed16Outer, "R:P0000/0").inner.id == 0
        # Shortcode
        @test shortcode(parse(Embed16Outer, "R:P0042/7")) == "R:P0042/7"
        # Comparison
        a = parse(Embed16Outer, "R:P0001/1")
        b = parse(Embed16Outer, "R:P0002/1")
        c = parse(Embed16Outer, "R:P0002/2")
        @test a < b
        @test b < c
        @test sort([c, a, b]) == [a, b, c]
        # Errors
        @test tryparse(Embed16Outer, "R:P10000/1") === nothing  # inner max 9999
        @test tryparse(Embed16Outer, "R:Q0001/1") === nothing  # wrong inner prefix
        @test tryparse(Embed16Outer, "R:P0001") === nothing  # missing separator+tag
        # Round-trips
        check_roundtrips(Embed16Outer, ("R:P0000/0", "R:P9999/99", "R:P0042/7"))
        @test_neverthrow parsebytes(Embed16Outer, ::Vector{UInt8})
    end
    @testset "multiple adjacent embeds" begin
        iddef = :(@defid MultiEmbed (:a(embed(Emb16)), "-", :b(embed(Emb8))))
        @test parsebytes_complexity(iddef) == (branches=4:5, branch_total=5, ops=20:20)
        eval(iddef)
        @test sizeof(MultiEmbed) >= 3
        # Parsing
        id = parse(MultiEmbed, "P1234-X99")
        @test id.a isa Emb16
        @test id.b isa Emb8
        @test id.a.id == 1234
        @test id.b.id == 99
        # All-zero
        id0 = parse(MultiEmbed, "P0000-X0")
        @test id0.a.id == 0
        @test id0.b.id == 0
        # All-max
        idmax = parse(MultiEmbed, "P9999-X255")
        @test idmax.a.id == 9999
        @test idmax.b.id == 255
        # Properties
        @test propertynames(parse(MultiEmbed, "P0001-X1")) == (:a, :b)
        # Shortcode
        @test shortcode(parse(MultiEmbed, "P0042-X7")) == "P0042-X7"
        # Equality
        @test parse(MultiEmbed, "P1-X2") == parse(MultiEmbed, "P0001-X2")
        @test parse(MultiEmbed, "P1-X2") != parse(MultiEmbed, "P1-X3")
        @test hash(parse(MultiEmbed, "P1-X2")) == hash(parse(MultiEmbed, "P0001-X2"))
        # Errors
        @test tryparse(MultiEmbed, "") === nothing
        @test tryparse(MultiEmbed, "P0001") === nothing  # missing second embed
        @test tryparse(MultiEmbed, "P0001-Y1") === nothing  # wrong prefix on second
        @test tryparse(MultiEmbed, "P10000-X1") === nothing  # first exceeds max
        # Round-trips
        check_roundtrips(MultiEmbed, ("P0000-X0", "P9999-X255", "P0042-X128"))
        @test_neverthrow parsebytes(MultiEmbed, ::Vector{UInt8})
    end
    @testset "three adjacent embeds (tiny + 16 + 8)" begin
        iddef = :(@defid TripleEmbed (:x(embed(EmbTiny)), ".", :y(embed(Emb16)), ".", :z(embed(Emb8))))
        @test parsebytes_complexity(iddef) == (branches=6:7, branch_total=7, ops=29:29)
        eval(iddef)
        # Parsing
        id = parse(TripleEmbed, "3.P5000.X200")
        @test id.x isa EmbTiny
        @test id.y isa Emb16
        @test id.z isa Emb8
        @test id.x.id == 3
        @test id.y.id == 5000
        @test id.z.id == 200
        # Shortcode
        @test shortcode(parse(TripleEmbed, "0.P0000.X0")) == "0.P0000.X0"
        # Edge: all max
        idmax = parse(TripleEmbed, "3.P9999.X255")
        @test idmax.x.id == 3
        @test idmax.y.id == 9999
        @test idmax.z.id == 255
        # Round-trips
        check_roundtrips(TripleEmbed, ("0.P0000.X0", "3.P9999.X255", "2.P0042.X128"))
        @test_neverthrow parsebytes(TripleEmbed, ::Vector{UInt8})
    end
    @testset "embed with optional" begin
        iddef = :(@defid EmbedOpt (:main(embed(Emb16)),
                   optional("-", :extra(embed(Emb8)))))
        @test parsebytes_complexity(iddef) == (branches=4:6, branch_total=6, ops=11:29)
        eval(iddef)
        # Present
        id = parse(EmbedOpt, "P1234-X42")
        @test id.main isa Emb16
        @test id.main.id == 1234
        @test id.extra isa Emb8
        @test id.extra.id == 42
        # Absent
        id2 = parse(EmbedOpt, "P1234")
        @test id2.main.id == 1234
        @test id2.extra === nothing
        # Distinct
        @test parse(EmbedOpt, "P1234-X42") != parse(EmbedOpt, "P1234")
        # Round-trips
        check_roundtrips(EmbedOpt, ("P0000", "P9999", "P0042-X0", "P0042-X255"))
        @test_neverthrow parsebytes(EmbedOpt, ::Vector{UInt8})
    end
    @testset "constructor" begin
        # Single embed
        @test EmbedTinyOuter(parse(EmbTiny, "2"), 50) == parse(EmbedTinyOuter, "T-2-50")
        @test EmbedTinyOuter(parse(EmbTiny, "2"), 50).inner == parse(EmbTiny, "2")
        @test EmbedTinyOuter(parse(EmbTiny, "2"), 50).extra == 50
        # Multi embed
        @test MultiEmbed(parse(Emb16, "P0042"), parse(Emb8, "X7")) ==
              parse(MultiEmbed, "P0042-X7")
        # Constructor round-trip via properties
        for input in ("T-0-0", "T-3-99", "T-1-50")
            id = parse(EmbedTinyOuter, input)
            @test EmbedTinyOuter(id.inner, id.extra) == id
        end
        for input in ("P0000-X0", "P9999-X255")
            id = parse(MultiEmbed, input)
            @test MultiEmbed(id.a, id.b) == id
        end
    end
    @testset "show form" begin
        id = parse(Embed8Outer, "E-X42-7")
        shown = sprint(show, id)
        @test startswith(shown, "Embed8Outer(")
        @test endswith(shown, ")")
        # Inner value should appear in show output
        @test occursin("Emb8", shown) || occursin("42", shown)
        # eval roundtrip
        @test eval(Meta.parse(repr(id))) == id
    end
    @testset "error: non-primitive type" begin
        # Struct (non-primitive) identifiers cannot be embedded
        err = try eval(:(@defid BadEmbed :x(embed(AbstractIdentifier)))); nothing
              catch e; e end
        @test err isa LoadError && err.error isa ArgumentError
    end
end # embed

@testset "PURL generation" begin
    @testset "WithPrefix" begin
        iddef = :(@defid WithPrefix ("WP-", :id(digits(max=9999))) purlprefix="https://example.com/wp/")
        @test parsebytes_complexity(iddef) == (branches=5:9, branch_total=9, ops=38:47)
        eval(iddef)
        # purlprefix method
        @test purlprefix(WithPrefix) == "https://example.com/wp/"
        # purl concatenates prefix + shortcode
        id = parse(WithPrefix, "WP-42")
        @test purl(id) == "https://example.com/wp/" * shortcode(id)
        # print uses PURL when no :limit
        @test sprint(print, id) == purl(id)
        # No prefix → purl returns nothing
        @test purl(parse(SimpleNum, "SN1")) === nothing
        # Round-trips
        check_roundtrips(WithPrefix, ("WP-0", "WP-9999"))
        @test_neverthrow parsebytes(WithPrefix, ::Vector{UInt8})
    end
end # PURL generation

@testset "Case folding" begin
    iddef = :(@defid CaseFolded ("Pfx:", :id(digits(max=999))))
    @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=36:36)
    eval(iddef)
    iddef = :(@defid CaseSensitive ("Pfx:", :id(digits(max=999))) casefold=false)
    @test parsebytes_complexity(iddef) == (branches=3:3, branch_total=3, ops=35:35)
    eval(iddef)
    @testset "Default: case-insensitive literals" begin
        a = parse(CaseFolded, "Pfx:42")
        b = parse(CaseFolded, "PFX:42")
        c = parse(CaseFolded, "pfx:42")
        @test a == b == c
    end
    @testset "casefold=false: case-sensitive literals" begin
        @test parse(CaseSensitive, "Pfx:42") isa CaseSensitive
        @test tryparse(CaseSensitive, "PFX:42") === nothing
        @test tryparse(CaseSensitive, "pfx:42") === nothing
    end
    @test_neverthrow parsebytes(CaseFolded, ::Vector{UInt8})
    @test_neverthrow parsebytes(CaseSensitive, ::Vector{UInt8})
end

@testset "Output formatting" begin
    id = parse(SimpleNum, "SN42")
    @testset "print (default context)" begin
        @test sprint(print, id) == shortcode(id)
    end
    @testset "show (reconstructable form)" begin
        shown = sprint(show, id)
        @test occursin("SimpleNum", shown)
        @test occursin("parse", shown) || occursin("SimpleNum(", shown)
    end
    @testset "show with :limit" begin
        limited = sprint(show, id; context=IOContext(stdout, :limit => true))
        @test occursin("SimpleNum", limited)
    end
    @testset "show with :typeinfo suppresses type name" begin
        ctx = IOContext(stdout, :limit => true, :typeinfo => SimpleNum)
        typed = sprint(show, id; context=ctx)
        @test !startswith(typed, "SimpleNum")
    end
    @testset "print with :limit" begin
        ctx = IOContext(stdout, :limit => true)
        limited = sprint(print, id; context=ctx)
        @test occursin("SimpleNum", limited)
        @test occursin("0042", limited)
    end
    @testset "print with :limit + :compact omits type" begin
        ctx = IOContext(stdout, :limit => true, :compact => true)
        compact = sprint(print, id; context=ctx)
        @test !startswith(compact, "SimpleNum:")
    end
end

@testset "show constructor form" begin
    @testset "Simple digits" begin
        id = parse(SimpleNum, "SN42")
        @test sprint(show, id) == "SimpleNum(42)"
    end
    @testset "Multi-field" begin
        id = parse(LargeId, "100-200")
        shown = sprint(show, id)
        @test startswith(shown, "LargeId(")
        @test endswith(shown, ")")
        # Roundtrip via eval
        id2 = eval(Meta.parse(shown))
        @test id == id2
    end
    @testset "Optional (present)" begin
        id = parse(WithOptional, "42.v3")
        shown = sprint(show, id)
        @test startswith(shown, "WithOptional(")
        @test endswith(shown, ")")
        @test !occursin("nothing", shown)
    end
    @testset "Optional (absent)" begin
        id = parse(WithOptional, "42")
        shown = sprint(show, id)
        @test occursin("nothing", shown)
        @test startswith(shown, "WithOptional(")
    end
    @testset "Nested optional" begin
        id = parse(DoubleOptional, "100.v2.p500")
        shown = sprint(show, id)
        @test startswith(shown, "DoubleOptional(")
        id2 = parse(DoubleOptional, "100")
        shown2 = sprint(show, id2)
        @test count("nothing", shown2) == 2
    end
    @testset "Choice" begin
        id = parse(ChoiceField, "B-99")
        @test sprint(show, id) == "ChoiceField(:B, 99)"
    end
    @testset "Charseq" begin
        id = parse(LettersFolded, "R-HSA-42")
        shown = sprint(show, id)
        @test startswith(shown, "LettersFolded(")
        @test occursin("\"HSA\"", shown)
    end
    @testset "Multi-node field" begin
        id = parse(MultiFieldProp, "v3.7")
        shown = sprint(show, id)
        @test startswith(shown, "MultiFieldProp(")
        @test occursin("3", shown) && occursin("7", shown)
    end
    @testset "eval roundtrip" begin
        # Verify that repr output is eval-roundtrippable for all types with constructors
        for (T, input) in [
            (SimpleNum, "SN42"),
            (ChoiceField, "B-99"),
            (WithOptional, "42.v3"),
            (WithOptional, "42"),
            (DoubleOptional, "100.v2.p500"),
            (DoubleOptional, "100"),
        ]
            id = parse(T, input)
            @test eval(Meta.parse(repr(id))) == id
        end
    end
end

@testset "Equality and hashing" begin
    @testset "Usable as Dict keys" begin
        d = Dict{SimpleNum, Int}()
        id = parse(SimpleNum, "SN5")
        d[id] = 1
        @test d[parse(SimpleNum, "SN5")] == 1
    end
    @testset "Usable in Sets" begin
        s = Set{WithOptional}()
        push!(s, parse(WithOptional, "1"))
        push!(s, parse(WithOptional, "1.v0"))
        push!(s, parse(WithOptional, "1"))  # duplicate
        @test length(s) == 2
    end
end

@testset "constructor" begin
    @testset "Simple digits" begin
        @test SimpleNum(42) == parse(SimpleNum, "SN42")
        @test SimpleNum(42).id == 42
        @test SimpleNum(0).id == 0
        @test SimpleNum(9999).id == 9999
        @test shortcode(SimpleNum(42)) == "SN0042"
        @test_throws ArgumentError SimpleNum(10000)
        @test_throws ArgumentError SimpleNum(-1)
    end
    @testset "Ranged digits" begin
        @test Ranged(100).id == 100
        @test Ranged(255).id == 255
        @test_throws ArgumentError Ranged(99)
        @test_throws ArgumentError Ranged(256)
    end
    @testset "Multi-field digits" begin
        @test LargeId(100, 200) == parse(LargeId, "100-200")
        @test LargeId(100, 200).a == 100
        @test LargeId(100, 200).b == 200
        @test Compound(3, 14) == parse(Compound, "ID:3.14")
        @test Compound(3, 14).major == 3
        @test Compound(3, 14).minor == 14
    end
    @testset "Multi-node field" begin
        id = MultiFieldProp(3, 7)
        @test id.compound == "v3.7"
        @test id == parse(MultiFieldProp, "v3.7")
    end
    @testset "Choice" begin
        @test ChoiceField(:B, 99) == parse(ChoiceField, "B-99")
        @test ChoiceField(:A, 1).kind == :A
        @test ChoiceField(:C, 0).kind == :C
        @test_throws ArgumentError ChoiceField(:D, 99)
        @test_throws ArgumentError ChoiceField(:Z, 0)
    end
    @testset "Optional" begin
        @test WithOptional(42, 3) == parse(WithOptional, "42.v3")
        @test WithOptional(42, nothing) == parse(WithOptional, "42")
        @test WithOptional(42, 3).version == 3
        @test WithOptional(42, nothing).version === nothing
        @test_throws ArgumentError WithOptional(42, 256)
    end
    @testset "Nested optional" begin
        @test DoubleOptional(100, 2, 500) == parse(DoubleOptional, "100.v2.p500")
        @test DoubleOptional(100, 2, nothing) == parse(DoubleOptional, "100.v2")
        @test DoubleOptional(100, nothing, nothing) == parse(DoubleOptional, "100")
        @test DoubleOptional(100, 2, 500).version == 2
        @test DoubleOptional(100, 2, 500).patch == 500
        @test DoubleOptional(100, nothing, nothing).version === nothing
        @test DoubleOptional(100, nothing, nothing).patch === nothing
        @test_throws ArgumentError DoubleOptional(100, nothing, 500)
    end
    @testset "Charseq" begin
        @test LettersFolded("HSA", 42) == parse(LettersFolded, "R-HSA-42")
        @test LettersFolded("HSA", 42).code == "HSA"
        @test LettersFolded("hsa", 42) == LettersFolded("HSA", 42)  # casefold
        @test_throws ArgumentError LettersFolded("H1A", 42)  # invalid char
        @test_throws ArgumentError LettersFolded("HS", 42)   # too short
    end
    @testset "Optional charseq" begin
        @test OptLettersFixed(42, "AB") == parse(OptLettersFixed, "42-AB")
        @test OptLettersFixed(42, nothing) == parse(OptLettersFixed, "42")
        @test OptLettersFixed(42, "AB").suffix == "AB"
        @test OptLettersFixed(42, nothing).suffix === nothing
        @test_throws ArgumentError OptLettersFixed(42, "A")   # too short
        @test_throws ArgumentError OptLettersFixed(42, "ABC") # too long
    end
    @testset "Round-trip invariant" begin
        # For types with single-node fields, T(fields...) should round-trip
        for (T, inputs) in [
            (SimpleNum, ("SN42", "SN0", "SN9999")),
            (Ranged, ("100", "200", "255")),
            (LargeId, ("100-200", "0-0", "65535-65535")),
            (Compound, ("ID:3.14", "ID:0.0", "ID:99.99")),
            (ChoiceField, ("A-0", "B-999", "C-42")),
            (LettersFolded, ("R-HSA-42", "R-ABC-0")),
        ]
            for input in inputs
                id = parse(T, input)
                props = map(p -> getproperty(id, p), propertynames(id))
                @test T(props...) == id
            end
        end
        # Multi-node field: constructor takes individual components, not the combined string
        for (v1, v2) in ((3, 7), (0, 0), (9, 9))
            @test parse(MultiFieldProp, shortcode(MultiFieldProp(v1, v2))) == MultiFieldProp(v1, v2)
        end
        # Optional types: explicit round-trip through properties
        for input in ("42.v3", "42")
            id = parse(WithOptional, input)
            @test WithOptional(id.id, id.version) == id
        end
        for input in ("100.v2.p500", "100.v2", "100")
            id = parse(DoubleOptional, input)
            @test DoubleOptional(id.id, id.version, id.patch) == id
        end
        for input in ("42-AB", "42")
            id = parse(OptLettersFixed, input)
            @test OptLettersFixed(id.id, id.suffix) == id
        end
    end
end

@testset "checkdigit" begin
    @testset "TestEAN13 (decimal check digit, mod10)" begin
        eval(:(@defid TestEAN13 (:code(digits(12:12, pad=12)),
               checkdigit(:code, mod10))))
        # Successful parse: 4006381333931 → check digit 1
        id = parse(TestEAN13, "4006381333931")
        @test id isa TestEAN13
        @test id.code == 400638133393
        @test idchecksum(id) == 1
        @test idcode(id) == 400638133393
        # Shortcode includes computed check digit
        @test shortcode(id) == "4006381333931"
        # Round-trip
        @test parse(TestEAN13, shortcode(id)) == id
        check_roundtrips(TestEAN13, ("4006381333931", "0000000000000", "5901234123457"))
        # ChecksumViolation on wrong check digit
        @test_throws ChecksumViolation parse(TestEAN13, "4006381333932")
        err = try parse(TestEAN13, "4006381333932"); nothing catch e; e end
        @test err isa ChecksumViolation{TestEAN13}
        @test err.expected == 1
        @test err.provided == 2
        # tryparse returns nothing on checksum violation
        @test tryparse(TestEAN13, "4006381333932") === nothing
        # Trailing content after valid checkdigit
        @test_throws MalformedIdentifier parse(TestEAN13, "40063813339310")
        # Structural errors take precedence over checksum errors
        @test_throws MalformedIdentifier parse(TestEAN13, "40063813339")  # too short
        @test_throws MalformedIdentifier parse(TestEAN13, "400638133393X")  # invalid digit
        # Invalid check character → MalformedIdentifier
        @test_throws MalformedIdentifier parse(TestEAN13, "40063813339A")
        # Constructor omits check digit argument
        @test TestEAN13(400638133393) == id
        @test shortcode(TestEAN13(400638133393)) == "4006381333931"
        # show uses constructor form without check digit
        shown = sprint(show, id)
        @test startswith(shown, "TestEAN13(")
        @test endswith(shown, ")")
        @test !occursin("checkdigit", shown)
        @test_neverthrow parsebytes(TestEAN13, ::Vector{UInt8})
    end
    @testset "TestMod11 (non-decimal check char, mod11_2)" begin
        eval(:(@defid TestMod11 (:code(digits(7:7, pad=7)),
               checkdigit(:code, mod11_2))))
        # mod11_2(1000002) = 1
        id = parse(TestMod11, "10000021")
        @test id isa TestMod11
        @test id.code == 1000002
        @test idchecksum(id) == 1
        # mod11_2(1000003) = 10 → 'X'
        idx = parse(TestMod11, "1000003X")
        @test idx isa TestMod11
        @test idchecksum(idx) == 10
        @test shortcode(idx) == "1000003X"
        # Case-insensitive X
        @test parse(TestMod11, "1000003x") == idx
        # Round-trips
        @test parse(TestMod11, shortcode(id)) == id
        @test parse(TestMod11, shortcode(idx)) == idx
        check_roundtrips(TestMod11, ("10000021", "1000003X"))
        # ChecksumViolation
        @test_throws ChecksumViolation parse(TestMod11, "10000022")
        err = try parse(TestMod11, "10000022"); nothing catch e; e end
        @test err isa ChecksumViolation{TestMod11}
        @test err.expected == 1
        @test err.provided == 2
        @test tryparse(TestMod11, "10000022") === nothing
        # Structural errors take precedence
        @test_throws MalformedIdentifier parse(TestMod11, "100000")  # too short
        # Invalid check character
        @test_throws MalformedIdentifier parse(TestMod11, "1000002Z")
        # Constructor omits check digit
        @test TestMod11(1000002) == id
        @test_neverthrow parsebytes(TestMod11, ::Vector{UInt8})
    end
    @testset "Non-terminal checkdigit (followed by literal)" begin
        eval(:(@defid CheckThenLit (:code(digits(4:4, pad=4)),
               checkdigit(:code, mod10), "-end")))
        # mod10(1234) = 8
        id = parse(CheckThenLit, "12348-end")
        @test id isa CheckThenLit
        @test id.code == 1234
        @test idchecksum(id) == 8
        @test shortcode(id) == "12348-end"
        @test parse(CheckThenLit, shortcode(id)) == id
        # Checksum violation with trailing literal present
        @test_throws ChecksumViolation parse(CheckThenLit, "12345-end")
        @test tryparse(CheckThenLit, "12345-end") === nothing
        # Missing trailing literal
        @test tryparse(CheckThenLit, "12348") === nothing
        @test tryparse(CheckThenLit, "12348-") === nothing
        @test_neverthrow parsebytes(CheckThenLit, ::Vector{UInt8})
    end
    @testset "Checkdigit with skip separator" begin
        eval(:(@defid CheckWithSkip (:code(digits(4:4, pad=4)),
               skip(print="-"), checkdigit(:code, mod10))))
        # mod10(1234) = 8
        id = parse(CheckWithSkip, "1234-8")
        @test id isa CheckWithSkip
        @test id.code == 1234
        @test shortcode(id) == "1234-8"
        @test parse(CheckWithSkip, "12348") == id  # without separator
        check_roundtrips(CheckWithSkip, ("1234-8", "0000-0"))
        @test_throws ChecksumViolation parse(CheckWithSkip, "1234-5")
        @test tryparse(CheckWithSkip, "1234-5") === nothing
        @test_neverthrow parsebytes(CheckWithSkip, ::Vector{UInt8})
    end
end # checkdigit

# end # @testset "@defid"
