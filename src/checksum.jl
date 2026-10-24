# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Checkdigit segment handler and standard checksum functions.
#
# The checkdigit segment validates a single check character derived from
# a previously captured field. Zero bits are stored — the check digit is
# recomputed from the field value on print.

## Checkdigit handler

function compile_checkdigit(state::ParserState, nctx::NodeCtx,
                            exprs::PatternExprs,
                            ::SegmentDef, args::Vector{Any})
    !isnothing(get(nctx, :optional, nothing)) &&
        throw(ArgumentError("checkdigit cannot appear inside optional(...)"))
    any(p -> first(p) === :checkdigit, state.segment_outputs) &&
        throw(ArgumentError("Only one checkdigit per type is allowed"))
    length(args) == 2 || throw(ArgumentError(
        "checkdigit requires exactly 2 positional arguments: (:field, fn), got $(length(args))"))
    fieldname_node, fn_expr = args
    fieldname_node isa QuoteNode || throw(ArgumentError(
        "First argument to checkdigit must be a quoted field name, got $fieldname_node"))
    fieldname = fieldname_node.value::Symbol
    # Resolve the referenced field's segment
    prop_idx = findfirst(p -> first(p) == fieldname, exprs.properties)
    isnothing(prop_idx) && throw(ArgumentError(
        "checkdigit references unknown field :$fieldname"))
    prop_val = last(exprs.properties[prop_idx])
    prop_val isa Symbol || throw(ArgumentError(
        "checkdigit field :$fieldname must be a single-segment property"))
    seg_idx = findfirst(s -> s.label == prop_val, exprs.segments)
    isnothing(seg_idx) && throw(ArgumentError(
        "checkdigit field :$fieldname has no matching segment"))
    # Resolve checksum function and codegen reference
    builtin = fn_expr isa Symbol && isdefined(Checksums, fn_expr)
    fn = if builtin getfield(Checksums, fn_expr) else Core.eval(state.mod, fn_expr) end
    fnref = if builtin GlobalRef(Checksums, fn_expr) else esc(fn_expr) end
    n = Checksums.nbytes(fn)
    checkbytes = ntuple(i -> gensym("checkbyte$i"), n)
    # Literal symbols for identifier_parse context (bound in the generated parse function)
    report_bytes = ntuple(i -> Symbol("checkbyte$i"), n)
    checksum_info = ChecksumInfo(fnref, seg_idx, n,
                                  Checksums.parse_bytes(fn, report_bytes, nctx))
    # Parse codegen
    checkpos = gensym("checkpos")
    checkval = gensym("checkval")
    ok_sym = gensym("checksum_ok")
    notfound = build_fail_expr!(state, nctx, "Invalid check character")
    lencheck = emit_lengthcheck(state, nctx, n)
    seg = exprs.segments[seg_idx]
    extract_copy = map(copy, seg.extract)
    parse_exprs = ExprVarLine[
          :($checkpos = pos),
          :(if !$lencheck; $notfound end)]
    for (i, bvar) in enumerate(checkbytes)
        push!(parse_exprs, :($bvar = @inbounds data[pos + $(i - 1)]))
    end
    expected = gensym("expected")
    lanecheck = gen_lane_check(state, fn, fnref, prop_val, expected)
    append!(parse_exprs, ExprVarLine[
          :($checkval = $(Checksums.parse_bytes(fn, checkbytes, nctx))),
          :(if $checkval < 0; $notfound end),
          lanecheck...,
          :(if $(if isempty(lanecheck) true else :($expected < 0) end)
                val = parsed
                $(extract_copy[1:end-1]...)
                $expected = $fnref($(last(extract_copy)))
            end),
          :(pos += $n),
          :($ok_sym = ($checkval == $expected)),
          Expr(:call, :__checksum_gate, ok_sym, checkpos)])
    # Print codegen
    seg_print_extract = map(copy, seg.extract)
    getval = ExprVarLine[seg_print_extract[1:end-1]...]
    print_exprs = ExprVarLine[Checksums.print_bytes(fn, :($fnref($(last(seg_print_extract)))), nctx)...]
    valid = Checksums.valid_bytes(fn, nctx)
    SegmentOutput(
        SegmentBounds(n:n, n:n, 0, nothing),
        SegmentCodegen(parse_exprs, ExprVarLine[],
            PrintExprs(direct = ExprVarLine[getval..., print_exprs...],
                       getval = getval, getlen = ExprVarLine[:(pos += $n)],
                       putval = print_exprs),
            Expr[]),
        SegmentMeta(:checkdigit, "check digit", "check", nothing, nothing, checksum_info),
        [fill(valid, n)])
end

# Set `expected` to the check value from the digits before `pos` (or -1), when `fn` is a
# weighted digit sum and they match the field's canonical layout: holding as many digits
# as the field, they are then its digits, however it parsed
function gen_lane_check(state::ParserState, fn, fnref, label::Symbol, expected::Symbol)
    at = something(findlast(((_, o),) -> o.meta.label == label, state.segment_outputs), 0)
    layout = if at > 0 last(state.segment_outputs[at]).meta.context end
    layout isa Vector{ByteSet} || return ExprVarLine[]
    # Only skips may follow it, of bytes no lane takes, which then fail the lanes' check
    for (kind, output) in state.segment_outputs[at+1:end]
        kind === :skip || return ExprVarLine[]
        for alt in output.bytespans, b in alt; isdisjoint(b, reduce(∪, layout)) || return ExprVarLine[] end
    end
    digit_set, k, weights = ByteSet(UInt8('0'):UInt8('9')), 0, Int[]
    for lane in Iterators.reverse(layout)  # A digit's weight, or a separator's -1
        w = if lane == digit_set; k += 1; Checksums.digitweight(fn, k - 1) elseif length(lane) == 1; -1 end
        isnothing(w) && return ExprVarLine[]
        pushfirst!(weights, w)
    end
    # Registers ending at `pos`, the first reaching back `pad` bytes before the field; each
    # byte's digit and separator masks, separator, and weight
    width = length(layout); pad = 8 * cld(width, 8) - width
    digitmask, sepmask, sepval, weight = zeros(UInt64, width + pad), zeros(UInt64, width + pad), zeros(UInt64, width + pad), zeros(UInt64, width + pad)
    for i in 1:width
        if weights[i] >= 0; digitmask[pad+i], weight[pad+i] = 0xff, weights[i]
        else sepmask[pad+i], sepval[pad+i] = 0xff, first(layout[i]) end
    end
    lanes(v::Vector{UInt64}, r::Int) = (x = zero(UInt64); for j in 0:7; x |= v[8r + j + 1] << 8j; end; x)
    # Σ lane × weight lands in the top 16-bit lane when the lanes' weights are mirrored
    dot(r::Int, odd::Int) = (x = zero(UInt64); for j in 0:3; x |= weight[8r + 2j + odd + 1] << (16 * (3 - j)); end; x)
    loads, bad, sum = ExprVarLine[], Expr[], Expr[]
    for r in 0:cld(width, 8)-1
        x = gensym("lanes")
        push!(loads, :($x = htol(Base.unsafe_load(Ptr{UInt64}(pointer(data, pos - $(8 * cld(width, 8) - 8r)))))))
        digits, seps, sepvals = lanes(digitmask, r), lanes(sepmask, r), lanes(sepval, r)
        # A digit lane's top nibble is 3 both before and after adding 6
        push!(bad, :(((($x & ($x + 0x0606060606060606)) & 0xf0f0f0f0f0f0f0f0) ⊻ 0x3030303030303030) & $digits |
                     ($x ⊻ $sepvals) & $seps))
        push!(sum, :(Int(((($x & 0x000f000f000f000f) * $(dot(r, 0))) >> 48) + (((($x >> 8) & 0x000f000f000f000f) * $(dot(r, 1))) >> 48))))
    end
    ExprVarLine[:($expected = -1),
                :(if pos > $width && canreadback(data, pos - $width, $pad)
                      $(loads...)
                      iszero($(Expr(:call, :|, bad...))) &&
                          ($expected = $(GlobalRef(Checksums, :checkfromsum))($fnref, $(Expr(:call, :+, sum...))))
                  end)]
end

## Checkdigit finalize hook

"""
    finalize_checkdigit!(block, exprs, state, name)

Post-assembly finalize hook for the checkdigit segment.

Generates `idchecksum` and `idcode` methods, and patches `parse`/`tryparse`
to handle checksum violations (negative pos from `__checksum_gate`).
"""
function finalize_checkdigit!(hookdata::Vector{Expr}, exprs::PatternExprs,
                              state::ParserState, name::Symbol)
    idx = findfirst(p -> first(p) === :checkdigit, state.segment_outputs)
    isnothing(idx) && return
    output = last(state.segment_outputs[idx])
    info = output.meta.context::ChecksumInfo
    (; fn, field_seg_idx) = info
    seg = exprs.segments[field_seg_idx]
    # idchecksum: extract the field value, apply the checksum function
    cs_extract = map(copy, seg.extract)
    implement_casting!(state, cs_extract)
    cs_value = last(cs_extract)
    push!(hookdata,
          :(function $(GlobalRef(FastIdentifiers, :idchecksum))(val::$(esc(name)))
                $(cs_extract[1:end-1]...)
                $fn($cs_value)
            end),
          :(function $(GlobalRef(FastIdentifiers, :idcode))(val::$(esc(name)))
                $(cs_extract[1:end-1]...)
                $cs_value
            end))
end

## Checksums module — protocol and standard checksum functions

module Checksums

using ..DefId: NodeCtx, ByteSet

# Checksum functions extend this protocol with methods of their own, and it is
# called on functions whose type inference can't know: analysing those calls
# against the methods seen so far only makes every new checksum invalidate them.
Base.Experimental.@max_methods 1

"""
    parse_byte(fn, bytevar::Symbol, nctx::NodeCtx) -> Expr

Return an expression mapping check byte `bytevar` to a 0-based integer,
or `-1` for invalid bytes. `nctx` carries pattern context (e.g. casefold).

The default handles decimal digits (0–9).
"""
parse_byte(fn, bytevar::Symbol, ::NodeCtx) =
    :(ifelse($bytevar - 0x30 < 0x0a, Int($bytevar - 0x30), -1))
valid_bytes(fn, ::NodeCtx) = ByteSet(UInt8('0'):UInt8('9'))

"""
    print_byte(fn, valexpr, nctx::NodeCtx) -> Expr

Return an expression mapping checksum integer `valexpr` to a `UInt8` byte.

The default handles decimal digits (0–9).
"""
print_byte(fn, valexpr, ::NodeCtx) =
    :(UInt8($valexpr) + 0x30)

## Weighted digit sums

# The digits of `n < 10^8` in 16-bit lanes: digits 0, 2, 4, 6 (from the right) and 1, 3, 5, 7
@inline function digitlanes(n::UInt64)
    hi = n ÷ 10000
    halves = (n - 10000hi) | hi << 32
    hundreds = ((halves * 5243) >> 19) & 0x0000007f_0000007f  # ÷100 per lane
    pairs = (halves - 100hundreds) | hundreds << 16
    tens = ((pairs * 103) >> 10) & 0x000f_000f_000f_000f      # ÷10 per lane
    pairs - 10tens, tens
end

# Σ lane_k × weight_k, with lane k's weight in lane 3 - k
@inline lanedot(lanes::UInt64, weights::UInt64) = Int((lanes * weights) >> 48)

@inline function chunks8(code::Integer)
    u = UInt64(code)
    rest = u ÷ 100_000_000
    u - 100_000_000rest, rest % 100_000_000, rest ÷ 100_000_000
end

"""
    mod10(code::Integer) -> Int

Weighted mod-10 checksum (EAN-13/UPC) of a `code` in `0:typemax(UInt64)`.

Alternates weights 3 and 1 across digits from right to left,
returns `(10 - sum % 10) % 10`.
"""
function mod10(code::Integer)
    sum10(c) = ((even, odd) = digitlanes(c); lanedot(3even + odd, 0x0001_0001_0001_0001))
    c0, c1, c2 = chunks8(code)
    (10 - (sum10(c0) + sum10(c1) + sum10(c2)) % 10) % 10
end

"""
    mod11_2(code::Integer) -> Int

ISO 7064 MOD 11-2 checksum (ORCID, ISNI) of a `code` in `0:typemax(UInt64)`.

Processes digits left to right: `r = (r + digit) * 2 mod 11`.
Returns `(12 - r) mod 11`, yielding 0–10 (10 maps to 'X' via `print_byte`).
"""
function mod11_2(code::Integer)
    # Digit k from the right weighs 2^(k+1) mod 11, so each 8-digit chunk a further 2^8 ≡ 3
    sum11(c) = ((even, odd) = digitlanes(c);
                lanedot(even, 0x0002_0008_000a_0007) + lanedot(odd, 0x0004_0005_0009_0003))
    c0, c1, c2 = chunks8(code)
    (12 - (sum11(c0) + 3sum11(c1) + 9sum11(c2)) % 11) % 11
end
parse_byte(::typeof(mod11_2), bytevar::Symbol, ::NodeCtx) =
    :(if $bytevar - 0x30 < 0x0a; Int($bytevar - 0x30)
      elseif ($bytevar | 0x20) == $(UInt8('x')); 10
      else -1 end)
valid_bytes(::typeof(mod11_2), ::NodeCtx) =
    ByteSet(UInt8('0'):UInt8('9'), UInt8('X'), UInt8('x'))
print_byte(::typeof(mod11_2), valexpr, ::NodeCtx) =
    :(ifelse($valexpr < 10, UInt8($valexpr) + 0x30, $(UInt8('X'))))

"""
    mod97(code::Integer) -> Int

ISO 7064 MOD 97-10 checksum (ROR).

The check value satisfies `code * 100 + check ≡ 1 (mod 97)`.
Returns `98 - (code * 100) % 97`, yielding 2–98 as a two-digit decimal.
"""
mod97(code::Integer) = 98 - (code * 100) % 97

## Weighted digit sums

"""
    digitweight(fn, k) -> Union{Int, Nothing}
    checkfromsum(fn, sum::Int) -> Int

For a check `fn` computed from a weighted sum of a code's decimal digits, the weight of
the digit `k` places from the right (from 0, in `0:255`), and the check from that sum.
Parsing then computes it from the digits as read. `digitweight` is otherwise `nothing`.
"""
digitweight(fn, k::Int) = nothing
digitweight(::typeof(mod11_2), k::Int) = powermod(2, k + 1, 11)
checkfromsum(::typeof(mod11_2), sum::Int) = (12 - sum % 11) % 11
digitweight(::typeof(mod10), k::Int) = if iseven(k); 3 else 1 end
checkfromsum(::typeof(mod10), sum::Int) = (10 - sum % 10) % 10

## Multi-byte protocol

"""
    nbytes(fn) -> Int

Number of check bytes for checksum function `fn`. Default is 1.
Override for multi-byte checksums (e.g. `mod97` uses 2 digits).
"""
nbytes(fn) = 1
nbytes(::typeof(mod97)) = 2

"""
    parse_bytes(fn, bytevars::NTuple{N, Symbol}, nctx) -> Expr

Map multiple check bytes to a single integer value, or `-1` for invalid.
Default defers to `parse_byte` for single-byte checksums.
"""
function parse_bytes(fn, bytevars::NTuple{1, Symbol}, nctx::NodeCtx)
    parse_byte(fn, first(bytevars), nctx)
end
function parse_bytes(::typeof(mod97), bytevars::NTuple{2, Symbol}, ::NodeCtx)
    b1, b2 = bytevars
    :(if $b1 - 0x30 < 0x0a && $b2 - 0x30 < 0x0a
          Int($b1 - 0x30) * 10 + Int($b2 - 0x30)
      else -1 end)
end

"""
    print_bytes(fn, valexpr, nctx) -> Vector{Expr}

Emit expressions writing the check value as bytes.
Default defers to `print_byte` for single-byte checksums.
"""
function print_bytes(fn, valexpr, nctx::NodeCtx)
    [:(write(io, $(print_byte(fn, valexpr, nctx))))]
end
function print_bytes(::typeof(mod97), valexpr, ::NodeCtx)
    [:(write(io, UInt8(($valexpr) ÷ 10) + 0x30)),
     :(write(io, UInt8(($valexpr) % 10) + 0x30))]
end

valid_bytes(::typeof(mod97), ::NodeCtx) = ByteSet(UInt8('0'):UInt8('9'))

end # module Checksums

using .Checksums: Checksums
