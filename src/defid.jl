# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module DefId

using FastIdentifiers: FastIdentifiers, AbstractIdentifier, MalformedIdentifier,
    ChecksumViolation, shortcode, idprefix, purlprefix, idchecksum, idcode

using PackedParselets: PackedParselets,
    ExprVarLine, NodeCtx, PatternExprs, ParserState, ByteSet, PrintExprs,
    SegmentOutput, SegmentDef, SegmentBounds, SegmentCodegen, SegmentMeta,
    CORE_SEGMENTS, maketype,
    emit_lengthcheck, build_fail_expr!, implement_casting!

"""
    ChecksumInfo

Resolved checkdigit metadata carried through compilation for downstream
codegen (parse error reporting, idchecksum/idcode generation).
"""
struct ChecksumInfo
    fn::Union{GlobalRef, Expr}
    field_seg_idx::Int
    nbytes::Int
    parse_expr::Expr
end

include("checksum.jl")

## Segment registry

const ID_SEGMENTS = merge(CORE_SEGMENTS, (checkdigit = SegmentDef(:checkdigit, compile_checkdigit, (), finalize_checkdigit!),))

const GLOBAL_KWARGS = (:prefix, :purlprefix)

## Identifier-specific finalization

function identifier_finalize(typeparts::NamedTuple, state::ParserState, name::Symbol)
    shortcode_ref = GlobalRef(FastIdentifiers, :shortcode)
    tobytes_ref = GlobalRef(PackedParselets, :tobytes)
    maxbytes = state.branches[1].print_max
    # Stack-buffer write core: tobytes into a fixed-size buffer, unsafe_write to IO
    writecore = ExprVarLine[
        :(buf = Memory{UInt8}(undef, $maxbytes)),
        :(len = $tobytes_ref(buf, id)),
        :(Base.unsafe_write(io, pointer(buf), len))]
    # Canonical prefix (defaults to purlprefix) and PURL prefix
    prefix = get(state.globals, :prefix, nothing)
    purlprefix = get(state.globals, :purlprefix, nothing)
    prefix = something(prefix, purlprefix, Some(nothing))
    # write = prefix + shortcode content; shortcode = just the content
    # When no prefix, shortcode delegates to write (identical).
    # When prefix, shortcode uses the stack-buffer core directly.
    extra = Expr[identifier_parse(state, name)...]
    # Per-type show only when PackedParselets generated a constructor form
    typeparts.show != :() && push!(extra, build_show(typeparts.show, name, shortcode_ref))
    push!(extra, @static if VERSION >= v"1.12-"
              :($(shortcode_ref)(id::$(esc(name))) = Base.unsafe_takestring($tobytes_ref(id)))
          else
              :($(shortcode_ref)(id::$(esc(name))) = String($tobytes_ref(id)))
          end)
    if isnothing(prefix)
        push!(extra,
              :(function $(GlobalRef(Base, :write))(io::IO, id::$(esc(name)))
                    $(writecore...)
                end),
              :($(shortcode_ref)(io::IO, id::$(esc(name))) =
                    ($(GlobalRef(Base, :write))(io, id); nothing)),
              :($(GlobalRef(Base, :string))(id::$(esc(name))) =
                    $shortcode_ref(id)))
    else
        push!(extra,
              :($(GlobalRef(FastIdentifiers, :idprefix))(::Type{$(esc(name))}) = $prefix),
              :(function $(GlobalRef(Base, :write))(io::IO, id::$(esc(name)))
                    write(io, $prefix)
                    $(writecore...)
                end),
              :(function $(shortcode_ref)(io::IO, id::$(esc(name)))
                    $(writecore...)
                    nothing
                end),
              :($(GlobalRef(Base, :string))(id::$(esc(name))) =
                    $prefix * $shortcode_ref(id)))
    end
    if !isnothing(purlprefix)
        push!(extra, :($(GlobalRef(FastIdentifiers, :purlprefix))(::Type{$(esc(name))}) = $purlprefix))
    end
    extra
end

function build_show(pp_show::Expr, name::Symbol, shortcode_ref::GlobalRef)
    constructor_body = if Meta.isexpr(pp_show, :function)
        body = pp_show.args[2]
        idx = findfirst(a -> Meta.isexpr(a, :if) && length(a.args) >= 3, body.args)
        if !isnothing(idx) body.args[idx].args[3] end
    end
    nonlimit = if !isnothing(constructor_body)
        constructor_body
    else
        Expr(:block,
             :(show(io, $(esc(name)))),
             :(print(io, '(', $shortcode_ref(val), ')')))
    end
    :(function $(GlobalRef(Base, :show))(io::IO, val::$(esc(name)))
          if get(io, :limit, false) === true
              if get(io, :typeinfo, Nothing) != $(esc(name))
                  print(io, $(QuoteNode((esc(name)).args[1])), ':')
              end
              $shortcode_ref(io, val)
          else
              $nonlimit
          end
      end)
end

function identifier_parse(state::ParserState, name::Symbol)
    errmsgs = Tuple(state.errconsts)
    _parsebytes = GlobalRef(PackedParselets, :parsebytes)
    _idchecksum = GlobalRef(FastIdentifiers, :idchecksum)
    checkdigit_output = let idx = findfirst(p -> first(p) === :checkdigit, state.segment_outputs)
        if !isnothing(idx) last(state.segment_outputs[idx]) end
    end
    has_checksum = !isnothing(checkdigit_output)
    parse_body = if has_checksum
        info = checkdigit_output.meta.context::ChecksumInfo
        byte_reads = [:($(Symbol("checkbyte$i")) = @inbounds codeunits(id)[-pos + $(i - 1)])
                      for i in 1:info.nbytes]
        byte_to_val = info.parse_expr
        quote
            result, pos = $_parsebytes($(esc(name)), codeunits(id))
            if result isa $(esc(name))
                if pos < 0
                    $(byte_reads...)
                    provided = $byte_to_val
                    throw(ChecksumViolation{$(esc(name))}(id, -pos, $_idchecksum(result), provided))
                end
                pos > ncodeunits(id) || throw(MalformedIdentifier{$(esc(name))}(id, pos, "Unparsed trailing content"))
                result
            else
                throw(MalformedIdentifier{$(esc(name))}(id, pos, @inbounds $errmsgs[result]))
            end
        end
    else
        quote
            result, pos = $_parsebytes($(esc(name)), codeunits(id))
            if result isa $(esc(name))
                pos > ncodeunits(id) || throw(MalformedIdentifier{$(esc(name))}(id, pos, "Unparsed trailing content"))
                result
            else
                throw(MalformedIdentifier{$(esc(name))}(id, pos, @inbounds $errmsgs[result]))
            end
        end
    end
    tryparse_cond = if has_checksum
        :(result isa $(esc(name)) && pos > 0 && pos > ncodeunits(id))
    else
        :(result isa $(esc(name)) && pos > ncodeunits(id))
    end
    (:(function $(GlobalRef(Base, :parse))(::Type{$(esc(name))}, id::AbstractString)
           $(parse_body.args...)
       end),
     :(function $(GlobalRef(Base, :tryparse))(::Type{$(esc(name))}, id::AbstractString)
           result, pos = $_parsebytes($(esc(name)), codeunits(id))
           if $tryparse_cond
               result
           end
       end))
end

"""
    decompose_purl_prefix(url) -> Vector{Union{String, Expr}}

Decompose a PURL prefix into sequential skip step arguments.
Returns a mix of `String` (single-alternative steps) and
`Expr(:call, :choice, ...)` (multi-alternative steps).

    decompose_purl_prefix("https://example.com/foo/")
    # → [choice("https://", "http://"), "example.com/foo/"]

    decompose_purl_prefix("https://www.example.com/foo/")
    # → [choice("https://", "http://"), choice("www.example.com/foo/", "example.com/foo/")]
"""
function decompose_purl_prefix(url::AbstractString)
    rest = lowercase(url)
    steps = Union{String, Expr}[]
    for scheme in ("https://", "http://")
        startswith(rest, scheme) || continue
        rest = rest[ncodeunits(scheme)+1:end]
        push!(steps, Expr(:call, :choice, "https://", "http://"))
        break
    end
    # Domain+path: single string or choice if www. variant exists
    if startswith(rest, "www.")
        push!(steps, Expr(:call, :choice, rest, rest[5:end]))
    else
        push!(steps, rest)
    end
    steps
end

function resolve_interpolations(mod::Module, @nospecialize(x))
    x isa Expr || return x
    Meta.isexpr(x, :$, 1) && return Core.eval(mod, x.args[1])
    Expr(x.head, (resolve_interpolations(mod, a) for a in x.args)...)
end

"""
    leading_skip_strings(pattern) -> Vector{String}

Collect all string literals from a leading `skip(...)` in `pattern`,
including strings inside `choice(...)` arguments. Returns an empty
vector if the pattern does not start with a skip.
"""
function leading_skip_strings(@nospecialize(pattern))
    head = Meta.isexpr(pattern, :tuple) ? get(pattern.args, 1, nothing) : pattern
    Meta.isexpr(head, :call) && length(head.args) >= 2 &&
        head.args[1] === :skip || return String[]
    strings = String[]
    for arg in @view head.args[2:end]
        if arg isa String
            push!(strings, arg)
        elseif Meta.isexpr(arg, :call) && !isempty(arg.args) && arg.args[1] === :choice
            for a in @view arg.args[2:end]
                a isa String && push!(strings, a)
            end
        end
    end
    strings
end

"""
    expand_macrocall_inbounds!(expr)

Pre-expand `@inbounds expr` macro calls to avoid a Julia <1.12 hygiene
bug where the expansion introduces `local val = expr` whose gensym'd
`val` clashes with function parameters named `val`. Uses a unique local
name to avoid the collision.
"""
function expand_macrocall_inbounds!(ex)
    ex isa Expr || return ex
    for (i, a) in enumerate(ex.args)
        if Meta.isexpr(a, :macrocall) && !isempty(a.args) &&
                a.args[1] === Symbol("@inbounds")
            inner = a.args[end]
            expand_macrocall_inbounds!(inner)
            v = gensym("inbounds")
            ex.args[i] = Expr(:block,
                              Expr(:inbounds, true),
                              Expr(:local, :($v = $inner)),
                              Expr(:inbounds, :pop),
                              v)
        else
            expand_macrocall_inbounds!(a)
        end
    end
    ex
end


"""
    @defid name pattern [kwarg=value...]
    @defid name <: Supertype pattern [kwarg=value...]

Define a bit-packed identifier type `name` with parsing and printing `pattern`.
The optional `<: Supertype` form sets a custom abstract supertype (must be
a subtype of `AbstractIdentifier`; defaults to `AbstractIdentifier`).

The `pattern` is an S-expression describing the identifier structure.
Available constructs:

- `seq(arg1, arg2, ...)`: sequence (implicit default, just write `(arg1, arg2, ...)`)
- `optional(arg1, arg2, ...)`: optional section
- `skip([print=str0], step1, step2, ...)`: sequentially skip optional prefixes (each step is a string or `choice(strings...)`)
- `choice([is=opt0], opt1, opt2, ...)`: choose between literal strings or compound patterns
- `choice(:tag, :a => arm1, :b => arm2, ...)`: tagged choice with named discriminant
- `literal(str)`: required literal string
- `digits([n | min:max], [base=10, min=0, max=base^digits-1, pad=0])`: digit field
- `letters([n | min:max])`, `alphnum([n | min:max])`, `hex([n | min:max])`: character sequences
- `charset([n | min:max], range1, range2, ...[, numeric=true])`: custom character set (ranges are `'a':'z'` or single `'x'`; `numeric=true` returns integer value)
- `embed(Type)`: embed another `@defid` primitive type
- `checkdigit(:field, fn)`: check digit validated against `fn(field_value)`

Use `:field(pattern)` to capture a sub-pattern as a named property.

# Examples

```julia-repl
julia> @defid MyId ("i",
                    skip("-"),
                    :id(digits(6, pad=6)),
                    optional(".v", :version(digits(max=255)),
                             optional(".p", :participants(digits(max=2^16-1)))))

julia> parse(MyId, "i-000473.v2.p10")
MyId:i000473.v2.p10

julia> id = parse(MyId, "i5162.v1")
MyId:i005162.v1

julia> (id.id, id.version, id.participants)
(5162, 1, nothing)
```
"""
macro defid(nameexpr, pattern, args...)
    # Parse `Name` or `Name <: Supertype`
    name, supertype_expr = if Meta.isexpr(nameexpr, :<:, 2)
        nameexpr.args[1]::Symbol, nameexpr.args[2]
    else
        nameexpr::Symbol, AbstractIdentifier
    end
    segments = ID_SEGMENTS
    all_kws = (Iterators.flatten(s.kwargs for s in segments)..., GLOBAL_KWARGS...)
    casefold_val = true
    prefix_val = nothing
    purlprefix_val = nothing
    for arg in args
        Meta.isexpr(arg, :(=), 2) || throw(ArgumentError("Expected keyword arguments of the form key=value, got $arg"))
        kwname, kwval = arg.args
        kwname ∈ all_kws ||
            throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(all_kws, ", "))"))
        kwname === :casefold && (casefold_val = kwval)
        kwname === :prefix && (prefix_val = kwval)
        kwname === :purlprefix && (purlprefix_val = kwval)
    end
    supertype_val = Core.eval(__module__, supertype_expr)
    supertype_val isa Type && supertype_val <: AbstractIdentifier ||
        throw(ArgumentError("Supertype must be a subtype of AbstractIdentifier, got $supertype_expr"))
    # Resolve $-interpolations in the pattern at macro-expansion time
    pattern = resolve_interpolations(__module__, pattern)
    # Prepend skip segments for prefix and PURL prefix stripping.
    # PURL: sequential steps (scheme choice, then domain+path choice) so that
    # "https://example.com/foo/123", "http://example.com/foo/123",
    # and "example.com/foo/123" are all accepted.
    # Prefix: simple case-insensitive skip, unless the pattern already
    # starts with a skip that covers the prefix string.
    full_pattern = pattern
    if !isnothing(prefix_val) && !isempty(prefix_val) &&
            lowercase(prefix_val) ∉ map(lowercase, leading_skip_strings(full_pattern))
        full_pattern = Expr(:tuple, Expr(:call, :skip, prefix_val), full_pattern)
    end
    if !isnothing(purlprefix_val)
        steps = decompose_purl_prefix(purlprefix_val)
        full_pattern = Expr(:tuple, Expr(:call, :skip, steps...), full_pattern)
    end
    globals = (; prefix = prefix_val, purlprefix = purlprefix_val)
    typeparts, state = maketype(
        segments, __module__, name, full_pattern;
        supertype = supertype_val,
        casefold = casefold_val,
        globals,
        global_kwargs = GLOBAL_KWARGS)
    # Work around Julia <1.12 hygiene bug: @inbounds expands to
    # `local val = expr` which conflicts with function parameters
    # named `val` after gensym renaming. Pre-expand in PackedParselets code.
    idparts = Base.structdiff(typeparts, NamedTuple{(:print, :show)})
    if VERSION < v"1.12-"
        for expr in values(idparts)
            expand_macrocall_inbounds!(expr)
        end
    end
    extra = identifier_finalize(typeparts, state, name)
    precompile_stmts = precompile_exprs(name)
    result = Expr(:toplevel, values(idparts)..., extra..., precompile_stmts..., nothing)
    result
end

function precompile_exprs(name::Symbol)
    T = esc(name)
    CU = Base.CodeUnits{UInt8, String}
    Expr[:(precompile($(GlobalRef(PackedParselets, :parsebytes)), (Type{$T}, $CU))),
         :(precompile($(GlobalRef(Base, :parse)), (Type{$T}, String))),
         :(precompile($(GlobalRef(Base, :tryparse)), (Type{$T}, String))),
         :(precompile($(GlobalRef(Base, :string)), ($T,)))]
end

end
