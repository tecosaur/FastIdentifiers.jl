# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module DefId

using FastIdentifiers: FastIdentifiers, AbstractIdentifier, MalformedIdentifier,
    ChecksumViolation, shortcode, purlprefix, idchecksum, idcode

using PackedParselets: PackedParselets,
    ExprVarLine, NodeCtx, PatternExprs, ParserState,
    SegmentOutput, SegmentDef, SegmentBounds, SegmentCodegen, SegmentMeta,
    CORE_SEGMENTS, maketype,
    emit_lengthcheck, register_errmsg!, implement_casting!

# Resolved checkdigit metadata for downstream codegen.
const ChecksumInfo = @NamedTuple{
    fn::Union{GlobalRef, Expr},
    field_seg_idx::Int,
    parse_expr::Expr,
}

include("checksum.jl")

## Segment registry

const ID_SEGMENTS = merge(CORE_SEGMENTS, (checkdigit = SegmentDef(:checkdigit, compile_checkdigit, (), finalize_checkdigit!),))

const GLOBAL_KWARGS = (:purlprefix,)

## Identifier-specific finalization

function identifier_finalize!(block::Expr, state::ParserState, name::Symbol)
    ename = esc(name)
    push!(block.args, identifier_parse(state, name)...)
    # Rewrite Base.print → FastIdentifiers.shortcode (the generic
    # AbstractIdentifier.print handles PURL prefixing), and patch
    # show's :limit branch similarly.
    shortcode_ref = GlobalRef(FastIdentifiers, :shortcode)
    print_ref = GlobalRef(Base, :print)
    show_ref = GlobalRef(Base, :show)
    for arg in block.args
        arg isa Expr && Meta.isexpr(arg, :function) || continue
        sig = arg.args[1]
        Meta.isexpr(sig, :call) && !isempty(sig.args) || continue
        if sig.args[1] == print_ref
            sig.args[1] = shortcode_ref
        elseif sig.args[1] == show_ref
            rewrite_show_print_to_shortcode!(arg, shortcode_ref)
        end
    end
    push!(block.args, :($(shortcode_ref)(id::$ename) = string(id)))
    prefix = get(state.globals, :purlprefix, nothing)
    if !isnothing(prefix)
        push!(block.args,
              :($(GlobalRef(FastIdentifiers, :purlprefix))(::Type{$ename}) = $prefix))
    end
end

function rewrite_show_print_to_shortcode!(expr::Expr, shortcode_ref::GlobalRef)
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && length(arg.args) == 3 &&
           arg.args[1] === :print && arg.args[2] === :io && arg.args[3] === :id
            arg.args[1] = shortcode_ref
        else
            rewrite_show_print_to_shortcode!(arg, shortcode_ref)
        end
    end
end

function identifier_parse(state::ParserState, name::Symbol)
    errmsgs = Tuple(state.errconsts)
    ename = esc(name)
    _parsebytes = GlobalRef(PackedParselets, :parsebytes)
    _idchecksum = GlobalRef(FastIdentifiers, :idchecksum)
    checkdigit_output = let idx = findfirst(p -> first(p) === :checkdigit, state.segment_outputs)
        isnothing(idx) ? nothing : last(state.segment_outputs[idx])
    end
    has_checksum = !isnothing(checkdigit_output)
    parse_body = if has_checksum
        info = checkdigit_output.meta.context::ChecksumInfo
        byte_to_val = info.parse_expr
        quote
            result, pos = $_parsebytes($ename, codeunits(id))
            if result isa $ename
                if pos < 0
                    checkbyte = @inbounds codeunits(id)[-pos]
                    provided = $byte_to_val
                    throw(ChecksumViolation{$ename}(id, $_idchecksum(result), provided))
                end
                pos > ncodeunits(id) || throw(MalformedIdentifier{$ename}(id, "Unparsed trailing content"))
                result
            else
                throw(MalformedIdentifier{$ename}(id, @inbounds $errmsgs[result]))
            end
        end
    else
        quote
            result, pos = $_parsebytes($ename, codeunits(id))
            if result isa $ename
                pos > ncodeunits(id) || throw(MalformedIdentifier{$ename}(id, "Unparsed trailing content"))
                result
            else
                throw(MalformedIdentifier{$ename}(id, @inbounds $errmsgs[result]))
            end
        end
    end
    tryparse_cond = if has_checksum
        :(result isa $ename && pos > 0 && pos > ncodeunits(id))
    else
        :(result isa $ename && pos > ncodeunits(id))
    end
    (:(function $(GlobalRef(Base, :parse))(::Type{$ename}, id::AbstractString)
           $(parse_body.args...)
       end),
     :(function $(GlobalRef(Base, :tryparse))(::Type{$ename}, id::AbstractString)
           result, pos = $_parsebytes($ename, codeunits(id))
           if $tryparse_cond
               result
           end
       end))
end

## @defid macro

"""
    @defid name pattern [kwarg=value...]

Define a bit-packed identifier type `name` with parsing and printing `pattern`.

The `pattern` is an S-expression describing the identifier structure.
Available constructs:

- `seq(arg1, arg2, ...)`: sequence (implicit default, just write `(arg1, arg2, ...)`)
- `optional(arg1, arg2, ...)`: optional section
- `skip([print=str0], str1, str2, ...)`: skip matching prefixes
- `choice([is=opt0], opt1, opt2, ...)`: choose between literal strings
- `literal(str)`: required literal string
- `digits([n | min:max], [base=10, min=0, max=base^digits-1, pad=0])`: digit field
- `letters([n | min:max])`, `alphnum([n | min:max])`, `hex([n | min:max])`: character sequences
- `charset([n | min:max], range1, range2, ...)`: custom character set (ranges are `'a':'z'` or single `'x'`)
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
macro defid(name, pattern, args...)
    segments = ID_SEGMENTS
    all_kws = (Iterators.flatten(s.kwargs for s in segments)..., GLOBAL_KWARGS...)
    casefold_val = true
    prefix_val = nothing
    for arg in args
        Meta.isexpr(arg, :(=), 2) || throw(ArgumentError("Expected keyword arguments of the form key=value, got $arg"))
        kwname, kwval = arg.args
        kwname ∈ all_kws ||
            throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(all_kws, ", "))"))
        kwname === :casefold && (casefold_val = kwval)
        kwname === :purlprefix && (prefix_val = kwval)
    end
    # Prepend a skip segment for PURL prefix stripping
    full_pattern = if !isnothing(prefix_val)
        Expr(:tuple, Expr(:call, :skip, lowercase(prefix_val)), pattern)
    else
        pattern
    end
    globals = if !isnothing(prefix_val); (; purlprefix = prefix_val) else (;) end
    block, state = maketype(segments, __module__, name, full_pattern;
                            supertype = AbstractIdentifier,
                            casefold = casefold_val,
                            globals,
                            global_kwargs = GLOBAL_KWARGS)
    identifier_finalize!(block, state, name)
    block
end

end
