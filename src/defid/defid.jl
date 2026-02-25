# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module DefId

using FastIdentifiers: FastIdentifiers, AbstractIdentifier, MalformedIdentifier,
    ChecksumViolation, shortcode, purlprefix, segments, nbits, parsebytes, tobytes,
    parsebounds, printbounds, idchecksum, idcode

include("../packed/PackedParselets.jl")
using .PackedParselets: SentinelSpec, SegmentBounds, SegmentCodegen, SegmentMeta,
    SegmentOutput, SegmentDef, segment_set, segment_kwargs, all_kwargs,
    # Core types
    ExprVarLine, NodeCtx, OptSentinel,
    ValueSegment, PatternExprs,
    ParseBranch, ParserState,
    # Bit-sizing
    cardbits, cardtype,
    # State mutation
    inc_parsed!, inc_print!, register_errmsg,
    # Segment helpers
    value_segment_output, emit_print_detect!, opt_fail_expr,
    unclaimed_sentinel, claim_sentinel!, process_segment_output!,
    segments_formstring,
    # Bit packing
    zero_int, zero_parsed_expr, emit_pack, emit_extract,
    # Loaders
    REGISTER_TYPES, register_type, register_chunks, backward_verify_chunk,
    pack_bytes, pack_chunk, gen_load, gen_masked_compare,
    # Runtime utilities
    parsechars, parseint, byte2int, fastparse,
    printchars, chars2string,
    bufprint, bufprintchars,
    # SWAR
    gen_digit_parse,
    # Placeholders
    emit_lengthcheck, emit_static_lengthcheck, emit_lengthbound,
    insert_length_checks!, fold_static_branches!, implement_casting!,
    strip_segment_markers!, resolve_remaining_sentinels!,
    # String handlers
    compile_literal, compile_skip,
    gen_literal_mismatch, gen_static_lchop, gen_string_match,
    negate_match, conjoin_match

@static if VERSION < v"1.13-"
    using .PackedParselets: takestring!
end

include("core.jl")
include("choices.jl")
include("methods.jl")
include("sequences.jl")
include("checkdigits.jl")
include("dispatch.jl")

"""
    deftype(segments, mod, name, pattern; casefold, purlprefix) -> Expr(:toplevel, ...)

Workhorse function for `@defid`. Walks the pattern AST, dispatches to
segment handlers via `segments`, and assembles all method definitions.

Returns a `:toplevel` expression block ready for `eval`.
"""
function deftype(segments::NamedTuple, mod::Module, name::Symbol, pattern;
                 casefold::Bool = true, purlprefix::Union{Nothing, String} = nothing)
    root = ParseBranch(1, nothing, :root, 0, 0, 0, 0, 0, 0)
    globals = if isnothing(purlprefix); (;) else (; purlprefix) end
    state = ParserState(name, mod, 0, AbstractIdentifier, FastIdentifiers,
                        globals, ParseBranch[root], String[], Pair{Symbol, SegmentOutput}[])
    nctx = NodeCtx(:current_branch, root)
    nctx = NodeCtx(nctx, :casefold, casefold)
    exprs = PatternExprs(([], [], [], []))
    if !isnothing(purlprefix)
        defid_dispatch!(exprs, state, nctx, segments, Expr(:call, :skip, lowercase(purlprefix)))
    end
    defid_dispatch!(exprs, state, nctx, segments, :__first_nonskip)
    defid_dispatch!(exprs, state, nctx, segments, pattern)
    defid_make(exprs, state, name, segments)
end

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
    all_kws = (all_kwargs(segments)..., GLOBAL_KWARGS...)
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
    deftype(segments, __module__, name, pattern;
            casefold = casefold_val, purlprefix = prefix_val)
end

end
