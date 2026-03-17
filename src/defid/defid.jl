# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module DefId

using FastIdentifiers: FastIdentifiers, AbstractIdentifier, MalformedIdentifier,
    ChecksumViolation, shortcode, purlprefix, segments, nbits, parsebytes, tobytes,
    parsebounds, printbounds, idchecksum, idcode

include("../packed/PackedParsers.jl")
using .PackedParsers: SentinelSpec, SegmentBounds, SegmentCodegen, SegmentMeta,
    SegmentOutput, SegmentDef, segment_set, all_kwargs

include("utils.jl")
include("core.jl")
include("loaders.jl")
include("swar.jl")
include("stringly.jl")
include("choices.jl")
include("placeholders.jl")
include("methods.jl")
include("sequences.jl")
include("checkdigits.jl")
include("dispatch.jl")

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
    casefold_val = true
    prefix_val = nothing
    for arg in args
        Meta.isexpr(arg, :(=), 2) || throw(ArgumentError("Expected keyword arguments of the form key=value, got $arg"))
        kwname, kwval = arg.args
        kwname ∈ ALL_KNOWN_KEYS ||
            throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
        kwname === :casefold && (casefold_val = kwval)
        kwname === :purlprefix && (prefix_val = kwval)
    end
    root = ParseBranch(1, nothing, nothing, 0, 0, 0, 0, 0)
    state = DefIdState(name, __module__, 0, casefold_val, prefix_val, ParseBranch[root], String[], nothing, Pair{Symbol, SegmentOutput}[])
    nctx = NodeCtx(:current_branch, root)
    exprs = IdExprs(([], [], [], []))
    if !isnothing(prefix_val)
        defid_dispatch!(exprs, state, nctx, Expr(:call, :skip, lowercase(prefix_val)))
    end
    defid_dispatch!(exprs, state, nctx, :__first_nonskip)
    defid_dispatch!(exprs, state, nctx, pattern)
    defid_make(exprs, state, name)
end

end
