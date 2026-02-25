# PackedParselets — parser compiler for bit-packed primitive types.
#
# Generates optimised parsers, printers, and accessors from declarative
# pattern specifications. This submodule has no knowledge of identifiers,
# PURLs, or checksums — those are added by the FastIdentifiers layer.

module PackedParselets

include("types.jl")
include("core.jl")
include("loaders.jl")
include("utils.jl")

end # module PackedParselets
