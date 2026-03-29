# FastIdentifiers.jl

A framework for structured, validated identifier types with parsing, formatting,
and URL generation.

FastIdentifiers provides [`AbstractIdentifier`](@ref) as a base type and
[`@defid`](@ref) as a macro for declaring concrete identifier types backed by
[PackedParselets.jl](https://code.tecosaur.net/tec/PackedParselets). It is not a
user-facing package, it provides the machinery for downstream packages such as
[AcademicIdentifiers.jl](https://code.tecosaur.net/tec/AcademicIdentifiers.jl)
and [BioIdentifiers.jl](https://code.tecosaur.net/tec/BioIdentifiers.jl).

## Display Model

Every identifier has three string representations:

- **`shortcode(id)`**: the minimal form without any prefix (e.g. `"0006915"`)
- **`string(id)`**: the canonical display form, typically `prefix * shortcode` (e.g. `"GO:0006915"`)
- **`purl(id)`**: a persistent URL when available (e.g. `"https://purl.obolibrary.org/obo/GO_0006915"`)

These are controlled by two `@defid` keyword arguments:

- **`prefix=`**: sets the display prefix used by `string` and `print` (e.g. `"GO:"`). Also generates a `skip` so identifiers can be parsed from prefixed form. Set to `""` for types where `string` should equal `shortcode`.
- **`purlprefix=`**: sets the URL prefix for `purl` construction (`purlprefix * shortcode`). Also generates URL-stripping `skip` steps so identifiers can be parsed from full URLs.

When only `purlprefix=` is set (no `prefix=`), `string` outputs the PURL. When
both are set, `string` uses the display prefix and `purl` uses the URL prefix.

## Defining Identifiers

```@docs
@defid
FastIdentifiers.@reexport
```

## Types

```@docs
AbstractIdentifier
MalformedIdentifier
ChecksumViolation
```

## Identifier API

```@docs
FastIdentifiers.shortcode
FastIdentifiers.purl
FastIdentifiers.purlprefix
FastIdentifiers.idprefix
FastIdentifiers.idcode
FastIdentifiers.idchecksum
Base.parse(::Type{<:AbstractIdentifier}, ::String)
Base.tryparse(::Type{<:AbstractIdentifier}, ::String)
Base.print(::IO, ::AbstractIdentifier)
```
