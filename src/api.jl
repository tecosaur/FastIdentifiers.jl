# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

"""
    AbstractIdentifier

An abstract type for structured (and validated) digital identifiers.

It is expected that all identifiers have a plain text canonical form, and
optionally a PURL (Persistent Uniform Resource Locator) that can be used to link
to the resource. These may be one and the same.

All subtypes of `AbstractIdentifier` must implement `Base.parse` and `Base.tryparse`
methods. Using [`@defid`](@ref) generates these automatically; hand-written types
should override the methods directly.

See also: [`shortcode`](@ref), [`purl`](@ref), [`@defid`](@ref).

# Extended help

Digital identifiers like DOIs, ORCIDs, and ISBNs share common patterns but have
different validation rules and URL schemes. This framework provides a consistent
interface for all of them.

## Terminology

- **Shortcode**: The minimal representation without prefixes (e.g., "123")
- **Canonical**: The standard formatted representation (e.g., "MyID:123")
- **PURL**: Persistent URL for web access (e.g., "https://example.com/123")

## Implementation Guide

The recommended way to define identifier types is [`@defid`](@ref), which
generates parsing, printing, and property access from a declarative pattern.

For hand-written types, implement `Base.parse(::Type{T}, ::AbstractString)`
and `Base.tryparse(::Type{T}, ::AbstractString)` directly.

### Optional Methods

- [`shortcode`](@ref) — minimally formatted representation (has a default
  for single-field numeric types via [`idcode`](@ref))
- [`idcode`](@ref) — numeric component extraction; enables automatic
  `shortcode` generation and comparison
- [`idchecksum`](@ref) — checksum component; defining this auto-generates
  a `T(id, checksum)` validating constructor
- [`purlprefix`](@ref) (or [`purl`](@ref)) — persistent URL generation

## Invariants

All identifiers should ensure round-trip consistency:
- `parse(T, shortcode(x)) == x`
- `parse(T, string(x)) == x`
- `parse(T, purl(x)) == x` (when applicable)

# See Also

- [`MalformedIdentifier`](@ref), [`ChecksumViolation`](@ref): Exception types
- [`@reexport`](@ref): Convenience macro for exporting the public-facing API
"""
abstract type AbstractIdentifier end

"""
    MalformedIdentifier{T}(input, position::Int, problem::String)
    MalformedIdentifier{T}(input, problem::String)

Exception indicating that `input` is not a valid form of identifier type `T`.

The `problem` string should describe what specifically makes the input invalid.
`position` is the 1-based byte offset where the error was detected (0 if unknown).
"""
struct MalformedIdentifier{T <: AbstractIdentifier, I} <: Exception
    input::I
    position::Int
    problem::String
end

MalformedIdentifier{T}(input::I, position::Int, problem::String) where {T, I} =
    MalformedIdentifier{T,I}(input, position, problem)
MalformedIdentifier{T}(input::I, problem::String) where {T, I} =
    MalformedIdentifier{T,I}(input, 0, problem)

"""
    ChecksumViolation{T}(id, position::Int, expected::Integer, provided::Integer)
    ChecksumViolation{T}(id, expected::Integer, provided::Integer)

The `provided` checksum for the `T` identifier `id` is incorrect;
the correct checksum is `expected`. `position` is the 1-based byte
offset of the check character (0 if unknown).

# Example

```julia
function MyID(value::Integer, checksum::Integer)
    id = MyID(value) # Create without checksum validation
    expected = idchecksum(id)
    expected == checksum || throw(ChecksumViolation{MyID}(value, expected, checksum))
    id
end
```
"""
struct ChecksumViolation{T <: AbstractIdentifier, I} <: Exception
    id::I
    position::Int
    expected::Int
    provided::Int
end

ChecksumViolation{T}(id::I, position::Int, expected::Integer, provided::Integer) where {T, I} =
    ChecksumViolation{T, I}(id, position, Int(expected), Int(provided))
ChecksumViolation{T}(id::I, expected::Integer, provided::Integer) where {T, I} =
    ChecksumViolation{T, I}(id, 0, Int(expected), Int(provided))

"""
    idcode(id::AbstractIdentifier) -> Union{Integer, Nothing}

Return the numeric identifier component, if applicable.

The default implementation automatically extracts the first field if the
identifier type has exactly one integer field and no checksum. Should the first
field be another identifier, `idcode` is called on that identifier. Specialised
methods should be implemented for identifiers that need more sophisticated
handling.

Returns `nothing` if the identifier has multiple fields or uses a checksum.

See also: [`idchecksum`](@ref), [`shortcode`](@ref).
"""
function idcode(id::AbstractIdentifier)
    if fieldcount(typeof(id)) == 1
        if fieldtype(typeof(id), 1) <: Integer && isnothing(idchecksum(id))
            getfield(id, 1)
        elseif fieldtype(typeof(id), 1) <: AbstractIdentifier
            idcode(getfield(id, 1))
        end
    end
end

"""
    idchecksum(id::AbstractIdentifier) -> Union{Integer, Nothing}

Return the checksum/check digit component, if applicable.

The default implementation returns `nothing`. Identifiers that include or
support checksum should implement specialised methods. When `idchecksum` is defined,
a generic `MyIdentifier(id, checksum)` constructor is automatically provided that:
- Constructs the identifier using `MyIdentifier(id)`
- Validates the computed checksum matches the provided checksum
- Throws `ChecksumViolation` if the checksums don't match

Returns `nothing` if the identifier has no checksum component.

See also: [`idcode`](@ref), [`ChecksumViolation`](@ref).
"""
function idchecksum(::AbstractIdentifier) end

function (T::Type{<:AbstractIdentifier})(id, checksum)
    if hasmethod(T, Tuple{typeof(id)})
        tid = T(id)
        expected = idchecksum(tid)
        if !isnothing(expected)
            checksum == expected || throw(ChecksumViolation{T}(id, expected, checksum))
            return tid
        end
    end
    throw(MethodError(T, (id, checksum)))
end

"""
    shortcode(io::IO, id::AbstractIdentifier) -> Nothing
    shortcode(id::AbstractIdentifier) -> String

Return the minimal string representation of an identifier.

This is the most compact unambiguous form, without prefixes or decorative formatting.
The shortcode should contain only the essential identifying information.

If [`idcode`](@ref) is defined, the default implementation prints the numeric value.
Otherwise, you must implement this method explicitly.

See also: [`idcode`](@ref), [`purl`](@ref).
"""
function shortcode(io::IO, id::AbstractIdentifier)
    icode = idcode(id)
    if !isnothing(icode)
        print(io, icode)
    elseif fieldcount(typeof(id)) == 1
        val = getfield(id, 1)
        if val isa AbstractIdentifier
            shortcode(io, val)
        end
    end
end

shortcode(id::AbstractIdentifier) = sprint(shortcode, id)

"""
    purlprefix(::Type{<:AbstractIdentifier}) -> Union{String, Nothing}

Return the standard prefix of a PURL for an `AbstractIdentifier`, if applicable.

If defined, this implies that a PURL can be constructed by appending the `shortcode`
representation of the identifier to this prefix. As such, you should take care to
include any necessary trailing slashes or other separators in this prefix.
"""
function purlprefix(::Type{T}) where {T <: AbstractIdentifier} end

purlprefix(::T) where {T <: AbstractIdentifier} = purlprefix(T)

"""
    idprefix(::Type{<:AbstractIdentifier}) -> Union{String, Nothing}

Return the canonical display prefix for an identifier type (e.g. "arXiv:"),
or `nothing` if the type has no prefix. Used by `print` and `string` to
produce the standard representation. Defaults to [`purlprefix`](@ref).
"""
idprefix(::Type{T}) where {T <: AbstractIdentifier} = purlprefix(T)

idprefix(::T) where {T <: AbstractIdentifier} = idprefix(T)

"""
    purl(id::AbstractIdentifier) -> Union{String, Nothing}

If applicable, return the PURL of an `AbstractIdentifier`.

PURLs provide permanent web links to resources. The generic implementation
constructs URLs using [`purlprefix`](@ref), if defined, together with the
[`shortcode`](@ref) of the identifier.

Returns `nothing` if no web URL is available for this identifier type.

See also: [`purlprefix`](@ref), [`shortcode`](@ref).
"""
function purl(id::AbstractIdentifier)
    prefix = purlprefix(id)
    if !isnothing(prefix)
        prefix * shortcode(id)
    end
end

function Base.print(io::IO, id::AbstractIdentifier)
    if get(io, :limit, false) === true
        get(io, :compact, false) === true ||
            print(io, nameof(typeof(id)), ':')
    else
        prefix = idprefix(id)
        isnothing(prefix) || print(io, prefix)
    end
    shortcode(io, id)
end

Base.string(id::AbstractIdentifier) = sprint(print, id)

function Base.show(io::IO, id::AbstractIdentifier)
    if get(io, :limit, false) === true
        if get(io, :typeinfo, Nothing) != typeof(id)
            print(io, nameof(typeof(id)), ':')
        end
        print(io, shortcode(id))
    elseif isnothing(idchecksum(id)) &&
           fieldcount(typeof(id)) == 1 &&
           idcode(id) == getfield(id, 1)
        show(io, typeof(id))
        print(io, '(', idcode(id), ')')
    else
        show(io, parse)
        show(io, (typeof(id), shortcode(id)))
    end
end

function Base.isless(a::T, b::T) where {T <: AbstractIdentifier}
    ca = idcode(a)
    cb = idcode(b)
    (isnothing(ca) || isnothing(cb)) && return isless(shortcode(a), shortcode(b))
    ca < cb
end
