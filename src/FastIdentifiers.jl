# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module FastIdentifiers

export AbstractIdentifier, MalformedIdentifier, ChecksumViolation, shortcode, purl, @defid

@static if VERSION >= v"1.11"
    eval(Expr(:public, :idcode, :idchecksum, :purlprefix, Symbol("@reexport")))
end

"""
    FastIdentifiers.@reexport

Convenience macro to import and export all public interface components.

This macro generates `using` and `export` statements for the core `FastIdentifiers`
interface, making it easy to re-export the API from implementing packages.

# Exported Components

- [`AbstractIdentifier`](@ref): Base type for all identifier implementations
- [`MalformedIdentifier`](@ref): Exception for invalid identifier formats
- [`ChecksumViolation`](@ref): Exception for checksum validation failures
- [`shortcode`](@ref): Get minimal string representation
- [`purl`](@ref): Get persistent URL representation
"""
macro reexport()
    quote
        using FastIdentifiers: AbstractIdentifier, MalformedIdentifier, ChecksumViolation, shortcode, purl
        export AbstractIdentifier, MalformedIdentifier, ChecksumViolation, shortcode, purl
    end
end

include("api.jl")
include("defid.jl")
using .DefId: @defid

end
