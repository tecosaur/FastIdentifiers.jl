# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module FastIdentifiers

export AbstractIdentifier, MalformedIdentifier, ChecksumViolation, shortcode, purl, @defid

public idcode, idchecksum, idprefix, purlprefix, @reexport

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
using .DefId: @defid, Checksums

# Compile the @defid pipeline once here so downstream packages inherit it rather
# than each re-paying the first-use cost. The types are eval'd, not just
# macroexpanded: expansion alone infers the compiler functions but skips their
# LLVM codegen, which is the larger cost. The patterns span the segment handlers
# and codegen branches (SWAR digit/hex, charseq flags, perfect-hash vs linear
# choice, tagged choice, optional, each checksum width, both display modes).
# The gensym'd module (and its types) persists in the package image, unreachable
# by name.
using PrecompileTools: @compile_workload
@compile_workload begin
    @eval module $(gensym(:warmup))
        using ..FastIdentifiers: @defid, Checksums, shortcode, purl
        @defid P1 ("R-", :sp(letters(3, upper=true)), skip(choice("-", "_")),
                   :id(digits(1:15, pad=15)), optional(".", :v(digits(max=255))),
                   checkdigit(:id, Checksums.mod11_2)) purlprefix="https://x.org/R_"
        @defid P2 (skip(choice("Q:", "Q_", "Q")), :h(hex(8, skip="-")),
                   :c(charset(6, '0':'9', numeric=true)), :id(digits(6, pad=6)),
                   checkdigit(:id, Checksums.mod97)) prefix="Q:"
        @defid P3 choice(seq("CID", :a(digits(3))),
                         seq("SID", :m(alphnum(4, upper=true))))
        @defid P3b (:code(digits(12, pad=12)), checkdigit(:code, Checksums.mod10))
        @defid P4 (choice(:kind, :a => seq("A", :v(digits(2))),
                                 :b => seq("B", :v(digits(3)))),
                   :sp(letters(3, lower=true)))
        # Warm the runtime helpers too; the constructor computes the check digit.
        let id = P3b(45)
            shortcode(id); string(id); purl(id)
        end
        tryparse(P3b, string(P3b(45)))
    end
end

end
