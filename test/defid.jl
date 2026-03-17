# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Tests for identifier-specific features: @defid output formatting,
# PURL generation, and checkdigit validation.

using Test
using FastIdentifiers: FastIdentifiers, AbstractIdentifier, MalformedIdentifier,
    ChecksumViolation, shortcode, purl, purlprefix, idcode, idchecksum, @defid
using PackedParselets: parsebytes, parsebounds, printbounds, nbits
using FastIdentifiers.DefId.Checksums: mod10, mod11_2
using InteractiveUtils: code_llvm

"""
    @test_neverthrow f(arg1, ::Type, ...)

Test that the LLVM IR for the given method signature contains no `throw` calls.
"""
macro test_neverthrow(expr)
    Meta.isexpr(expr, :call) || error("@test_neverthrow expects a call expression, got: $expr")
    func = expr.args[1]
    argtypes = map(expr.args[2:end]) do arg
        if Meta.isexpr(arg, :(::), 1)
            esc(arg.args[1])
        else
            :(ttypeof($(esc(arg))))
        end
    end
    typetup = Expr(:curly, :Tuple, argtypes...)
    quote
        let ir = sprint(code_llvm, $(esc(func)), $typetup; context=:debuginfo => :none)
            throws = filter(contains("ijl_throw"), split(ir, '\n'))
            @test isempty(throws)
        end
    end
end
ttypeof(::Type{T}) where {T} = Type{T}
ttypeof(x) = typeof(x)

function check_roundtrips(T, inputs)
    for input in inputs
        id = parse(T, input)
        @test parse(T, shortcode(id)) == id
    end
end

# --- Define a simple @defid type for output formatting tests ---

eval(:(@defid SimpleId ("SI", :id(digits(max=9999, pad=4)))))

@testset "Output formatting" begin
    id = parse(SimpleId, "SI42")
    @testset "print (default context)" begin
        @test sprint(print, id) == shortcode(id)
    end
    @testset "show (reconstructable form)" begin
        shown = sprint(show, id)
        @test occursin("SimpleId", shown)
        @test occursin("parse", shown) || occursin("SimpleId(", shown)
    end
    @testset "show with :limit" begin
        limited = sprint(show, id; context=IOContext(stdout, :limit => true))
        @test occursin("SimpleId", limited)
    end
    @testset "show with :typeinfo suppresses type name" begin
        ctx = IOContext(stdout, :limit => true, :typeinfo => SimpleId)
        typed = sprint(show, id; context=ctx)
        @test !startswith(typed, "SimpleId")
    end
    @testset "print with :limit" begin
        ctx = IOContext(stdout, :limit => true)
        limited = sprint(print, id; context=ctx)
        @test occursin("SimpleId", limited)
        @test occursin("0042", limited)
    end
    @testset "print with :limit + :compact omits type" begin
        ctx = IOContext(stdout, :limit => true, :compact => true)
        compact = sprint(print, id; context=ctx)
        @test !startswith(compact, "SimpleId:")
    end
end

@testset "PURL generation" begin
    @testset "WithPrefix" begin
        eval(:(@defid WithPrefix ("WP-", :id(digits(max=9999))) purlprefix="https://example.com/wp/"))
        # purlprefix method
        @test purlprefix(WithPrefix) == "https://example.com/wp/"
        # purl concatenates prefix + shortcode
        id = parse(WithPrefix, "WP-42")
        @test purl(id) == "https://example.com/wp/" * shortcode(id)
        # print uses PURL when no :limit
        @test sprint(print, id) == purl(id)
        # No prefix → purl returns nothing
        @test purl(parse(SimpleId, "SI1")) === nothing
        # Round-trips
        check_roundtrips(WithPrefix, ("WP-0", "WP-9999"))
        @test_neverthrow parsebytes(WithPrefix, ::Vector{UInt8})
    end
    @testset "PURL prefix stripping" begin
        id = parse(WithPrefix, "WP-42")
        @test parse(WithPrefix, "https://example.com/wp/WP-42") == id
        @test tryparse(WithPrefix, "https://example.com/wp/WP-42") == id
    end
end

@testset "checkdigit" begin
    @testset "TestEAN13 (decimal check digit, mod10)" begin
        eval(:(@defid TestEAN13 (:code(digits(12:12, pad=12)),
               checkdigit(:code, mod10))))
        # Successful parse: 4006381333931 → check digit 1
        id = parse(TestEAN13, "4006381333931")
        @test id isa TestEAN13
        @test id.code == 400638133393
        @test idchecksum(id) == 1
        @test idcode(id) == 400638133393
        # Shortcode includes computed check digit
        @test shortcode(id) == "4006381333931"
        # Round-trip
        @test parse(TestEAN13, shortcode(id)) == id
        check_roundtrips(TestEAN13, ("4006381333931", "0000000000000", "5901234123457"))
        # ChecksumViolation on wrong check digit
        @test_throws ChecksumViolation parse(TestEAN13, "4006381333932")
        err = try parse(TestEAN13, "4006381333932"); nothing catch e; e end
        @test err isa ChecksumViolation{TestEAN13}
        @test err.expected == 1
        @test err.provided == 2
        # tryparse returns nothing on checksum violation
        @test tryparse(TestEAN13, "4006381333932") === nothing
        # Trailing content after valid checkdigit
        @test_throws MalformedIdentifier parse(TestEAN13, "40063813339310")
        # Structural errors take precedence over checksum errors
        @test_throws MalformedIdentifier parse(TestEAN13, "40063813339")  # too short
        @test_throws MalformedIdentifier parse(TestEAN13, "400638133393X")  # invalid digit
        # Invalid check character → MalformedIdentifier
        @test_throws MalformedIdentifier parse(TestEAN13, "40063813339A")
        # Constructor omits check digit argument
        @test TestEAN13(400638133393) == id
        @test shortcode(TestEAN13(400638133393)) == "4006381333931"
        # show uses constructor form without check digit
        shown = sprint(show, id)
        @test startswith(shown, "TestEAN13(")
        @test endswith(shown, ")")
        @test !occursin("checkdigit", shown)
        @test_neverthrow parsebytes(TestEAN13, ::Vector{UInt8})
    end
    @testset "TestMod11 (non-decimal check char, mod11_2)" begin
        eval(:(@defid TestMod11 (:code(digits(7:7, pad=7)),
               checkdigit(:code, mod11_2))))
        # mod11_2(1000002) = 1
        id = parse(TestMod11, "10000021")
        @test id isa TestMod11
        @test id.code == 1000002
        @test idchecksum(id) == 1
        # mod11_2(1000003) = 10 → 'X'
        idx = parse(TestMod11, "1000003X")
        @test idx isa TestMod11
        @test idchecksum(idx) == 10
        @test shortcode(idx) == "1000003X"
        # Case-insensitive X
        @test parse(TestMod11, "1000003x") == idx
        # Round-trips
        @test parse(TestMod11, shortcode(id)) == id
        @test parse(TestMod11, shortcode(idx)) == idx
        check_roundtrips(TestMod11, ("10000021", "1000003X"))
        # ChecksumViolation
        @test_throws ChecksumViolation parse(TestMod11, "10000022")
        err = try parse(TestMod11, "10000022"); nothing catch e; e end
        @test err isa ChecksumViolation{TestMod11}
        @test err.expected == 1
        @test err.provided == 2
        @test tryparse(TestMod11, "10000022") === nothing
        # Structural errors take precedence
        @test_throws MalformedIdentifier parse(TestMod11, "100000")  # too short
        # Invalid check character
        @test_throws MalformedIdentifier parse(TestMod11, "1000002Z")
        # Constructor omits check digit
        @test TestMod11(1000002) == id
        @test_neverthrow parsebytes(TestMod11, ::Vector{UInt8})
    end
    @testset "Non-terminal checkdigit (followed by literal)" begin
        eval(:(@defid CheckThenLit (:code(digits(4:4, pad=4)),
               checkdigit(:code, mod10), "-end")))
        # mod10(1234) = 8
        id = parse(CheckThenLit, "12348-end")
        @test id isa CheckThenLit
        @test id.code == 1234
        @test idchecksum(id) == 8
        @test shortcode(id) == "12348-end"
        @test parse(CheckThenLit, shortcode(id)) == id
        # Checksum violation with trailing literal present
        @test_throws ChecksumViolation parse(CheckThenLit, "12345-end")
        @test tryparse(CheckThenLit, "12345-end") === nothing
        # Missing trailing literal
        @test tryparse(CheckThenLit, "12348") === nothing
        @test tryparse(CheckThenLit, "12348-") === nothing
        @test_neverthrow parsebytes(CheckThenLit, ::Vector{UInt8})
    end
    @testset "Checkdigit with skip separator" begin
        eval(:(@defid CheckWithSkip (:code(digits(4:4, pad=4)),
               skip(print="-"), checkdigit(:code, mod10))))
        # mod10(1234) = 8
        id = parse(CheckWithSkip, "1234-8")
        @test id isa CheckWithSkip
        @test id.code == 1234
        @test shortcode(id) == "1234-8"
        @test parse(CheckWithSkip, "12348") == id  # without separator
        check_roundtrips(CheckWithSkip, ("1234-8", "0000-0"))
        @test_throws ChecksumViolation parse(CheckWithSkip, "1234-5")
        @test tryparse(CheckWithSkip, "1234-5") === nothing
        @test_neverthrow parsebytes(CheckWithSkip, ::Vector{UInt8})
    end
end # checkdigit
