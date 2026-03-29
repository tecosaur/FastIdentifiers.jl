# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Checkdigit segment handler and standard checksum functions.
#
# The checkdigit segment validates a single check character derived from
# a previously captured field. Zero bits are stored — the check digit is
# recomputed from the field value on print.

## Checkdigit handler

function compile_checkdigit(state::ParserState, nctx::NodeCtx,
                            exprs::PatternExprs,
                            ::SegmentDef, args::Vector{Any})
    !isnothing(get(nctx, :optional, nothing)) &&
        throw(ArgumentError("checkdigit cannot appear inside optional(...)"))
    any(p -> first(p) === :checkdigit, state.segment_outputs) &&
        throw(ArgumentError("Only one checkdigit per type is allowed"))
    length(args) == 2 || throw(ArgumentError(
        "checkdigit requires exactly 2 positional arguments: (:field, fn), got $(length(args))"))
    fieldname_node, fn_expr = args
    fieldname_node isa QuoteNode || throw(ArgumentError(
        "First argument to checkdigit must be a quoted field name, got $fieldname_node"))
    fieldname = fieldname_node.value::Symbol
    # Resolve the referenced field's segment
    prop_idx = findfirst(p -> first(p) == fieldname, exprs.properties)
    isnothing(prop_idx) && throw(ArgumentError(
        "checkdigit references unknown field :$fieldname"))
    prop_val = last(exprs.properties[prop_idx])
    prop_val isa Symbol || throw(ArgumentError(
        "checkdigit field :$fieldname must be a single-segment property"))
    seg_idx = findfirst(s -> s.label == prop_val, exprs.segments)
    isnothing(seg_idx) && throw(ArgumentError(
        "checkdigit field :$fieldname has no matching segment"))
    # Resolve checksum function and codegen reference
    builtin = fn_expr isa Symbol && isdefined(Checksums, fn_expr)
    fn = if builtin getfield(Checksums, fn_expr) else Core.eval(state.mod, fn_expr) end
    fnref = if builtin GlobalRef(Checksums, fn_expr) else esc(fn_expr) end
    n = Checksums.nbytes(fn)
    checkbytes = ntuple(i -> gensym("checkbyte$i"), n)
    # Literal symbols for identifier_parse context (bound in the generated parse function)
    report_bytes = ntuple(i -> Symbol("checkbyte$i"), n)
    checksum_info = ChecksumInfo(fnref, seg_idx, n,
                                  Checksums.parse_bytes(fn, report_bytes, nctx))
    # Parse codegen
    checkpos = gensym("checkpos")
    checkval = gensym("checkval")
    ok_sym = gensym("checksum_ok")
    notfound = build_fail_expr!(state, nctx, "Invalid check character")
    lencheck = emit_lengthcheck(state, nctx, n)
    seg = exprs.segments[seg_idx]
    extract_copy = map(copy, seg.extract)
    parse_exprs = ExprVarLine[
          :($checkpos = pos),
          :(if !$lencheck; $notfound end)]
    for (i, bvar) in enumerate(checkbytes)
        push!(parse_exprs, :($bvar = @inbounds data[pos + $(i - 1)]))
    end
    append!(parse_exprs, ExprVarLine[
          :($checkval = $(Checksums.parse_bytes(fn, checkbytes, nctx))),
          :(if $checkval < 0; $notfound end),
          :(pos += $n),
          :(val = parsed),
          extract_copy[1:end-1]...,
          :($ok_sym = ($checkval == $fnref($(last(extract_copy))))),
          Expr(:call, :__checksum_gate, ok_sym, checkpos)])
    # Print codegen
    seg_print_extract = map(copy, seg.extract)
    getval = ExprVarLine[seg_print_extract[1:end-1]...]
    print_exprs = ExprVarLine[Checksums.print_bytes(fn, :($fnref($(last(seg_print_extract)))), nctx)...]
    valid = Checksums.valid_bytes(fn, nctx)
    SegmentOutput(
        SegmentBounds(n:n, n:n, 0, nothing),
        SegmentCodegen(parse_exprs, ExprVarLine[],
            PrintExprs(direct = ExprVarLine[getval..., print_exprs...],
                       getval = getval, getlen = ExprVarLine[:(pos += $n)],
                       putval = print_exprs),
            Expr[]),
        SegmentMeta(:checkdigit, "check digit", "check", nothing, nothing, checksum_info),
        [fill(valid, n)])
end

## Checkdigit finalize hook

"""
    finalize_checkdigit!(block, exprs, state, name)

Post-assembly finalize hook for the checkdigit segment.

Generates `idchecksum` and `idcode` methods, and patches `parse`/`tryparse`
to handle checksum violations (negative pos from `__checksum_gate`).
"""
function finalize_checkdigit!(hookdata::Vector{Expr}, exprs::PatternExprs,
                              state::ParserState, name::Symbol)
    idx = findfirst(p -> first(p) === :checkdigit, state.segment_outputs)
    isnothing(idx) && return
    output = last(state.segment_outputs[idx])
    info = output.meta.context::ChecksumInfo
    (; fn, field_seg_idx) = info
    seg = exprs.segments[field_seg_idx]
    # idchecksum: extract the field value, apply the checksum function
    cs_extract = map(copy, seg.extract)
    implement_casting!(state, cs_extract)
    cs_value = last(cs_extract)
    push!(hookdata,
          :(function $(GlobalRef(FastIdentifiers, :idchecksum))(val::$(esc(name)))
                $(cs_extract[1:end-1]...)
                $fn($cs_value)
            end),
          :(function $(GlobalRef(FastIdentifiers, :idcode))(val::$(esc(name)))
                $(cs_extract[1:end-1]...)
                $cs_value
            end))
end

## Checksums module — protocol and standard checksum functions

module Checksums

using ..DefId: NodeCtx, ByteSet

"""
    parse_byte(fn, bytevar::Symbol, nctx::NodeCtx) -> Expr

Return an expression mapping check byte `bytevar` to a 0-based integer,
or `-1` for invalid bytes. `nctx` carries pattern context (e.g. casefold).

The default handles decimal digits (0–9).
"""
parse_byte(fn, bytevar::Symbol, ::NodeCtx) =
    :(ifelse($bytevar - 0x30 < 0x0a, Int($bytevar - 0x30), -1))
valid_bytes(fn, ::NodeCtx) = ByteSet(UInt8('0'):UInt8('9'))

"""
    print_byte(fn, valexpr, nctx::NodeCtx) -> Expr

Return an expression mapping checksum integer `valexpr` to a `UInt8` byte.

The default handles decimal digits (0–9).
"""
print_byte(fn, valexpr, ::NodeCtx) =
    :(UInt8($valexpr) + 0x30)

"""
    mod10(code::Integer) -> Int

Weighted mod-10 checksum (EAN-13/UPC).

Alternates weights 1 and 3 across digits from right to left,
returns `(10 - sum % 10) % 10`.
"""
function mod10(code::Integer)
    s, w = 0, 3
    while code > 0
        code, d = divrem(code, 10)
        s += d * w
        w = 4 - w  # alternates 3, 1, 3, 1, ...
    end
    (10 - s % 10) % 10
end

"""
    mod11_2(code::Integer) -> Int

ISO 7064 MOD 11-2 checksum (ORCID, ISNI).

Processes digits left to right: `r = (r + digit) * 2 mod 11`.
Returns `(12 - r) mod 11`, yielding 0–10 (10 maps to 'X' via `print_byte`).
"""
function mod11_2(code::Integer)
    r = 0
    for d in Iterators.reverse(digits(code))
        r = (r + d) * 2 % 11
    end
    (12 - r) % 11
end
parse_byte(::typeof(mod11_2), bytevar::Symbol, ::NodeCtx) =
    :(if $bytevar - 0x30 < 0x0a; Int($bytevar - 0x30)
      elseif ($bytevar | 0x20) == $(UInt8('x')); 10
      else -1 end)
valid_bytes(::typeof(mod11_2), ::NodeCtx) =
    ByteSet(UInt8('0'):UInt8('9'), UInt8('X'), UInt8('x'))
print_byte(::typeof(mod11_2), valexpr, ::NodeCtx) =
    :(ifelse($valexpr < 10, UInt8($valexpr) + 0x30, $(UInt8('X'))))

"""
    mod97(code::Integer) -> Int

ISO 7064 MOD 97-10 checksum (ROR).

The check value satisfies `code * 100 + check ≡ 1 (mod 97)`.
Returns `98 - (code * 100) % 97`, yielding 2–98 as a two-digit decimal.
"""
mod97(code::Integer) = 98 - (code * 100) % 97

## Multi-byte protocol

"""
    nbytes(fn) -> Int

Number of check bytes for checksum function `fn`. Default is 1.
Override for multi-byte checksums (e.g. `mod97` uses 2 digits).
"""
nbytes(fn) = 1
nbytes(::typeof(mod97)) = 2

"""
    parse_bytes(fn, bytevars::NTuple{N, Symbol}, nctx) -> Expr

Map multiple check bytes to a single integer value, or `-1` for invalid.
Default defers to `parse_byte` for single-byte checksums.
"""
function parse_bytes(fn, bytevars::NTuple{1, Symbol}, nctx::NodeCtx)
    parse_byte(fn, first(bytevars), nctx)
end
function parse_bytes(::typeof(mod97), bytevars::NTuple{2, Symbol}, ::NodeCtx)
    b1, b2 = bytevars
    :(if $b1 - 0x30 < 0x0a && $b2 - 0x30 < 0x0a
          Int($b1 - 0x30) * 10 + Int($b2 - 0x30)
      else -1 end)
end

"""
    print_bytes(fn, valexpr, nctx) -> Vector{Expr}

Emit expressions writing the check value as bytes.
Default defers to `print_byte` for single-byte checksums.
"""
function print_bytes(fn, valexpr, nctx::NodeCtx)
    [:(write(io, $(print_byte(fn, valexpr, nctx))))]
end
function print_bytes(::typeof(mod97), valexpr, ::NodeCtx)
    [:(write(io, UInt8(($valexpr) ÷ 10) + 0x30)),
     :(write(io, UInt8(($valexpr) % 10) + 0x30))]
end

valid_bytes(::typeof(mod97), ::NodeCtx) = ByteSet(UInt8('0'):UInt8('9'))

end # module Checksums

using .Checksums: Checksums
