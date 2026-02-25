# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Checkdigit segment handler and standard checksum functions.
#
# The checkdigit segment validates a single check character derived from
# a previously captured field. Zero bits are stored — the check digit is
# recomputed from the field value on print.

## Checkdigit handler

function compile_checkdigit(exprs::IdExprs,
                            state::DefIdState, nctx::NodeCtx,
                            ::SegmentDef, args::Vector{Any})
    !isnothing(get(nctx, :optional, nothing)) &&
        throw(ArgumentError("checkdigit cannot appear inside optional(...)"))
    !isnothing(state.checksum) &&
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
    fn_resolved = builtin ? getfield(Checksums, fn_expr) : Core.eval(state.mod, fn_expr)
    fn_ref = builtin ? GlobalRef(Checksums, fn_expr) : esc(fn_expr)
    # Side effect: register checksum info (used by defid_make for idchecksum/idcode)
    state.checksum = ChecksumInfo((fn_ref, seg_idx,
                                   Checksums.parse_byte(fn_resolved, :checkbyte, nctx)))
    # Parse codegen
    checkpos = gensym("checkpos")
    checkbyte = gensym("checkbyte")
    checkval = gensym("checkval")
    ok_sym = gensym("checksum_ok")
    errmsg = defid_errmsg(state, "Invalid check character")
    lencheck = defid_lengthcheck(state, nctx, 1)
    seg = exprs.segments[seg_idx]
    extract_copy = map(copy, seg.extract)
    parse_exprs = ExprVarLine[
          :($checkpos = pos),
          :(if !$lencheck; return ($errmsg, pos) end),
          :($checkbyte = @inbounds idbytes[pos]),
          :($checkval = $(Checksums.parse_byte(fn_resolved, checkbyte, nctx))),
          :(if $checkval < 0; return ($errmsg, pos) end),
          :(pos += 1),
          :(id = parsed),
          extract_copy[1:end-1]...,
          :($ok_sym = ($checkval == $fn_ref($(last(extract_copy))))),
          Expr(:call, :__checksum_gate, ok_sym, checkpos)]
    # Print codegen — emit single byte via write(io, UInt8)
    seg_print_extract = map(copy, seg.extract)
    val_to_byte = Checksums.print_byte(fn_resolved, :($fn_ref($(last(seg_print_extract)))), nctx)
    print_detect = ExprVarLine[seg_print_extract[1:end-1]...]
    SegmentOutput(
        SegmentBounds(1:1, 1:1, 0, nothing),
        SegmentCodegen(parse_exprs, ExprVarLine[], print_detect, Any[],
                       ExprVarLine[:(write(io, $val_to_byte))]),
        SegmentMeta(:checkdigit, "check digit", "check", nothing, nothing))
end

## Checksums module — protocol and standard checksum functions

module Checksums

using ..DefId: NodeCtx

"""
    parse_byte(fn, bytevar::Symbol, nctx::NodeCtx) -> Expr

Return an expression mapping check byte `bytevar` to a 0-based integer,
or `-1` for invalid bytes. `nctx` carries pattern context (e.g. casefold).

The default handles decimal digits (0–9).
"""
parse_byte(fn, bytevar::Symbol, ::NodeCtx) =
    :(ifelse($bytevar - 0x30 < 0x0a, Int($bytevar - 0x30), -1))

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
print_byte(::typeof(mod11_2), valexpr, ::NodeCtx) =
    :(ifelse($valexpr < 10, UInt8($valexpr) + 0x30, $(UInt8('X'))))

end # module Checksums

using .Checksums: Checksums
