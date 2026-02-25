# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Identifier-specific method assembly: parse/tryparse with MalformedIdentifier
# and ChecksumViolation, shortcode/tobytes, and purlprefix emission.

"""
    defid_make(exprs, state, name, segments) -> Expr(:toplevel, ...)

Assemble all method definitions for the generated identifier type.

Delegates to `assemble_type` for generic methods, with `identifier_finalize!`
providing identifier-specific parse/tryparse, shortcode, and purlprefix.
"""
function defid_make(exprs::PatternExprs, state::DefIdState, name::Symbol,
                    segments::NamedTuple = (;))
    assemble_type(exprs, state, name, segments;
                  finalize! = identifier_finalize!)
end

## Identifier-specific finalization

function identifier_finalize!(block::Expr, exprs::PatternExprs,
                              state::DefIdState, name::Symbol)
    # parse/tryparse with MalformedIdentifier and ChecksumViolation
    push!(block.args, identifier_parse(state, name)...)
    # shortcode/tobytes
    push!(block.args, identifier_shortcode(exprs.print, state, name))
    # purlprefix
    prefix = get(state.globals, :purlprefix, nothing)
    if !isnothing(prefix)
        push!(block.args,
              :($(GlobalRef(FastIdentifiers, :purlprefix))(::Type{$(esc(name))}) = $prefix))
    end
end

## parse / tryparse

function identifier_parse(state::DefIdState, name::Symbol)
    errmsgs = Tuple(state.errconsts)
    ename = esc(name)
    checkdigit_output = let idx = findfirst(p -> first(p) === :checkdigit, state.segment_outputs)
        isnothing(idx) ? nothing : last(state.segment_outputs[idx])
    end
    has_checksum = !isnothing(checkdigit_output)
    parse_body = if has_checksum
        info = checkdigit_output.meta.context::ChecksumInfo
        fn_ref = info.fn
        byte_to_val = info.parse_expr
        quote
            result, pos = parsebytes($ename, codeunits(id))
            if result isa $ename
                if pos < 0
                    # Checksum violation: re-read the check byte to report provided value
                    checkbyte = @inbounds codeunits(id)[-pos]
                    provided = $byte_to_val
                    throw(ChecksumViolation{$ename}(id, idchecksum(result), provided))
                end
                pos > ncodeunits(id) || throw(MalformedIdentifier{$ename}(id, "Unparsed trailing content"))
                result
            else
                throw(MalformedIdentifier{$ename}(id, @inbounds $errmsgs[result]))
            end
        end
    else
        quote
            result, pos = parsebytes($ename, codeunits(id))
            if result isa $ename
                pos > ncodeunits(id) || throw(MalformedIdentifier{$ename}(id, "Unparsed trailing content"))
                result
            else
                throw(MalformedIdentifier{$ename}(id, @inbounds $errmsgs[result]))
            end
        end
    end
    tryparse_cond = if has_checksum
        :(result isa $ename && pos > 0 && pos > ncodeunits(id))
    else
        :(result isa $ename && pos > ncodeunits(id))
    end
    (:(function $(GlobalRef(Base, :parse))(::Type{$ename}, id::AbstractString)
           $(parse_body.args...)
       end),
     :(function $(GlobalRef(Base, :tryparse))(::Type{$ename}, id::AbstractString)
           result, pos = parsebytes($ename, codeunits(id))
           if $tryparse_cond
               result
           end
       end))
end

## shortcode / tobytes

function identifier_shortcode(pexprs::Vector{ExprVarLine}, state::DefIdState, name::Symbol)
    tobytes_def = assemble_tobytes(pexprs, state, name)
    root = state.branches[1]
    fixedlen = root.print_min == root.print_max
    shortcode_io_def = :(function $(GlobalRef(FastIdentifiers, :shortcode))(io::IO, id::$(esc(name)))
          buf, len = tobytes(id)
          unsafe_write(io, pointer(buf), len)
          nothing
      end)
    shortcode_def = if fixedlen
        :(function $(GlobalRef(FastIdentifiers, :shortcode))(id::$(esc(name)))
              buf, _ = tobytes(id)
              Base.unsafe_takestring(buf)
          end)
    else
        :(function $(GlobalRef(FastIdentifiers, :shortcode))(id::$(esc(name)))
              buf, len = tobytes(id)
              str = Base.StringMemory(len)
              Base.unsafe_copyto!(pointer(str), pointer(buf), len)
              Base.unsafe_takestring(str)
          end)
    end
    Expr(:block, tobytes_def, shortcode_io_def, shortcode_def)
end
