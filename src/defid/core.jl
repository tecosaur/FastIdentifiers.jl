# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Identifier-specific types layered on top of PackedParselets core.

# Resolved checkdigit metadata for downstream codegen.
const ChecksumInfo = @NamedTuple{
    fn::Union{GlobalRef, Expr},  # the checksum function reference for codegen
    field_seg_idx::Int,          # index into exprs.segments of the referenced field
    parse_expr::Expr,            # byte→value expression (uses :checkbyte as the byte var)
}

# Compatibility alias during transition.
const DefIdState = ParserState
