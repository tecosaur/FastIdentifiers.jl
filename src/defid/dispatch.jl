# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Identifier-specific segment registries and dispatch wrappers.

const ID_SEGMENTS = merge(CORE_SEGMENTS, segment_set(
    SegmentDef(:checkdigit, compile_checkdigit, (), finalize_checkdigit!),
))

const GLOBAL_KWARGS = (:purlprefix,)

# Dispatch wrappers that bind the identifier-specific global kwargs tuple.
function defid_dispatch!(exprs::PatternExprs, state::DefIdState,
                         nctx::NodeCtx, segments::NamedTuple,
                         node::Any, args::Vector{Any})
    pattern_dispatch!(exprs, state, nctx, segments, GLOBAL_KWARGS, node, args)
end
function defid_dispatch!(exprs::PatternExprs, state::DefIdState,
                         nctx::NodeCtx, segments::NamedTuple,
                         thing::Any)
    pattern_dispatch!(exprs, state, nctx, segments, GLOBAL_KWARGS, thing)
end
