# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Placeholder sentinel emission, resolution, and AST post-processing.
#
# During pattern walking, length checks and type casts are emitted as
# placeholder sentinel calls (e.g. `__length_check`, `__cast_to_id`)
# since the final byte counts and type sizes aren't known yet. After
# the full pattern has been walked, `resolve_length_checks!`,
# `fold_static_branches!`, and `implement_casting!` replace these
# sentinels with concrete expressions or compile-time constants.

## Sentinel emission

function defid_lengthcheck(state::DefIdState, nctx::NodeCtx, n_expr, n_min::Int=n_expr, n_max::Int=n_min)
    b = nctx[:current_branch]
    Expr(:call, :__length_check, b.id, b.parsed_max, n_min, n_max, n_expr)
end

function defid_static_lengthcheck(state::DefIdState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__static_length_check, b.id, b.parsed_max, n)
end

function defid_lengthbound(state::DefIdState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__length_bound, b.id, b.parsed_max, n)
end

## Sentinel resolution

"""
    resolve_length_checks!(exprlikes, branches) -> exprlikes

Walk the AST and replace all length-related sentinels with concrete expressions.

Each sentinel type uses the emitting branch's `parsed_min` as the static guarantee:
- `__length_check` → `true` or runtime `nbytes - pos + 1 >= n`
- `__static_length_check` → compile-time `Bool` (never runtime)
- `__length_bound` → `n` or `min(n, nbytes - pos + 1)`
- `__branch_check(Bool, id)` → resolved via `resolve_branch_check`
- `__branch_check(Int, id)` → left for `defid_parsebytes` (root upfront check)
"""
function resolve_length_checks!(exprlikes::Vector{<:ExprVarLine}, branches::Vector{ParseBranch})
    remove = Int[]
    for (idx, expr) in enumerate(exprlikes)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && first(expr.args) === :__branch_check
            if expr.args[2] === Bool
                exprlikes[idx] = resolve_branch_check(branches[expr.args[3]])
            end
            continue
        end
        result = resolve_sentinels!(expr, branches)
        if result === :remove
            push!(remove, idx)
        elseif !isnothing(result)
            exprlikes[idx] = result
        end
    end
    deleteat!(exprlikes, remove)
end

function resolve_branch_check(b::ParseBranch)
    local_min = b.parsed_min - b.start_min
    if local_min <= 0 || (!isnothing(b.parent) && b.parent.parsed_min >= b.parsed_min)
        true
    else
        :(nbytes - pos + 1 >= $local_min)
    end
end

# Recursive AST walker that resolves sentinel calls in-place.
# Branch-local `parsed_min` is the guarantee, so optionals don't inflate
# the max seen by sentinels in other branches.
function resolve_sentinels!(expr::Expr, branches::Vector{ParseBranch})
    remove = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        sentinel = if Meta.isexpr(arg, :call)
            first(arg.args)
        end
        if sentinel === :__length_check
            resolved = resolve_length_check(arg, branches)
            if resolved isa Expr
                arg.head, arg.args = resolved.head, resolved.args
            else
                expr.args[i] = resolved
            end
        elseif sentinel === :__length_bound
            branch_id, emission_max, n = arg.args[2:end]
            if branches[branch_id].parsed_min - emission_max >= n
                expr.args[i] = n
            else
                r = :(min($n, nbytes - pos + 1))
                arg.head, arg.args = r.head, r.args
            end
        elseif sentinel === :__static_length_check
            branch_id, emission_max, n = arg.args[2:end]
            expr.args[i] = branches[branch_id].parsed_min - emission_max >= n
        elseif sentinel === :__branch_check
            if arg.args[2] === Bool
                resolved = resolve_branch_check(branches[arg.args[3]])
                if resolved isa Expr
                    arg.head, arg.args = resolved.head, resolved.args
                else
                    expr.args[i] = resolved
                end
            end
        else
            result = resolve_sentinels!(arg, branches)
            if result === :remove
                push!(remove, i)
            elseif !isnothing(result)
                expr.args[i] = result
            end
        end
    end
    deleteat!(expr.args, remove)
    nothing
end

function resolve_length_check(expr::Expr, branches::Vector{ParseBranch})
    branch_id, emission_max, _, n_max, n_expr = expr.args[2:end]
    if branches[branch_id].parsed_min - emission_max >= n_max
        true
    else
        :(nbytes - pos + 1 >= $n_expr)
    end
end

## Optimal length-check insertion
#
# Framework-driven pass that analyses segment markers and inner sentinels
# to insert the minimum number of runtime length checks. Replaces the
# handler-embedded outer checks with globally optimal placement.

"""
    SegmentInfo

Segment metadata extracted from `__segment_begin`/`__segment_end` markers
for the length-check insertion pass.
"""
const SegmentInfo = @NamedTuple{
    begin_idx::Int,      # index into pexprs of __segment_begin marker
    end_idx::Int,        # index into pexprs of __segment_end marker
    seg_id::Int,         # 1-based segment ID
    branch_id::Int,      # branch owning this segment
    parsed_min::Int,     # minimum bytes consumed by this segment
    parsed_max::Int,     # maximum bytes consumed by this segment
    option::Any,         # optional scope symbol, or nothing if required
    opt_label::Any,      # goto label for optional failure, or nothing
    desc::String,        # human-readable description for error messages
}

"""
    SentinelInfo

A length sentinel found within a segment's parse expressions.
"""
const SentinelInfo = @NamedTuple{
    seg_idx::Int,        # index into segments array
    emission_max::Int,   # branch parsed_max at emission time
    threshold::Int,      # bytes needed (for __length_check: n_max; for others: n)
    kind::Symbol,        # :length_check, :static_length_check, :length_bound
}

"""
    insert_length_checks!(pexprs, branches) -> pexprs

Analyse segment markers and inner sentinels in `pexprs` to insert the
minimum number of runtime length checks. After insertion, resolves all
sentinels (outer and inner) and strips markers.

This is an optimisation pass: at each segment boundary where the remaining
byte guarantee is insufficient, it inserts a check for the maximum useful
amount, pushing the next mandatory check as far forward as possible.
"""
function insert_length_checks!(pexprs::Vector{ExprVarLine}, branches::Vector{ParseBranch})
    # Pass 1: collect segment markers
    segments = SegmentInfo[]
    open_seg = nothing
    for (idx, expr) in enumerate(pexprs)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && !isempty(expr.args)
            sentinel = first(expr.args)
            if sentinel === :__segment_begin
                _, seg_id, branch_id, p_min, p_max, option, opt_label, desc = expr.args
                open_seg = (idx, seg_id, branch_id, p_min, p_max, option, opt_label, desc)
            elseif sentinel === :__segment_end && !isnothing(open_seg)
                push!(segments, SegmentInfo((open_seg[1], idx, open_seg[2],
                    open_seg[3], open_seg[4], open_seg[5], open_seg[6],
                    open_seg[7], open_seg[8])))
                open_seg = nothing
            end
        end
    end
    isempty(segments) && return pexprs
    # Pass 1b: collect inner sentinels within each segment
    sentinels = SentinelInfo[]
    for (si, seg) in enumerate(segments)
        for idx in seg.begin_idx+1:seg.end_idx-1
            expr = pexprs[idx]
            collect_sentinels!(sentinels, si, expr)
        end
    end
    # Pass 2: greedy forward check placement per branch
    # Group segments by branch
    branch_segs = Dict{Int, Vector{Int}}()  # branch_id -> segment indices
    for (si, seg) in enumerate(segments)
        push!(get!(Vector{Int}, branch_segs, seg.branch_id), si)
    end
    # Track which sentinels are unresolved (not statically covered by parsed_min)
    unresolved = Set{Int}()
    for (i, sent) in enumerate(sentinels)
        bid = segments[sent.seg_idx].branch_id
        if branches[bid].parsed_min - sent.emission_max < sent.threshold
            push!(unresolved, i)
        end
    end
    # For each branch, compute check insertions.
    # Build fail_expr on demand from stored context (option, opt_label, desc).
    # Note: for Phase A dual-emit, these expressions aren't used (old pass is
    # primary), but we compute them for correctness validation.
    insertions = Tuple{Int, Expr}[]  # (pexprs index, check expression)
    for (bid, seg_indices) in branch_segs
        remaining = 0
        for si in seg_indices
            seg = segments[si]
            # What does this segment need at entry?
            seg_entry_need = seg.parsed_min
            # What do inner sentinels in this segment need?
            seg_inner_need = 0
            for (i, sent) in enumerate(sentinels)
                sent.seg_idx == si && i ∈ unresolved || continue
                seg_inner_need = Base.max(seg_inner_need, sent.threshold)
            end
            need = Base.max(seg_entry_need, seg_inner_need)
            if remaining < need
                G = max_needed_from(si, segments, sentinels, unresolved)
                G = Base.max(G, need)
                fail = if isnothing(seg.option)
                    # Required segment: error return (use desc as placeholder)
                    :(return ($(seg.desc), pos))
                else
                    opt_fail_expr(seg.option, seg.opt_label)
                end
                push!(insertions, (seg.begin_idx, :(nbytes - pos + 1 >= $G || $fail)))
                remaining = G
            end
            remaining -= seg.parsed_max
        end
    end
    # Pass 3: resolve all sentinels using the new guarantee tracking
    # Check is: Expr(:||, Expr(:call, :>=, lhs, G), fail_expr)
    insertion_set = Dict{Int, Int}()  # begin_idx -> guaranteed bytes
    for (idx, expr) in insertions
        G = expr.args[1].args[3]::Int
        insertion_set[idx] = G
    end
    for (bid, seg_indices) in branch_segs
        remaining = 0
        for si in seg_indices
            seg = segments[si]
            if haskey(insertion_set, seg.begin_idx)
                remaining = insertion_set[seg.begin_idx]
            end
            # Resolve sentinels in this segment
            for idx in seg.begin_idx+1:seg.end_idx-1
                resolve_sentinels_with_guarantee!(pexprs, idx, branches, remaining)
            end
            remaining -= seg.parsed_max
        end
    end
    # Pass 4: insert checks and strip markers
    # Sort insertions by position (descending) so indices stay valid
    sort!(insertions, by=first, rev=true)
    for (idx, check_expr) in insertions
        # Insert right after the __segment_begin marker
        insert!(pexprs, idx + 1, check_expr)
    end
    # Strip markers (collect indices, remove in reverse)
    marker_indices = Int[]
    for (idx, expr) in enumerate(pexprs)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && !isempty(expr.args)
            s = first(expr.args)
            if s === :__segment_begin || s === :__segment_end
                push!(marker_indices, idx)
            end
        end
    end
    deleteat!(pexprs, sort!(marker_indices, rev=false))
    pexprs
end

# Collect sentinel calls from an expression tree
function collect_sentinels!(sentinels::Vector{SentinelInfo}, seg_idx::Int, expr)
    expr isa Expr || return
    if Meta.isexpr(expr, :call) && !isempty(expr.args)
        s = first(expr.args)
        if s === :__length_check
            _, branch_id, emission_max, n_min, n_max, n_expr = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n_max, :length_check)))
        elseif s === :__static_length_check
            _, branch_id, emission_max, n = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n, :static_length_check)))
        elseif s === :__length_bound
            _, branch_id, emission_max, n = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n, :length_bound)))
        else
            for arg in expr.args
                collect_sentinels!(sentinels, seg_idx, arg)
            end
        end
    else
        for arg in expr.args
            collect_sentinels!(sentinels, seg_idx, arg)
        end
    end
end

# Compute the maximum useful check value from segment si onward
function max_needed_from(si::Int, segments::Vector{SegmentInfo},
                         sentinels::Vector{SentinelInfo}, unresolved::Set{Int})
    bid = segments[si].branch_id
    # Find all segments on the same branch from si onward
    cumulative_max = 0
    G = 0
    for sj in si:length(segments)
        segments[sj].branch_id == bid || continue
        # Check sentinels in segment sj
        for (i, sent) in enumerate(sentinels)
            sent.seg_idx == sj && i ∈ unresolved || continue
            G = Base.max(G, sent.threshold + cumulative_max)
        end
        # Also need the outer entry requirement
        G = Base.max(G, segments[sj].parsed_min + cumulative_max)
        cumulative_max += segments[sj].parsed_max
    end
    G
end

# Resolve sentinels in a single expression using the guarantee at that point
function resolve_sentinels_with_guarantee!(pexprs::Vector{ExprVarLine}, idx::Int,
                                           branches::Vector{ParseBranch}, remaining::Int)
    expr = pexprs[idx]
    expr isa Expr || return
    resolve_sentinel_in_expr!(expr, branches, remaining)
end

function resolve_sentinel_in_expr!(expr::Expr, branches::Vector{ParseBranch}, remaining::Int)
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && !isempty(arg.args)
            s = first(arg.args)
            if s === :__length_check
                _, branch_id, emission_max, n_min, n_max, n_expr = arg.args
                if branches[branch_id].parsed_min - emission_max >= n_max || remaining >= n_max
                    expr.args[i] = true
                else
                    r = :(nbytes - pos + 1 >= $n_expr)
                    arg.head, arg.args = r.head, r.args
                end
            elseif s === :__static_length_check
                _, branch_id, emission_max, n = arg.args
                expr.args[i] = branches[branch_id].parsed_min - emission_max >= n || remaining >= n
            elseif s === :__length_bound
                _, branch_id, emission_max, n = arg.args
                if branches[branch_id].parsed_min - emission_max >= n || remaining >= n
                    expr.args[i] = n
                else
                    r = :(min($n, nbytes - pos + 1))
                    arg.head, arg.args = r.head, r.args
                end
            else
                resolve_sentinel_in_expr!(arg, branches, remaining)
            end
        else
            resolve_sentinel_in_expr!(arg, branches, remaining)
        end
    end
end

"""
    strip_segment_markers!(pexprs) -> pexprs

Remove `__segment_begin` and `__segment_end` marker calls from the expression
list and any nested expression blocks. Used by the old resolution pass to
tolerate the new markers during the dual-emit transition.
"""
function strip_segment_markers!(pexprs::Vector{<:ExprVarLine})
    filter!(pexprs) do expr
        !(expr isa Expr && Meta.isexpr(expr, :call) && !isempty(expr.args) &&
          first(expr.args) in (:__segment_begin, :__segment_end))
    end
    for expr in pexprs
        expr isa Expr && strip_segment_markers_nested!(expr)
    end
    pexprs
end

function strip_segment_markers_nested!(expr::Expr)
    remove = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && !isempty(arg.args) &&
           first(arg.args) in (:__segment_begin, :__segment_end)
            push!(remove, i)
        else
            strip_segment_markers_nested!(arg)
        end
    end
    isempty(remove) || deleteat!(expr.args, sort!(remove))
end

## Static branch folding

"""
    fold_static_branches!(items::Vector{<:ExprVarLine}) -> items

Resolve `if true`/`if false` and their negations statically, splicing the
taken branch in place. Recurses into nested expressions and repeats until
fixpoint.
"""
function fold_static_branches!(items::Vector{<:ExprVarLine})
    while fold_branches!(items) end
    items
end

function fold_branches!(items::AbstractVector)
    splices = Tuple{Int, Vector{Any}}[]
    changed = false
    for (i, item) in enumerate(items)
        item isa Expr || continue
        if item.head in (:if, :elseif) && item.args[1] isa Bool
            push!(splices, (i, take_branch(item)))
            changed = true
        elseif item.head in (:if, :elseif) &&
               Meta.isexpr(item.args[1], :call, 2) &&
               item.args[1].args[1] === :! && item.args[1].args[2] isa Bool
            item.args[1] = !item.args[1].args[2]
            push!(splices, (i, take_branch(item)))
            changed = true
        elseif item.head === :|| && item.args[1] isa Bool
            push!(splices, (i, if item.args[1] Any[] else Any[item.args[2]] end))
            changed = true
        elseif item.head === :&& && item.args[1] isa Bool
            push!(splices, (i, if item.args[1] Any[item.args[2]] else Any[] end))
            changed = true
        else
            changed |= fold_branches!(item.args)
        end
    end
    for (i, replacement) in reverse(splices)
        splice!(items, i, replacement)
    end
    changed
end

function take_branch(expr::Expr)
    if expr.args[1]::Bool
        body = expr.args[2]
    elseif length(expr.args) >= 3
        body = expr.args[3]
        if body isa Expr && body.head === :elseif
            body.head = :if
        end
    else
        return Any[]
    end
    if body isa Expr && body.head === :block
        filter(e -> !(e isa LineNumberNode), body.args)
    else
        Any[body]
    end
end

## Casting resolution

"""
    implement_casting!(state, exprlikes) -> exprlikes

Replace `__cast_to_id` / `__cast_from_id` sentinels with the appropriate
`Core.bitcast`, `zext_int`, or `trunc_int` call, now that the final type
size is known.

Compares physical type sizes (`sizeof`) for intrinsic selection, since
`zext_int`/`trunc_int` operate on physical widths — not logical bit counts.
This matters for embedded `@defid` types whose `nbits` may be less than
`8*sizeof`.
"""
function implement_casting!(state::DefIdState, exprlikes::Vector{<:ExprVarLine})
    targetsize = cld(state.bits, 8)
    for expr in exprlikes
        if expr isa Expr
            implement_casting!(expr, state.name, targetsize)
        end
    end
    exprlikes
end

function implement_casting!(expr::Expr, name::Symbol, targetsize::Int)
    if Meta.isexpr(expr, :call, 3) && first(expr.args) in (:__cast_to_id, :__cast_from_id)
        casttype, valtype, value = expr.args
        targettype, targetbits, valbits = if casttype == :__cast_to_id
            esc(name), targetsize, sizeof(valtype)
        else
            valtype, sizeof(valtype), targetsize
        end
        expr.args[1:3] = if valbits == targetbits
            :(Core.bitcast($targettype, $value)).args
        elseif valbits < targetbits
            :(Core.Intrinsics.zext_int($targettype, $value)).args
        else
            :(Core.Intrinsics.trunc_int($targettype, $value)).args
        end
    else
        for arg in expr.args
            if arg isa Expr
                implement_casting!(arg, name, targetsize)
            end
        end
    end
    expr
end
