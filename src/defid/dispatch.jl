# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern dispatch and structural handlers (field capture, optional branching).

## Pattern dispatch

function defid_dispatch!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         node::Any, args::Vector{Any})
    if node isa QuoteNode
        defid_field!(exprs, state, nctx, node, args)
    elseif node === :seq
        for arg in args
            defid_dispatch!(exprs, state, nctx, arg)
        end
    elseif node === :optional
        defid_optional!(exprs, state, nctx, args)
    elseif node === :skip
        output = compile_skip(state, nctx, args)
        if isempty(output.meta.desc)
            # Skip without print: apply parse codegen and byte bounds only
            append!(exprs.parse, output.codegen.parse)
            inc_parsed!(nctx, first(output.bounds.parsed), last(output.bounds.parsed))
        else
            process_segment_output!(exprs, state, nctx, :skip, output)
        end
    elseif node === :choice
        defid_choice!(exprs, state, nctx, args)
    elseif node === :literal
        output = compile_literal(state, nctx, args)
        process_segment_output!(exprs, state, nctx, :literal, output)
    elseif node === :digits
        output = compile_digits(state, nctx, args)
        process_segment_output!(exprs, state, nctx, :digits, output)
    elseif node in (:letters, :alphnum, :hex, :charset)
        defid_charseq!(exprs, state, nctx, args, node)
    elseif node === :embed
        output = compile_embed(state, nctx, args)
        process_segment_output!(exprs, state, nctx, :embed, output)
    elseif node === :checkdigit
        output = compile_checkdigit(exprs, state, nctx, args)
        process_segment_output!(exprs, state, nctx, :checkdigit, output)
    else
        throw(ArgumentError("Unknown pattern node $node"))
    end
end

function defid_dispatch!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         thing::Any)
    if Meta.isexpr(thing, :tuple)
        args = Any[]
        for arg in thing.args
            if Meta.isexpr(arg, :(=), 2)
                kwname, kwval = arg.args
                kwname ∈ ALL_KNOWN_KEYS ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(ALL_KNOWN_KEYS, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, state, nctx, :seq, args)
    elseif Meta.isexpr(thing, :call)
        name = first(thing.args)
        args = Any[]
        nkeys = if name isa Symbol && haskey(KNOWN_KEYS, name)
            KNOWN_KEYS[name]
        else
            ALL_KNOWN_KEYS
        end
        for arg in thing.args[2:end]
            if Meta.isexpr(arg, :kw, 2)
                kwname, kwval = arg.args
                kwname ∈ nkeys ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments for $name are: $(join(nkeys, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        defid_dispatch!(exprs, state, nctx, name, args)
    elseif thing isa String
        output = compile_literal(state, nctx, Any[thing])
        process_segment_output!(exprs, state, nctx, :literal, output)
    elseif thing === :__first_nonskip
        root = nctx[:current_branch]
        root.parsed_min = 0
        root.parsed_max = 0
        push!(exprs.parse, Expr(:call, :__branch_check, root.id, nothing))
    end
end

## Field capture

function defid_field!(exprs::IdExprs,
                      state::DefIdState, nctx::NodeCtx,
                      node::QuoteNode,
                      args::Vector{Any})
    isnothing(get(nctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    nctx = NodeCtx(nctx, :fieldvar, Symbol("attr_$(node.value)"))
    initial_segs = length(exprs.segments)
    initialprints = length(exprs.print)
    for arg in args
        defid_dispatch!(exprs, state, nctx, arg)
    end
    new_value_segs = filter(s -> !isnothing(s.argtype), @view exprs.segments[initial_segs+1:end])
    isempty(new_value_segs) && throw(ArgumentError("Field $(node.value) does not capture any value"))
    if length(new_value_segs) == 1
        push!(exprs.properties, node.value => new_value_segs[1].label)
    else
        # Multi-node field: property assembles via IOBuffer from print expressions
        propprints = map(strip_segsets! ∘ copy, exprs.print[initialprints+1:end])
        filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, propprints)
        push!(exprs.properties, node.value => ExprVarLine[(
            quote
                io = IOBuffer()
                $(propprints...)
                takestring!(io)
            end).args...])
    end
end

## Optional branching

function defid_optional!(exprs::IdExprs,
                         state::DefIdState, nctx::NodeCtx,
                         args::Vector{Any})
    popt = get(nctx, :optional, nothing)
    optvar = gensym("optional")
    end_label = gensym("opt_end")
    nctx = NodeCtx(nctx, :optional, optvar)
    nctx = NodeCtx(nctx, :opt_label, end_label)
    nctx = NodeCtx(nctx, :oprint_detect, ExprVarLine[])
    # Fork a child branch for this optional scope
    parent = nctx[:current_branch]
    child = ParseBranch(length(state.branches) + 1, parent, optvar,
                        parent.parsed_min, parent.parsed_min, parent.parsed_min,
                        parent.print_min, parent.print_max)
    push!(state.branches, child)
    nctx = NodeCtx(nctx, :current_branch, child)
    sentinel_ref = Ref{Union{Nothing, OptSentinel}}(nothing)
    nctx = NodeCtx(nctx, :optional_sentinel, sentinel_ref)
    seg_start = length(exprs.segments)
    bits_before = state.bits
    oexprs = (; parse = ExprVarLine[], print = ExprVarLine[], segments = exprs.segments, properties = exprs.properties)
    if all(a -> a isa String, args)
        defid_choice!(oexprs, state, nctx, push!(Any[join(Vector{String}(args))], ""))
    else
        for arg in args
            defid_dispatch!(oexprs, state, nctx, arg)
        end
    end
    seg_end = length(exprs.segments)
    if sentinel_ref[] === nothing
        flag_nbits = (state.bits += 1)
        push!(oexprs.parse, defid_emit_pack(state, Bool, optvar, flag_nbits))
        sentinel_ref[] = OptSentinel((flag_nbits, 1))
    end
    # Patch segment extract conditions with the resolved sentinel check
    sentinel = sentinel_ref[]
    check = :(!iszero($(defid_emit_extract(state, sentinel.position, sentinel.nbits))))
    for i in seg_start+1:seg_end
        extract = exprs.segments[i].extract
        isempty(extract) && continue
        last_expr = extract[end]
        if Meta.isexpr(last_expr, :if) && last_expr.args[1] === true
            last_expr.args[1] = check
        end
    end
    # Merge max back to parent; min stays unchanged (optional content doesn't raise the guarantee)
    parent.parsed_max += child.parsed_max - child.start_min
    parent.print_max = Base.max(parent.print_max, child.print_max)
    # Build the branch guard (nested optionals require the parent flag too)
    savedpos = gensym("savedpos")
    branch_check = Expr(:call, :__branch_check, Bool, child.id)
    guard = if isnothing(popt)
        branch_check
    else
        :($popt && $branch_check)
    end
    push!(exprs.parse, :($savedpos = pos))
    push!(exprs.parse, :($optvar = $guard))
    push!(exprs.parse, :(if $optvar; $(oexprs.parse...) end))
    push!(exprs.parse, :(@label $end_label))
    # Cleanup: rewind pos and clear any bits packed by partial success
    opt_bits = state.bits - bits_before
    if opt_bits > 1  # single segment: failure already leaves zero bits
        opt_width = opt_bits
        mask_type = cardtype(opt_width)
        mask_val = typemax(mask_type) >> (8 * sizeof(mask_type) - opt_width)
        clear_expr = :(parsed = Core.Intrinsics.and_int(parsed,
            Core.Intrinsics.not_int(
                Core.Intrinsics.shl_int(
                    __cast_to_id($mask_type, $mask_val),
                    8 * sizeof($(esc(state.name))) - $(state.bits)))))
        push!(exprs.parse, :(if !$optvar; pos = $savedpos; $clear_expr end))
    else
        push!(exprs.parse, :(if !$optvar; pos = $savedpos end))
    end
    # Print-time presence detection: single assignment from the sentinel
    append!(exprs.print, nctx[:oprint_detect])
    push!(exprs.print, :($optvar = $check))
    push!(exprs.print, :(if $optvar; $(oexprs.print...) end))
end
