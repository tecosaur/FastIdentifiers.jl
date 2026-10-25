# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module AboutExt

using FastIdentifiers: AbstractIdentifier
using PackedParselets: segments, Segment
using About
using StyledStrings: @styled_str as @S_str, face!
using Base: AnnotatedString

# function About.memorylayout(io::IO, type::Type{<:AbstractIdentifier})
#     isprimitivetype(type) && hasmethod(segments, (Type{type},)) || invoke(About.memorylayout, Tuple{IO, Type}, io, type)
#     segs = segments(type)
#     for (i, (; nbits)) in enumerate(segs)
#         print(io, '.' ^ nbits)
#     end
# end

# The segments of `layout` from bit `pos` that `id` holds, and the bit after it. `owner` is
# the position of the `:arm` whose option holds a segment; an `:arm` adds its `option`.
function held(layout, texts::Vector{Any}, pos::Int, owner = nothing)
    parts, arm = Any[], nothing
    for s in layout
        if s isa Segment
            part = (; pos, s.nbits, seg = s, text = popfirst!(texts), owner)
            if s.kind === :arm
                arm = part
            elseif !isnothing(part.text)
                push!(parts, part)
            end
            pos += s.nbits
        else
            options = [if isnothing(opt); (Any[], pos) else held(opt, texts, pos, if isnothing(arm) owner else arm.pos end) end
                       for opt in s.options]
            k = findfirst(o -> !isempty(first(o)), options)
            held_arm = !isnothing(arm) && !isnothing(arm.text)
            isnothing(k) && held_arm && (k = findfirst(isnothing, s.options))
            if !isnothing(k)
                held_arm && push!(parts, (; arm..., option = k, s.options))
                append!(parts, first(options[k]))
            end
            pos, arm = maximum(last, options), nothing
        end
    end
    parts, pos
end

held(id::AbstractIdentifier) = first(held(segments(typeof(id)), collect(Any, segments(id)), 0))

function About.memorylayout(io::IO, id::AbstractIdentifier)
    isprimitivetype(typeof(id)) && hasmethod(segments, (Type{typeof(id)},)) || invoke(About.memorylayout, Tuple{IO, DataType}, io, id)
    parts = held(id)
    shown = filter(p -> p.nbits > 0, parts)
    bstr = AnnotatedString(bitstring(id))
    lastbit = 0
    for (i, (; pos, nbits)) in enumerate(shown)
        pos > lastbit && face!(bstr, lastbit + 1:pos, :shadow)
        face!(bstr, pos + 1:pos + nbits, About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))])
        lastbit = pos + nbits
    end
    if lastbit < ncodeunits(bstr)
        face!(bstr, lastbit + 1:ncodeunits(bstr), :shadow)
    end
    if get(io, :compact, false) == true
        return print(io, bstr)
    end
    print(io, "\n ", bstr, "\n ")
    lastbit = 0
    for (i, (; pos, nbits)) in enumerate(shown)
        face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
        print(io, ' ' ^ (pos - lastbit))
        if nbits == 1
            print(io, S"{$face:╨}")
        elseif nbits < 2 + ndigits(i)
            print(io, S"{$face:└$('─'^(nbits - 2))┘}")
        else
            nleft = (nbits - 2 - ndigits(i)) ÷ 2
            nright = (nbits - 2 - ndigits(i)) - nleft
            print(io, S"{$face:└$('─'^nleft)$(i)$('─'^nright)┘}")
        end
        lastbit = pos + nbits
    end
    print(io, S"\n {bold:=} ")
    for p in parts
        i = findfirst(q -> q.pos === (if iszero(p.nbits) p.owner else p.pos end), shown)
        if isnothing(i)
            print(io, S"{light:$(p.text)}")
        else
            face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
            print(io, S"{$face:$(p.text)}")
        end
    end
    println(io)
end

function About.elaboration(io::IO, id::AbstractIdentifier)
    isprimitivetype(typeof(id)) && hasmethod(segments, (Type{typeof(id)},)) || invoke(About.elaboration, Tuple{IO, DataType}, io, id)
    for (i, p) in enumerate(filter(p -> p.nbits > 0, held(id)))
        seg = p.seg
        face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
        label, desc = if seg.kind === :arm
            tagged = hasproperty(id, seg.label)
            alternatives = string(if any(isnothing, p.options) "optional, " else "" end,
                                  count(!isnothing, p.options), " alternatives")
            (if tagged seg.label else :choice end,
             string(if tagged getproperty(id, seg.label) else "option $(p.option)" end, " (", alternatives, ")"))
        elseif seg.kind === :presence
            (:optional, "present")
        else
            (seg.label, seg.desc)
        end
        print(io, S"\n {$face:• $label}: $desc")
    end
    println(io)
end

end
