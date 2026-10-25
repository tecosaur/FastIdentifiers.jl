# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module AboutExt

using FastIdentifiers: AbstractIdentifier
using PackedParselets: segments, Segment, SegmentOptions
using About
using StyledStrings: @styled_str as @S_str, face!
using Base: AnnotatedString

const Mark = @NamedTuple{kind::Symbol, col::Int, text::String, face::Symbol}

# A row of a type's drawn layout: its marks, then its name, the choices it names, and notes
struct Row
    name::String
    depth::Int
    choices::Vector{String}
    marks::Vector{Mark}
    notes::Vector{AnnotatedString{String}}
end

Row(name::String, depth::Int) = Row(name, depth, [], [], [])

function About.memorylayout(io::IO, ::Type{T}) where {T <: AbstractIdentifier}
    isprimitivetype(T) && hasmethod(segments, (Type{T},)) || return invoke(About.memorylayout, Tuple{IO, DataType}, io, T)
    rows = [Row("", 0)]
    layoutrows!(rows, 1, segments(T), 0)
    use = bituse(segments(T))
    print(io, "\n\n ")
    for bit in 1:8 * sizeof(T)
        bit > 1 && bit % 8 == 1 && print(io, ' ')
        u = get(use, bit, :never)
        print(io, if u === :always '◼' elseif u === :sometimes '◩' else S"{shadow:□}" end)
    end
    namecol = 2 + maximum(row -> maximum(m -> m.col + textwidth(m.text), row.marks, init = 0), rows)
    for (; name, depth, choices, marks, notes) in rows
        print(io, "\n ")
        at = 0
        for (; col, text, face) in sort(marks, by = m -> m.col)
            print(io, ' ' ^ (col - at), S"{$face:$text}")
            at = col + textwidth(text)
        end
        title = join(filter(!isempty, [name, join(choices, ", ")]), ": ")
        isempty(title) && isempty(notes) && continue
        print(io, ' ' ^ (namecol - at + 2 * depth), title)
        listed = join(notes, ", ")
        isempty(notes) || print(io, if isempty(title) "" else " " end, S"{shadow:(}$listed{shadow:)}")
    end
end

# A column a bit, and a space between bytes
column(bit::Int) = bit + bit ÷ 8
width(pos::Int, nbits::Int) = column(pos + nbits - 1) + 1 - column(pos)

bracket(label::String, w::Int, edge::Char = '─') =
    let left = (w - 2 - textwidth(label)) ÷ 2
        string('└', edge ^ left, label, edge ^ (w - 2 - textwidth(label) - left), '┘')
    end

isanonymous(s::Segment) = startswith(string(s.label), '#')

# Lay out `layout` from bit `pos` in row `r` of `rows`; return the bit after it. Each choice
# adds rows for its options, joined to the bits selecting them and a level deeper than
# the row naming it, and echoes the segments following it there with ditto marks.
# Segments are named with `mark` appended, and echoed in the rows `echo`.
function layoutrows!(rows::Vector{Row}, r::Int, layout, pos::Int; mark::String = "", echo::Vector{Int} = Int[])
    row = rows[r]
    draw!(into, kind, col, text, face = :shadow) = push!(into.marks, (; kind, col, text, face))
    function box!(s::Segment)
        w = width(pos, s.nbits)
        face = About.FACE_CYCLE[mod1(count(m -> m.kind === :box, row.marks) + 1, length(About.FACE_CYCLE))]
        name = string(if isanonymous(s) s.kind else s.label end, mark)
        # A name too long for its box shows its initial, if even that fits
        shown = if textwidth(name) <= w - 2 name elseif w > 2 string(first(name)) else "" end
        nstrings = if s.kind === :choice && !isempty(s.desc) count(" | ", s.desc) + 1 else 0 end
        note = if nstrings > 0 "$name, $nstrings options" else name end
        note == shown || push!(row.notes, S"{$face:$note}")
        draw!(row, :box, column(pos), bracket(shown, w), face)
        # Centred under the label, or the box if unlabelled
        from, n = if isempty(shown); (0, w) else (1 + (w - 2 - textwidth(shown)) ÷ 2, textwidth(shown)) end
        ditto = if iseven(n) "╶╴" else "─" end
        foreach(ri -> draw!(rows[ri], :ditto, column(pos) + from + (n - textwidth(ditto)) ÷ 2, ditto, face), echo)
    end
    arm = nothing
    for (i, s) in enumerate(layout)
        if s isa Segment
            if s.kind === :arm
                w = width(pos, s.nbits)
                draw!(row, :selector, column(pos), if w == 1 "╦" else string("╘╦", '═' ^ max(w - 3, 0), if w > 2 "╛" else "" end) end)
                isanonymous(s) || push!(row.choices, string(s.label, mark))
                arm = pos
            else
                s.nbits > 0 && box!(s)
                arm = nothing
            end
            pos += s.nbits
        elseif isnothing(arm)
            pos = layoutrows!(rows, r, something(first(s.options)), pos; mark = "?", echo)
        else
            stop = pos + maximum(opt -> length(bituse(something(opt, Segment[]))), s.options)
            optrows = Int[]
            for (opt, names) in alike(s)
                push!(rows, Row(join(if length(names) > 4; [names[1:2]; "… $(length(names) - 3) more"; names[end]] else names end, ", "),
                                row.depth + 1))
                push!(optrows, length(rows))
                optstop = layoutrows!(rows, length(rows), opt, pos)
                optstop < stop && draw!(rows[end], :span, column(optstop), bracket("", width(optstop, stop - optstop), '╌'))
            end
            # Branches leave from the selector's `╦`, a column in when it brackets two or more bits
            w = width(arm, pos - arm)
            for ri in r+1:last(optrows)
                branch = if ri ∉ optrows "║"
                else string(if ri == last(optrows) '╚' else '╠' end, '═' ^ max(w - 3, 0), if w > 2 "▸" else "" end) end
                draw!(rows[ri], :link, column(arm) + Int(w > 1), branch)
            end
            stop > pos && draw!(row, :span, column(pos), bracket("", width(pos, stop - pos), '╌'))
            return layoutrows!(rows, r, layout[i+1:end], stop; mark, echo = [echo; optrows])
        end
    end
    pos
end

# The options of `s` as they're drawn, with the names of those drawn alike: options alike
# but for their segments' widths, or lacking only later segments, drawn at the widest.
function alike(s::SegmentOptions)
    # Zero-width segments aren't drawn, so options differing only in them look alike
    isdrawn(x) = x isa SegmentOptions || x.nbits > 0
    shape(l) = if !isnothing(l)
        [if x isa Segment; (x.kind, if isanonymous(x) nothing else x.label end) else (x.names, map(shape, x.options)) end
         for x in l if isdrawn(x)]
    end
    extends(a, b) = length(a) >= length(b) && a[1:length(b)] == b
    function widest(a, b)
        isnothing(a) && return b
        long, short = if extends(shape(a), shape(b)); (a, b) else (b, a) end
        others = filter(isdrawn, short)
        map(long) do x
            isdrawn(x) && !isempty(others) || return x
            y = popfirst!(others)
            if x isa Segment
                (; x..., nbits = max(x.nbits, y.nbits), desc = if x.desc == y.desc x.desc else "" end)
            else
                SegmentOptions(map(widest, x.options, y.options), x.names)
            end
        end
    end
    groups = []
    for (k, opt) in enumerate(s.options)
        lead = if !isnothing(opt) && first(opt) isa Segment && first(opt).kind === :literal first(opt).shortform end
        name = string(something(s.names[k], lead, if isnothing(opt) "none" else "#$k" end))
        opt = something(opt, Segment[])
        g = findfirst(((a, _),) -> extends(shape(a), shape(opt)) || extends(shape(opt), shape(a)), groups)
        if isnothing(g)
            push!(groups, (opt, [name]))
        else
            groups[g] = (widest(first(groups[g]), opt), push!(last(groups[g]), name))
        end
    end
    groups
end

# How each bit of `layout` is used across the values it holds: `:always`, `:sometimes`, or `:never`
function bituse(layout)
    use = Symbol[]
    for s in layout
        if s isa Segment
            append!(use, fill(:always, s.nbits))
            continue
        end
        options = [if isnothing(opt) Symbol[] else bituse(opt) end for opt in s.options]
        for i in 1:maximum(length, options)
            at = [get(o, i, :never) for o in options]
            push!(use, if allequal(at) first(at) else :sometimes end)
        end
    end
    use
end

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
