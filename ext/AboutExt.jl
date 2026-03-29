# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module AboutExt

using FastIdentifiers: AbstractIdentifier
using PackedParselets: segments
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

function About.memorylayout(io::IO, id::AbstractIdentifier)
    isprimitivetype(typeof(id)) && hasmethod(segments, (Type{typeof(id)},)) || invoke(About.memorylayout, Tuple{IO, DataType}, io, id)
    sfields = segments(typeof(id))
    allsegs = segments(id)
    bstr = AnnotatedString(bitstring(id))
    lastbit = 0
    for (i, (; nbits)) in enumerate(sfields)
        face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
        face!(bstr, lastbit + 1:lastbit + nbits, face)
        lastbit += nbits
    end
    if lastbit < ncodeunits(bstr)
        face!(bstr, lastbit + 1:ncodeunits(bstr), :shadow)
    end
    if get(io, :compact, false) == true
        return print(io, bstr)
    end
    print(io, "\n ", bstr, "\n ")
    for (i, (; nbits)) in enumerate(sfields)
        face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
        if nbits == 1
            print(io, S"{$face:╨}")
        elseif nbits == 2
            print(io, S"{$face:└┘}")
        else
            nleft = (nbits - 2 - ndigits(i)) ÷ 2
            nright = (nbits - 2 - ndigits(i)) - nleft
            print(io, S"{$face:└$('─'^nleft)$(i)$('─'^nright)┘}")
        end
    end
    print(io, S"\n {bold:=} ")
    for (i, str) in segments(id)
        if i == 0
            print(io, S"{light:$str}")
        else
            face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
            print(io, S"{$face:$str}")
        end
    end
    println(io)
end

function About.elaboration(io::IO, id::AbstractIdentifier)
    isprimitivetype(typeof(id)) && hasmethod(segments, (Type{typeof(id)},)) || invoke(About.elaboration, Tuple{IO, DataType}, io, id)
    for (i, (; kind, label, desc)) in enumerate(segments(typeof(id)))
        face = About.FACE_CYCLE[mod1(i, length(About.FACE_CYCLE))]
        print(io, S"\n {$face:• $label}: $desc")
    end
    println(io)
end

end
