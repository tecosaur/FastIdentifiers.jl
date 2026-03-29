# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

module PrettyPrintExt

using FastIdentifiers: AbstractIdentifier, MalformedIdentifier, ChecksumViolation, purl, shortcode

using StyledStrings: @styled_str as @S_str

function Base.showerror(io::IO, @nospecialize(ex::MalformedIdentifier{T})) where {T}
    input = string(ex.input)
    header = S"Malformed {blue:$T} identifier:"
    if iszero(ex.position)
        print(io, header, S" {emphasis:$input} $(ex.problem)")
    else
        pre, post = input[1:prevind(input, ex.position)], input[ex.position:end]
        print(io, header, S"\n\n   {light:$pre}{error,bold:$post}")
        print(io, '\n', ' '^(textwidth(pre) + 3), S"{error:└─╴}$(ex.problem)")
    end
end

function Base.showerror(io::IO, @nospecialize(ex::ChecksumViolation{T})) where {T}
    input = string(ex.id)
    header = S"Checksum violation in {blue:$T} identifier:"
    msg = S"expected {success:$(ex.expected)}, got {error:$(ex.provided)}"
    if iszero(ex.position)
        print(io, header, S" {emphasis:$input} $msg")
    else
        pre, post = input[1:prevind(input, ex.position)], input[ex.position:end]
        print(io, header, S"\n\n   {light:$pre}{error,bold:$post}")
        print(io, '\n', ' '^(textwidth(pre) + 3), S"{error:└─╴}$msg")
    end
end

function Base.show(io::IO, ::MIME"text/plain", id::AbstractIdentifier)
    label = String(nameof(typeof(id)))
    lowerlabel = lowercase(label)
    url = purl(id)
    idstr = shortcode(id)
    prefix = if ':' in idstr; lowerlabel * ':' else lowerlabel end
    if startswith(lowercase(idstr), prefix)
        idstr = idstr[ncodeunits(prefix)+1:end]
    end
    if endswith(label, "ID")
        idstr = chopprefix(idstr, chopsuffix(label, "ID"))
    end
    if get(io, :typeinfo, Nothing) != typeof(id)
        print(io, S"{bold:$label:}")
    end
    if isnothing(url)
        print(io, S"$idstr")
    else
        print(io, S"{link=$url:$idstr}")
    end
end

end
