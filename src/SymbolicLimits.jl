module SymbolicLimits

export limit
module Internals
    include("limits.jl")
    const _AUTO = :__0x6246e6c6ad56df8113c7eb80b2a84080__
end

"""
    limit(expr, var, h[, side::Symbol])

Compute the limit of `expr` as `var` approaches `h`.

`side` indicates the direction from which `var`` approaches `h`. It may be one of `:left`,
`:right`, or `:both`. If `side` is `:both` and the two sides do not align, an error is
thrown. Side defaults to `:both` for finite `h`, `:left` for `h = Inf`, and `:right` for
`h = -Inf`.
"""
function limit end

limit(expr, var::Internals.BasicSymbolic, h) = limit(expr, var, h, Internals._AUTO)
function limit(expr, var::Internals.BasicSymbolic, h, side::Symbol)
    side ∈ (:left, :right, :both, Internals._AUTO) || throw(ArgumentError("Unknown side: $side"))
    if isinf(h)
        if signbit(h)
            side ∈ (:right, Internals._AUTO) || throw(ArgumentError("Cannot take limit on the $side side of -Inf"))
            Internals.limit(SymbolicUtils.substitute(expr, Dict(var => -var), var))
        else
            side ∈ (:left, Internals._AUTO) || throw(ArgumentError("Cannot take limit on the $side side of Inf"))
            Internals.limit(expr, var)
        end
    else
        if side == :left
            Internals.limit(SymbolicUtils.substitute(expr, Dict(var => h-1/var), var, h))
        elseif side == :right
            Internals.limit(SymbolicUtils.substitute(expr, Dict(var => h+1/var), var, h))
        else @assert side ∈ (:both, Internals._AUTO)
            left = Internals.limit(SymbolicUtils.substitute(expr, Dict(var => h-1/var), var, h))
            right = Internals.limit(SymbolicUtils.substitute(expr, Dict(var => h+1/var), var, h))
            Internals.zero_equivalence(left-right) || throw(ArgumentError("The left sided limit ($left) and right sided limit ($right) are not equal"))
            right
        end
    end
end

end
