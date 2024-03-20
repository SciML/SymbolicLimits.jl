module SymbolicLimits

export limit

include("limits.jl")
const _AUTO = :__0x6246e6c6ad56df8113c7eb80b2a84080__

"""
    limit(expr, var, h[, side::Symbol])

Compute the limit of `expr` as `var` approaches `h` and return `(limit, assumptions)`. If
all the `assumptions` are true, then the returned `limit` is correct.

`side` indicates the direction from which `var`` approaches `h`. It may be one of `:left`,
`:right`, or `:both`. If `side` is `:both` and the two sides do not align, an error is
thrown. Side defaults to `:both` for finite `h`, `:left` for `h = Inf`, and `:right` for
`h = -Inf`.
"""
function limit end

limit(expr, var::BasicSymbolic, h) = limit(expr, var, h, _AUTO)
limit(expr, var::BasicSymbolic, h, side::Symbol) = expr
function limit(expr::BasicSymbolic, var::BasicSymbolic, h, side::Symbol)
    side ∈ (:left, :right, :both, _AUTO) || throw(ArgumentError("Unknown side: $side"))
    if isinf(h)
        if signbit(h)
            side ∈ (:right, _AUTO) || throw(ArgumentError("Cannot take limit on the $side side of -Inf"))
            limit_inf(SymbolicUtils.substitute(expr, Dict(var => -var), var))
        else
            side ∈ (:left, _AUTO) || throw(ArgumentError("Cannot take limit on the $side side of Inf"))
            limit_inf(expr, var)
        end
    else
        if side == :left
            limit_inf(SymbolicUtils.substitute(expr, Dict(var => h-1/var)), var)
        elseif side == :right
            limit_inf(SymbolicUtils.substitute(expr, Dict(var => h+1/var)), var)
        else @assert side ∈ (:both, _AUTO)
            left = limit_inf(SymbolicUtils.substitute(expr, Dict(var => h-1/var), var, h))
            right = limit_inf(SymbolicUtils.substitute(expr, Dict(var => h+1/var), var, h))
            zero_equivalence(left-right) || throw(ArgumentError("The left sided limit ($left) and right sided limit ($right) are not equal"))
            right[1], union(left[2], right[2])
        end
    end
end

end
