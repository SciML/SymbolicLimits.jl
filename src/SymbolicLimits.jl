module SymbolicLimits

using PrecompileTools: @compile_workload, @setup_workload
using SymbolicUtils: @syms

export limit

include("limits.jl")
const _AUTO = :__0x6246e6c6ad56df8113c7eb80b2a84080__

"""
    limit(expr, var, h[, side::Symbol]) -> Tuple

Compute the symbolic limit of `expr` as `var` approaches `h`.

# Arguments

  - `expr`: A scalar `SymbolicUtils.BasicSymbolic` expression, or a scalar value.
  - `var`: The symbolic variable that approaches `h`.
  - `h`: The finite limit point, `Inf`, or `-Inf`.
  - `side::Symbol`: The optional direction of approach. Use `:left`, `:right`, or `:both`.
    When omitted, the function computes a two-sided finite limit and uses the only meaningful
    direction for `Inf` and `-Inf`.

# Returns

A tuple `(value, assumptions)`, where `value` is the computed limit and `assumptions` is a
`Set` of symbolic propositions used by the zero-equivalence heuristic. The result is valid
when every proposition in `assumptions` holds.

# Throws

When [GruntzLimit.jl](https://github.com/jverzani/GruntzLimit.jl) is loaded
(`using GruntzLimit`), this package's algorithm runs first. When it does not produce a
result, GruntzLimit is consulted, which adds trigonometric, hyperbolic, inverse and
special functions, non-integer powers and symbolic limit points. The `assumptions` set
is then empty when GruntzLimit's answer does not depend on generic assumptions about
symbolic parameters. A limit GruntzLimit proves does not exist throws `ArgumentError`.
When a generic GruntzLimit answer would depend on such assumptions, or the input
contains a numeric constant other than `Float64`, the extension declines and the error
of this package's algorithm is thrown.

Throws `ArgumentError` when `side` is not `:left`, `:right`, or `:both`, or when a direction
is incompatible with an infinite limit point. A two-sided finite limit throws `ArgumentError`
when its one-sided values differ.

# Examples

```jldoctest
julia> using SymbolicLimits, SymbolicUtils

julia> @syms x::Real
(x,)

julia> limit(x^2 / exp(x), x, Inf)[1]
0

julia> limit(1 / x, x, 0, :left)[1]
-Inf
```
"""
function limit end

# Extended by the GruntzLimit extension. Returns `(value, assumptions)`, or `nothing` to
# decline, in which case the error of the algorithm in this package is thrown.
function _gruntz_limit end

limit(expr, var::BasicSymbolic, h) = limit(expr, var, h, _AUTO)
limit(expr, var::BasicSymbolic, h, side::Symbol) = expr
function limit(expr::BasicSymbolic, var::BasicSymbolic, h, side::Symbol)
    side ∈ (:left, :right, :both, _AUTO) || throw(ArgumentError("Unknown side: $side"))
    if h isa Number && isinf(h)
        side ∈ (signbit(h) ? (:right, _AUTO) : (:left, _AUTO)) ||
            throw(ArgumentError("Cannot take limit on the $side side of $h"))
    end
    outcome = try
        (:ok, _native_limit(expr, var, h, side))
    catch err
        err isa InterruptException && rethrow()
        (:err, err)
    end
    outcome[1] === :ok && return outcome[2]
    if !isempty(methods(_gruntz_limit))
        result = Base.invokelatest(_gruntz_limit, expr, var, h, side)
        result === nothing || return result
    end
    throw(outcome[2])
end

function _native_limit(expr::BasicSymbolic, var::BasicSymbolic, h, side::Symbol)
    return if isinf(h)
        if signbit(h)
            side ∈ (:right, _AUTO) ||
                throw(ArgumentError("Cannot take limit on the $side side of -Inf"))
            limit_inf(SymbolicUtils.substitute(expr, Dict(var => -var)), var)
        else
            side ∈ (:left, _AUTO) ||
                throw(ArgumentError("Cannot take limit on the $side side of Inf"))
            limit_inf(expr, var)
        end
    else
        if side == :left
            limit_inf(SymbolicUtils.substitute(expr, Dict(var => h - 1 / var)), var)
        elseif side == :right
            limit_inf(SymbolicUtils.substitute(expr, Dict(var => h + 1 / var)), var)
        else
            @assert side ∈ (:both, _AUTO)
            left = limit_inf(SymbolicUtils.substitute(expr, Dict(var => h - 1 / var)), var)
            right = limit_inf(SymbolicUtils.substitute(expr, Dict(var => h + 1 / var)), var)
            zero_equivalence(left[1] - right[1], left[2]) ||
                throw(ArgumentError("The left sided limit ($(left[1])) and right sided limit ($(right[1])) are not equal"))
            right[1], union(left[2], right[2])
        end
    end
end

include("precompilation.jl")

end
