module SymbolicLimitsGruntzLimitExt

using SymbolicLimits: SymbolicLimits
using GruntzLimit: gruntz_limit, GruntzError

const _CONSTANT_NAMES = ("π", "ℯ")

# GruntzLimit evaluates numerically, so inexact constants and free parameters can make its
# answer conditional or wrong. Only exact constants and the limit variable are accepted.
_exact(n::Number) = n isa Integer || n isa Rational || (n isa Real && isinf(n))

function _supported(expr, var)
    if expr isa Number
        return _exact(expr)
    elseif expr isa SymbolicLimits.BasicSymbolic
        if SymbolicLimits.issym(expr)
            return expr === var
        elseif SymbolicLimits.isconstant(expr)
            value = SymbolicLimits.unwrap_const(expr)
            return value isa Number && _exact(value)
        elseif SymbolicLimits.isterm(expr) || SymbolicLimits.isaddmul(expr) ||
                SymbolicLimits.isdiv(expr)
            return all(arg -> _supported(arg, var), SymbolicLimits.arguments(expr))
        end
    end
    return false
end

_big(v) = v isa Real ? BigFloat(v) : v

function _numeval(expr, var, h)
    expr isa Number && return _big(expr)
    if expr isa SymbolicLimits.BasicSymbolic
        if SymbolicLimits.issym(expr)
            return expr === var ? _big(h) : nothing
        elseif SymbolicLimits.isconstant(expr)
            value = SymbolicLimits.unwrap_const(expr)
            return value isa Number ? _big(value) : nothing
        elseif SymbolicLimits.isterm(expr) || SymbolicLimits.isaddmul(expr) ||
                SymbolicLimits.isdiv(expr)
            args = map(arg -> _numeval(arg, var, h), SymbolicLimits.arguments(expr))
            any(isnothing, args) && return nothing
            return try
                SymbolicLimits.operation(expr)(args...)
            catch
                nothing
            end
        end
    end
    return nothing
end

_norm(value) = value isa SymbolicLimits.BasicSymbolic && SymbolicLimits.isconstant(value) ?
    SymbolicLimits.unwrap_const(value) : value

# The backend treats values below 1e-60 as zero, so a zero answer can hide a tiny nonzero
# limit. Such a zero is trusted only when no exact constant (or finite limit point) is of
# extreme magnitude and the expression does not evaluate to a nonzero value at the limit
# point, checked at a precision far above the backend's resolution.
const _EVAL_PRECISION = 4096

_extreme(n::Real) = isfinite(n) && !iszero(n) && (abs(n) < 1 // 10^6 || abs(n) > 10^6)
_extreme(n) = false

function _extreme_constant(expr)
    if expr isa Number
        return _extreme(expr)
    elseif expr isa SymbolicLimits.BasicSymbolic
        if SymbolicLimits.isconstant(expr)
            return _extreme(SymbolicLimits.unwrap_const(expr))
        elseif SymbolicLimits.isterm(expr) || SymbolicLimits.isaddmul(expr) ||
                SymbolicLimits.isdiv(expr)
            return any(_extreme_constant, SymbolicLimits.arguments(expr))
        end
    end
    return false
end

function _unverifiable_zero(value, expr, var, h)
    result = _norm(value)
    (result isa Number && iszero(result)) || return false
    (_extreme_constant(expr) || _extreme_constant(h)) && return true
    (h isa Number && isfinite(h)) || return false
    point = setprecision(() -> _numeval(expr, var, h), BigFloat, _EVAL_PRECISION)
    return point isa Number && isfinite(point) && !iszero(point)
end

function SymbolicLimits._gruntz_limit(expr, var, h, side::Symbol)
    string(var.name) in _CONSTANT_NAMES && return nothing
    (_supported(expr, var) && _supported(h, var)) || return nothing
    dir = side == :left ? :- : side == :right ? :+ : :both
    value = try
        gruntz_limit(expr, var, h; dir)
    catch err
        err isa GruntzError || rethrow()
        err.kind === :nolimit && throw(ArgumentError(err.msg))
        return nothing
    end
    _unverifiable_zero(value, expr, var, h) && return nothing
    return value, Set{Any}()
end

end
