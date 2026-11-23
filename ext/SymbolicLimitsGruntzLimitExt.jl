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

# Values produced during evaluation below 1e-60 are snapped to zero by the backend, so a
# reported zero is suspect when the expression evaluates to a nonzero finite value at the
# limit point.
function _suspicious_zero(value, expr, var, h)
    result = _norm(value)
    (result isa Number && iszero(result)) || return false
    (h isa Number && isfinite(h)) || return false
    point = _numeval(expr, var, h)
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
    _suspicious_zero(value, expr, var, h) && return nothing
    return value, Set{Any}()
end

end
