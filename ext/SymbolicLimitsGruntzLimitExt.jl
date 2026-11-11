module SymbolicLimitsGruntzLimitExt

using SymbolicLimits: SymbolicLimits
using GruntzLimit: gruntz_limit, GruntzError

const _CONSTANT_NAMES = ("π", "ℯ")

mutable struct _Scan
    unsupported::Bool
    params::Vector{Any}
end

_unsupported(n::Number) = n isa AbstractFloat && !(n isa Float64)

function _walk(expr, var, state::_Scan)
    if expr isa Number
        state.unsupported |= _unsupported(expr)
    elseif expr isa SymbolicLimits.BasicSymbolic
        if SymbolicLimits.issym(expr)
            if expr === var
                return
            end
            if string(expr.name) in _CONSTANT_NAMES
                state.unsupported = true
                return
            end
            any(p -> p === expr, state.params) || push!(state.params, expr)
        elseif SymbolicLimits.isconstant(expr)
            value = SymbolicLimits.unwrap_const(expr)
            value isa Number && (state.unsupported |= _unsupported(value))
        elseif SymbolicLimits.isterm(expr) || SymbolicLimits.isaddmul(expr) ||
                SymbolicLimits.isdiv(expr)
            for arg in SymbolicLimits.arguments(expr)
                _walk(arg, var, state)
            end
        else
            state.unsupported = true
        end
    end
    return
end

_norm(value) = value isa SymbolicLimits.BasicSymbolic && SymbolicLimits.isconstant(value) ?
    SymbolicLimits.unwrap_const(value) : value

function _agrees(value, param, specialized)
    candidate = value isa SymbolicLimits.BasicSymbolic ?
        SymbolicLimits.SymbolicUtils.substitute(value, Dict(param => 0)) : value
    return isequal(_norm(candidate), _norm(specialized))
end

function SymbolicLimits._gruntz_limit(expr, var, h, side::Symbol)
    string(var.name) in _CONSTANT_NAMES && return nothing
    dir = side == :left ? :- : side == :right ? :+ : :both
    state = _Scan(false, Any[])
    _walk(expr, var, state)
    _walk(h, var, state)
    state.unsupported && return nothing
    value = try
        gruntz_limit(expr, var, h; dir)
    catch err
        err isa GruntzError || rethrow()
        err.kind === :nolimit && throw(ArgumentError(err.msg))
        return nothing
    end
    for param in state.params
        specialized = try
            gruntz_limit(expr, var, h; dir, signs = (param => :zero,))
        catch err
            err isa GruntzError || rethrow()
            return nothing
        end
        _agrees(value, param, specialized) || return nothing
    end
    return value, Set{Any}()
end

end
