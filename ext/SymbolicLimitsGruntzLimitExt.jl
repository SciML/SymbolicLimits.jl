module SymbolicLimitsGruntzLimitExt

using SymbolicLimits: SymbolicLimits
using GruntzLimit: gruntz_limit, GruntzError

function SymbolicLimits._gruntz_limit(expr, var, h, side::Symbol)
    dir = side == :left ? :- : side == :right ? :+ : :both
    value = try
        gruntz_limit(expr, var, h; dir)
    catch err
        err isa GruntzError || rethrow()
        err.kind === :nolimit && throw(ArgumentError(err.msg))
        return nothing
    end
    return value, Set{Any}()
end

end
