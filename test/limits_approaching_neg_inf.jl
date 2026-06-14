using SymbolicLimits, SymbolicUtils
using Test

@syms x::Real
# x * exp(x) -> 0 as x -> -Inf because exp(x) dominates
@test limit(x * exp(x), x, -Inf)[1] == 0
# exp(x) -> 0 as x -> -Inf
@test limit(exp(x), x, -Inf)[1] == 0
# x^2 * exp(x) -> 0 as x -> -Inf
@test limit(x^2 * exp(x), x, -Inf)[1] == 0
