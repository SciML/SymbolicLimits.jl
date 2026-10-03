using SymbolicLimits, SymbolicUtils
using Test

@syms u::Real

# lim_{u→0+} log(u) = -∞
@test limit(log(u), u, 0, :right)[1] === -Inf

# lim_{u→∞} log(1/u) = lim_{u→∞} (-log(u)) = -∞
@test limit(log(1 / u), u, Inf)[1] === -Inf

# lim_{u→0+} 1/log(u) = 1/(-∞) = 0
@test limit(1 / log(u), u, 0, :right)[1] == 0

# lim_{u→∞} log(1 + 1/u) = log(1) = 0
@test limit(log(1 + 1 / u), u, Inf)[1] == 0
