using SymbolicLimits, SymbolicUtils
using Test

@syms x
limit(x + 1, x, 0)[1] == 1
limit(x, x, 0)[1] == 0
@test_throws ArgumentError limit(1 / x, x, 0)
@test limit(1 / x, x, 0, :left)[1] == -Inf
@test limit(1 / x, x, 0, :right)[1] == Inf
