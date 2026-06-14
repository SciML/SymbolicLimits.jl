using SymbolicLimits, SymbolicUtils
using Test

let
    @syms x::Real h::Real
    @test limit(exp(x + exp(-x)) - exp(x), x, Inf)[1] == 1
    @test limit(x^7 / exp(x), x, Inf)[1] == 0
    @test_broken limit((arccos(x + h) - arccos(x)) / h, h, 0, :right)[1] == _unknown_
    @test_broken limit(1 / (x^log(log(log(log(1 / x - 1))))), x, 0, :right)[1] == Inf
    @test_broken limit((erf(x - exp(-exp(x))) - erf(x)) * exp(exp(x)) * exp(x^2), x, Inf)[1] ≈
        -2 / √π
    @test_broken limit(exp(csc(x)) / exp(cot(x)), x, 0)[1] == 1
    @test_broken limit(exp(x) * (sin(1 / x + exp(-x)) - sin(1 / x)), x, Inf)[1] == 1
    @test limit(log(log(x * exp(x * exp(x)) + 1)) - exp(exp(log(log(x)) + 1 / x)), x, Inf)[1] ==
        0
    @test limit(2exp(-x) / exp(-x), x, 0)[1] == 2
    @test_broken limit(exp(csc(x)) / exp(cot(x)), x, 0)[1] == 1
end
