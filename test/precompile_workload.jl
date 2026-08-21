using SymbolicLimits, SymbolicUtils
using Test

@syms x::Real

@testset "Precompile workload" begin
    @test limit(x + 1, x, 0)[1] == 1
    @test limit(1 / x, x, 0, :left)[1] == -Inf
    @test limit(1 / x, x, 0, :right)[1] == Inf
    @test limit(x^2 / exp(x), x, Inf)[1] == 0
    @test limit(x * exp(x), x, -Inf)[1] == 0
end
