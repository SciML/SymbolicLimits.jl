using SymbolicLimits, SymbolicUtils, GruntzLimit
using SymbolicUtils: simplify, unwrap_const
using SpecialFunctions: erf
using Test

@syms x::Real h::Real a::Real

@testset "GruntzLimit extension" begin
    @test !isnothing(Base.get_extension(SymbolicLimits, :SymbolicLimitsGruntzLimitExt))

    @testset "limits beyond the native algorithm" begin
        @test limit(sin(x) / x, x, 0)[1] == 1
        @test limit(sin(x) / x, x, Inf)[1] == 0
        @test limit((tan(x) - sin(x)) / x^3, x, 0)[1] == 1 // 2
        @test limit(x * sin(1 / x), x, Inf)[1] == 1
        @test limit(sin(x)^2 / (1 + cos(x)), x, π) == (2, Set{Any}())
        @test isequal(limit(sin(a * x) / x, x, 0)[1], a)
        @test limit(exp(x) * (sin(1 / x + exp(-x)) - sin(1 / x)), x, Inf)[1] == 1
        @test limit(exp(csc(x)) / exp(cot(x)), x, 0)[1] == 1
        @test limit(1 / (x^log(log(log(log(1 / x - 1))))), x, 0, :right)[1] == Inf
        v = limit((erf(x - exp(-exp(x))) - erf(x)) * exp(exp(x)) * exp(x^2), x, Inf)[1]
        @test Float64(unwrap_const(simplify(v))) ≈ -2 / √π
    end

    @testset "removable singularities" begin
        @test limit((x^2 - 1) / (x - 1), x, 1)[1] == 2
        @test limit((x^3 - 8) / (x^2 - 4), x, 2)[1] == 3
        @test limit((x^2 - 4) / (x^2 - 5x + 6), x, 2)[1] == -4
    end

    @testset "agrees with the native results" begin
        @test limit(exp(x + exp(-x)) - exp(x), x, Inf)[1] == 1
        @test limit(x^7 / exp(x), x, Inf)[1] == 0
        @test limit(x * exp(x), x, -Inf)[1] == 0
        @test limit(1 / x, x, 0, :left)[1] == -Inf
        @test limit(1 / x, x, 0, :right)[1] == Inf
        @test limit(x + 1, x, 0)[1] == 1
    end

    @testset "limits that do not exist" begin
        @test_throws ArgumentError limit(1 / x, x, 0)
        @test_throws ArgumentError limit(sin(x), x, Inf)
        @test_throws ArgumentError limit(sin(1 / x), x, 0)
    end

    @testset "argument validation is unchanged" begin
        @test_throws ArgumentError limit(x, x, 0, :up)
        @test_throws ArgumentError limit(x^2, x, Inf, :right)
        @test_throws ArgumentError limit(x^2, x, -Inf, :left)
    end

    @testset "undecided limits fall back to the native algorithm" begin
        # The native algorithm reports whichever of sin/cos it meets first, which
        # depends on term ordering and differs across Julia and SymbolicUtils versions.
        @test_throws r"Not implemented: (sin|cos)" limit(sin(x)^2 + cos(x)^2, x, Inf)
    end
end
