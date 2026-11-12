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

    @testset "native results are not changed by the extension" begin
        @test limit(x + 1.0e-100, x, 0)[1] == 1.0e-100
        c = big"1e-1000"
        @test limit(c * x, x, Inf)[1] == Inf
        @test limit(x + c, x, 0)[1] ≈ c
    end

    @testset "generic parameter answers are not returned as unconditional" begin
        @test_throws ErrorException limit(sin(x) / (a + x), x, 0)
        expr = SymbolicUtils.substitute(sin(x) / (a + x), Dict(a => 0))
        @test limit(expr, x, 0)[1] == 1
        @test_throws ErrorException limit(sin(x) / (a - 1 + x), x, 0)
        specialized = SymbolicUtils.substitute(sin(x) / (a - 1 + x), Dict(a => 1))
        @test limit(specialized, x, 0)[1] == 1
    end

    @testset "tiny constants are not dropped on fallback expressions" begin
        @test_throws ErrorException limit(sin(x) + 1.0e-100, x, 0)
        @test Float64(limit(sin(x) + 1.0e-50, x, 0)[1]) ≈ 1.0e-50
    end

    @testset "symbol identity is preserved" begin
        @syms π::Real
        r = limit(π * x, x, 1)[1]
        @test r === π
        @test isequal(unwrap_const(SymbolicUtils.substitute(r, Dict(π => 3))), 3)
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
