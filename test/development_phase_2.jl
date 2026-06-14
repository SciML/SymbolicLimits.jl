using SymbolicLimits, SymbolicUtils
using Test

let limit = ((args...) -> SymbolicLimits.limit_inf(args...)[1]),
        get_series_term = ((args...) -> SymbolicLimits.get_series_term(args..., Set{Any}())),
        mrv_join = ((args...) -> SymbolicLimits.mrv_join(args..., Set{Any}())),
        zero_equivalence = ((args...) -> SymbolicLimits.zero_equivalence(args..., Set{Any}())),
        signed_limit = ((args...) -> SymbolicLimits.signed_limit_inf(args..., Set{Any}()))

    @syms x::Real ω::Real
    @test limit(-1 / x, x) === 0
    @test limit(-x / log(x), x) === -Inf
    @test unwrap_const(only(mrv_join(x)([exp(x)], [x])) - exp(x)) === 0
    @test signed_limit(exp(exp(-x)) - 1, x) == (0, 1)
    @test limit(exp(x + exp(-x)) - exp(x), x) == 1
    @test limit(x^7 / exp(x), x) == 0
    @test limit(x^70000 / exp(x), x) == 0
    @test !zero_equivalence(get_series_term(log(x / ω), ω, -x, 0) - log(x / ω))
    @test get_series_term(1 / ω, ω, -x, 0) == 0
    @test limit(x^2 / (x^2 + log(x)), x) == 1
    @test get_series_term(exp(ω), ω, -x, 2) == 1 / 2
    @test zero_equivalence(1.0 - exp(-x + exp(log(x)))) # sus b.c. domain is not R, but okay
    @test limit(x + log(x) - exp(exp(1 / x + log(log(x)))), x) == 0
    @test limit(log(log(x * exp(x * exp(x)) + 1)) - exp(exp(log(log(x)) + 1 / x)), x) == 0
end
