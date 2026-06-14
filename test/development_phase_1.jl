using SymbolicLimits, SymbolicUtils
using Test

let
    @syms x::Real y::Real ω::Real
    @test SymbolicLimits.zero_equivalence(x * (x + y) - x - x * y + x - x * (x + 1) + x, Set{Any}())
    @test_broken SymbolicLimits.zero_equivalence(exp((x + 1) * x - x * x - x) - 1, Set{Any}())

    @test SymbolicLimits.get_leading_exponent(x^2, x, nothing, Set{Any}()) == 2
    @test SymbolicLimits.get_series_term(log(exp(x)), x, nothing, 1, Set{Any}()) ==
        1
    @test SymbolicLimits.get_series_term(log(exp(x)), x, -x, 0, Set{Any}()) == 0
    @test SymbolicLimits.get_series_term(log(exp(x)), x, nothing, 2, Set{Any}()) ==
        0

    # F = exp(x+exp(-x))-exp(x)
    # Ω = {exp(x + exp(-x)), exp(x), exp(-x)}
    # Topo-sort Ω by containment
    # Take a smallest element of Ω and call it ω.
    # ω = exp(-x)
    # From largest to smallest, rewrite elements f ∈ Ω in terms of ω in the form
    # Assume f is of the form exp(s) and ω is of the form exp(t).
    # -- Recursively compute c = lim(s/t)
    # f = f*ω^c/ω^c = exp(log(f)-c*log(ω))*ω^c = exp(s-ct)*ω^c

    # f = exp(x+exp(-x))
    # s = x+exp(-x)
    # t = -x
    # c = lim(s/t) = lim((x+exp(-x))/-x) = -1
    # f = exp(s-ct)*ω^c = exp(x+exp(-x)-c*t)*ω^-1 = exp(exp(-x))/ω

    @test SymbolicLimits.zero_equivalence(
        SymbolicLimits.rewrite(exp(x + exp(-x)), ω, -x, x, Set{Any}()) -
            exp(exp(-x)) / ω,
        Set{Any}()
    ) # it works if you define `limit(args...) = -1`

    # F = exp(exp(-x))/ω - exp(x)

    # f = exp(x)
    # s = x
    # t = -x
    # c = -1
    # f = exp(s-ct)*ω^c = exp(x-c*t)*ω^-1 = exp(0)/ω = 1/ω

    # F = exp(exp(-x))/ω - 1/ω

    # ...

    # F = exp(ω)/ω - 1/ω
    let F = exp(ω) / ω - 1 / ω, h = -x
        @test SymbolicLimits.get_leading_exponent(F, ω, h, Set{Any}()) == 0
        @test SymbolicLimits.get_series_term(F, ω, h, 0, Set{Any}()) == 1 # the correct final answer
    end

    function test(expr, leading_exp, series, sym = x)
        lt = SymbolicLimits.get_leading_exponent(expr, sym, nothing, Set{Any}())
        @test lt === leading_exp
        for (i, val) in enumerate(series)
            @test SymbolicLimits.get_series_term(
                expr, sym, nothing, lt + i - 1, Set{Any}()
            ) === val
        end
        for i in (leading_exp - 10):(leading_exp - 1)
            @test SymbolicLimits.get_series_term(
                expr, sym, nothing, i, Set{Any}()
            ) === 0
        end
        return
    end
    test(x, 1, [1, 0, 0, 0, 0, 0])
    test(x^2, 2, [1, 0, 0, 0, 0, 0])
    test(x^2 + x, 1, [1, 1, 0, 0, 0, 0])

    @test SymbolicLimits.recursive([1, [2, 3]]) do f, arg
        arg isa AbstractArray ? sum(f, arg) : arg
    end == 6

    @test unwrap_const(
        only(SymbolicLimits.most_rapidly_varying_subexpressions(exp(x), x, Set{Any}())) -
            exp(x)
    ) === 0 # works if you define `limit(args...) = Inf`
    @test all(i -> i === x, SymbolicLimits.most_rapidly_varying_subexpressions(x + 2(x + 1), x, Set{Any}())) # works if you define `limit(args...) = 1`

    @test SymbolicLimits.log_exp_simplify(x) === x
    @test SymbolicLimits.zero_equivalence(
        SymbolicLimits.log_exp_simplify(exp(x)) -
            exp(x), Set{Any}()
    )
    @test SymbolicLimits.zero_equivalence(
        SymbolicLimits.log_exp_simplify(exp(log(x))) - exp(log(x)), Set{Any}()
    )
    @test SymbolicLimits.log_exp_simplify(log(exp(x))) === x
    @test SymbolicLimits.zero_equivalence(
        SymbolicLimits.log_exp_simplify(log(exp(log(x)))) - log(x), Set{Any}()
    )
    @test unwrap_const(SymbolicLimits.log_exp_simplify(log(exp(1 + x))) - (1 + x)) === 0
    @test SymbolicLimits.log_exp_simplify(log(log(exp(exp(x))))) === x
    @test SymbolicLimits.log_exp_simplify(log(exp(log(exp(x))))) === x
end
