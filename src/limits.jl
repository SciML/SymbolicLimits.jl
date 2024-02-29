# Sympy uses
# - heuristic fastpaths for common cases
# - the Gruntz algorithm for all other cases
# https://github.com/sympy/sympy/blob/24792d5f4fbf8fe4365101e53b735c6c1f140e0f/sympy/series/limits.py#L54C1-L56C50
# Code: https://github.com/sympy/sympy/blob/24792d5f4fbf8fe4365101e53b735c6c1f140e0f/sympy/series/gruntz.py
# Paper: https://www.cybertester.com/data/gruntz.pdf (1996)
# That paper includes motivating exmaples that existing systems fail to solve:
#=

limit(exp(x+exp(-x))-exp(x), x=%plusInfinity) (1)
limit(x^7/exp(x), x, infinity); (0)
limit((arccos(x + h) - arccos(x))/h, h=0, right); (?)
limit(1/(x^log(log(log(log(1/x-1))))))), x, 0, '+') (Inf)
limit((erf(x - exp(-exp(x)))-erf(x))*exp(exp(x))*exp(x^2), x, Inf) (-2/√π)
limit(exp(csc(x))/exp(cot(x)), x, 0) (1)
limit(exp(x)*(sin(1/x+exp(-x)) - sin(1/x)), x, Inf) (1)
limit(log(log(x*exp(x*exp(x))+1))-exp(exp(log(log(x))+1/x))) (?)
limit(2exp(-x)/exp(-x), x, 0) (2)
limit(exp(csc(x))/exp(cot(x)), x, 0) (1)
=#

# The limit of a continuous function `f` (e.g. all rational functions) is the function
# applied to the limits `y...` of its arguments (provided `f(y...)`` exists)

# Generations of limit algorithms:

# 1) heuristic
# 2) series
# 3) this

# Comparability class: f ≍ g iff log(f)/log(g) -> c for c ∈ ℝ*
# f ≺ g iff log(f)/log(g) -> 0
# Ω(expr) is the set of most varying subexpressions of expr

# Topl-sort Ω by containment
# Take a smallest element of Ω and call it ω.
# From largest to smallest, rewrite elements f ∈ Ω in terms of ω in the form
# Assume f is of the form exp(s) and ω is of the form exp(t).
# -- Recursively compute c = lim(s/t)
# f = exp(s) = exp((s/t)*t) = exp(t)^(s/t) = ω^(s/t) ≠ ω^c
# f = f*ω^c/ω^c = exp(log(f)-c*log(ω))*ω^c = exp(s-ct)*ω^c

# Recursively compute a series expansion of the rewritten expression in terms of ω
# This should be a lazy construction that includes a query to a zero-equivalence oracle

# ---

#=

function limit(expr, x)
    Ω = mvr(expr, x)
    isempty(Ω) && return expr
    ω = first(mvr)

    if exprtype(ω) != EXP
        expr = recursive(expr) do f, ex
            ex == x ? exp(x) : f(ex)
        end
        expr = log_exp_simplify(expr)
        ω = exp(x)
    end

    **normalize ω to be positive and approach zero**

    expr2 = recursive(expr) do f, ex
        f(ex ∈ Ω ? rewrite(ex, ω) : ex)
    end
    ser = series(expr2, ω)
    c, e = first(ser)
    if e < 0
        Inf
    elseif e > 0
        0
    else
        limit(c, x)
    end
end

function rewrite(expr, ω)
    @assert exprtype(expr) == EXP
    @assert exprtype(ω) == EXP
    s = expr.exponent
    t = ω.exponent
    c = limit(s/t, x)
    @assert isfinite(c) && !iszero(c)
    exp(s-ct)*ω^c
end

=#

# We can't just do a series expansion of the raw input in terms of x because given a serise
# expansion of `g` in terms of `x`, how do we get a series expansion of `log(g)` in terms of
# `x`?

using SymbolicUtils
using SymbolicUtils: BasicSymbolic, exprtype
using SymbolicUtils: SYM, TERM, ADD, MUL, POW, DIV
"""
ω is a symbol that represents the expression exp(h).
"""
function get_series_term(expr::BasicSymbolic{Field}, ω::BasicSymbolic{Field}, h, i::Int) where Field
    exprtype(ω) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))

    et = exprtype(expr)
    if et == SYM
        if expr.name == ω.name
            i == 1 ? one(Field) : zero(Field)
        else
            i == 0 ? expr : zero(Field)
        end
    elseif et == TERM
        op = operation(expr)
        if op == log
            arg = only(arguments(expr))
            exponent = get_leading_exponent(arg, ω, h)
            t0 = get_series_term(arg, ω, h, exponent)
            if i == 0
                _log(t0*ω^exponent, ω, h)
            else
                # TODO: refactor this to share code for the "sum of powers of a series" form
                sm = zero(Field)
                for k in 1:i # the sum starts at 1
                    term = i ÷ k
                    if term * k == i # integral
                        sm += (-get_series_term(arg, ω, h, term+exponent)/t0)^k/k
                    end
                end
                # TODO: All these for loops are ugly and error-prone
                # abstract this all away into a lazy series type to pay of the tech-debt.
                -sm
            end
        elseif op == exp
            i < 0 && return zero(Field)
            arg = only(arguments(expr))
            exponent = get_leading_exponent(arg, ω, h)
            sm = one(Field) # k == 0 adds one to the sum
            if exponent == 0
                # e^c0 * sum (s-t0)^k/k!
                # TODO: refactor this to share code for the "sum of powers of a series" form
                for k in 1:i
                    term = i ÷ k
                    if term * k == i # integral
                        sm += get_series_term(arg, ω, h, term+exponent)^k/factorial(k) # this could overflow... oh well. It'l error if it does.
                    end
                end
                sm * exp(get_series_term(arg, ω, h, exponent))
            else @assert exponent > 0 # from the theory.
                # sum s^k/k!
                for k in 1:i
                    term = i ÷ k
                    if term * k == i && term >= exponent # integral and not structural zero
                        sm += get_series_term(arg, ω, h, term+exponent)^k/factorial(k) # this could overflow... oh well. It'l error if it does.
                    end
                end
                sm
            end
        else
            error("Not implemented: $op")
        end
    elseif et == ADD
        sum(get_series_term(arg, ω, h, i) for arg in arguments(expr))
    elseif et == MUL
        arg1, arg_rest = Iterators.peel(arguments(expr))
        arg2 = prod(arg_rest)
        exponent1 = get_leading_exponent(arg1, ω, h)
        exponent2 = get_leading_exponent(arg2, ω, h)
        sm = zero(Field)
        for j in exponent1:(i-exponent2)
            t1 = get_series_term(arg1, ω, h, j)
            t2 = get_series_term(arg2, ω, h, i-j)
            sm += t1 * t2
        end
        sm
    elseif et == POW
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        if exponent isa Real && isinteger(exponent)
            t = i ÷ exponent
            if t * exponent == i # integral
                get_series_term(base, ω, h, t) ^ exponent
            else
                zero(Field)
            end
        else
            error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
        end
    elseif et == DIV
        args = arguments(expr)
        @assert length(args) == 2
        num, den = args
        num_exponent = get_leading_exponent(num, ω, h)
        den_exponent = get_leading_exponent(den, ω, h)
        den_leading_term = get_series_term(den, ω, h, den_exponent)
        @assert !zero_equivalence(den_leading_term)
        sm = zero(Field)
        for j in num_exponent:i+den_exponent
            t_num = get_series_term(num, ω, h, j)
            exponent = i-j
            # TODO: refactor this to share code for the "sum of powers of a series" form
            sm2 = one(Field) # k = 0 adds one to the sum
            for k in 1:exponent
                term = exponent ÷ k
                if term * k == exponent # integral
                    sm2 += (-get_series_term(den, ω, h, term+den_exponent)/den_leading_term)^k
                end
            end
            sm += sm2 * t_num
        end
        sm / den_leading_term
    else
        error("Unknwon Expr type: $et")
    end
end
function get_series_term(expr::Field, ω::BasicSymbolic{Field}, h, i::Int) where Field
    exprtype(ω) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))
    i == 0 ? expr : zero(Field)
end

function get_leading_exponent(expr::BasicSymbolic{Field}, ω::BasicSymbolic{Field}, h) where Field
    exprtype(ω) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))

    zero_equivalence(expr) && return Inf

    et = exprtype(expr)
    if et == SYM
        if expr.name == ω.name
            1
        else
            0
        end
    elseif et == TERM
        op = operation(expr)
        if op == log
            arg = only(arguments(expr))
            exponent = get_leading_exponent(arg, ω, h)
            lt = get_series_term(arg, ω, h, exponent)
            if !zero_equivalence(lt - one(Field))
                0
            else
                # There will never be a term with power less than 0, and the zero power term
                # is log(T0) which is handled above with the "isone" check.
                findfirst(i -> zero_equivalence(get_series_term(expr, ω, h, i)), 1:typemax(Int))
            end
        elseif op == exp
            0
        else
            error("Not implemented: $op")
        end
    elseif et == ADD
        exponent = minimum(get_leading_exponent(arg, ω, h) for arg in  arguments(expr))
        for i in exponent:typemax(Int)
            sm = sum(get_series_term(arg, ω, h, i) for arg in arguments(expr))
            if !zero_equivalence(sm)
                return i
            end
            i > exponent+1000 && error("This is likely due to known zero_equivalence bugs")
        end
    elseif et == MUL
        sum(get_leading_exponent(arg, ω, h) for arg in arguments(expr))
    elseif et == POW # This is not an idiomatic representation of powers. Avoid it if possible.
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        if exponent isa Real && isinteger(exponent)
            exponent * get_leading_exponent(base, ω, h)
        else
            error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
        end
    elseif et == DIV
        args = arguments(expr)
        @assert length(args) == 2
        num, den = args
         # The naive answer is actually correct. See the get_series_term implementation for how.
        get_leading_exponent(num, ω, h) - get_leading_exponent(den, ω, h)
    else
        error("Unknwon Expr type: $et")
    end
end
function get_leading_exponent(expr::Field, ω::BasicSymbolic{Field}, h) where Field
    exprtype(ω) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))
    zero_equivalence(expr) ? Inf : 0
end

_log(x, ω, h) = log(x)
function _log(x::BasicSymbolic, ω::BasicSymbolic, h)
    exprtype(x) == TERM && operation(x) == exp && return only(arguments(x))
    x === ω && return h
    log(x)
end

zero_equivalence(expr) = iszero(simplify(expr, expand=true)) === true

using Test
let
    @syms x::Real y::Real
    @test zero_equivalence(x*(x+y)-x-x*y+x-x*(x+1)+x)
    @test_broken zero_equivalence(exp((x+1)*x - x*x-x)-1)

    @test get_leading_exponent(x^2, x, nothing) == 2
    @test get_series_term(log(exp(x)), x, nothing, 1) == 1
    @test get_series_term(log(exp(x)), x, nothing, 0) == 0
    @test_broken get_series_term(log(exp(x)), x, nothing, 2) == 0

    function test(expr, leading_exp, series, sym=x)
        lt = get_leading_exponent(expr, sym, nothing)
        @test lt === leading_exp
        for (i,val) in enumerate(series)
            @test get_series_term(expr, sym, nothing, lt+i-1) === val
        end
        for i in leading_exp-10:leading_exp-1
            @test get_series_term(expr, sym, nothing, i) === 0
        end
    end
    test(x, 1, [1,0,0,0,0,0])
    # test(x^2, 2, [1,0,0,0,0,0]) # broken
    # test(x^2+x, 1, [1,0,1,0,0,0]) # broken
end
