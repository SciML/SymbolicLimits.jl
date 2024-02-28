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

using SymbolicUtils: BasicSymbolic, exprtype
using SymbolicUtils: SYM, TERM, ADD, MUL, POW, DIV
function get_series_term(expr::BasicSymbolic{Field}, sym::BasicSymbolic{Field}, i::Int) where Field
    exprtype(sym) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $sym"))

    et = exprtype(expr)
    if et == SYM
        if expr.name == sym.name
            i == 1 ? one(Field) : zero(Field)
        else
            i == 0 ? expr : zero(Field)
        end
    elseif et == TERM
        op = operation(expr)
        if op == log
            error("Not implemented: $op")
        elseif op == exp
            error("Not implemented: $op")
        else
            error("Not implemented: $op")
        end
    elseif et == ADD
        sum(get_series_term(arg, sym, i) for arg in arguments(expr))
    elseif et == MUL
        arg1, arg_rest = Iterators.peel(arguments(expr))
        arg2 = prod(arg_rest)
        exponent1 = get_leading_exponent(arg1, sym)
        exponent2 = get_leading_exponent(arg2, sym)
        sm = zero(Field)
        for j in exponent1:(i-exponent2)
            t1 = get_series_term(arg1, sym, j)
            t2 = get_series_term(arg2, sym, i-j)
            sm += t1 * t2
        end
        sm
    elseif et == POW
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        get_series_term(exp(log(base)*exponent), sym, i)
    elseif et == DIV
        args = arguments(expr)
        @assert length(args) == 2
        num, den = args
        num_exponent = get_leading_exponent(num, sym)
        den_exponent = get_leading_exponent(den, sym)
        den_leading_term = get_series_term(den, sym, den_exponent)
        @assert !zero_equivalence(den_leading_term)
        sm = zero(Field)
        for j in num_exponent:i+den_exponent
            t_num = get_series_term(num, sym, j)
            exponent = i-j
            sm2 = one(Field) # k = 0 adds one to the sum
            for k in 1:exponent
                term = exponent ÷ k
                if term * k == exponent # integral
                    sm2 += (-get_series_term(den, sym, term)/den_leading_term)^k
                end
            end
            sm += sm2 * t_num
        end
        sm / den_leading_term
    else
        error("Unknwon Expr type: $et")
    end
end
function get_series_term(expr::Field, sym::BasicSymbolic{Field}, i::Int) where Field
    exprtype(sym) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $sym"))
    i == 0 ? expr : zero(Field)
end

function get_leading_exponent(expr::BasicSymbolic{Field}, sym::BasicSymbolic{Field}) where Field
    exprtype(sym) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $sym"))

    zero_equivalence(expr) && return Inf

    et = exprtype(expr)
    if et == SYM
        if expr.name == sym.name
            1
        else
            0
        end
    elseif et == TERM
        op = operation(expr)
        if op == log
            error("Not implemented: $op")
        elseif op == exp
            error("Not implemented: $op")
        else
            error("Not implemented: $op")
        end
    elseif et == ADD
        exponent = minimum(get_leading_exponent(arg, sym) for arg in  arguments(expr))
        for i in exponent:typemax(Int)
            sm = sum(get_series_term(arg, sym, i) for arg in arguments(expr))
            if !zero_equivalence(sm)
                return i
            end
            i > exponent+1000 && error("This is likely due to known zero_equivalence bugs")
        end
    elseif et == MUL
        sum(get_leading_exponent(arg, sym) for arg in arguments(expr))
    elseif et == POW
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        get_leading_exponent(exp(log(base)*exponent), sym)
    elseif et == DIV
        args = arguments(expr)
        @assert length(args) == 2
        num, den = args
         # The naive answer is actually correct. See the get_series_term implementation for how.
        get_leading_exponent(num, sym) - get_leading_exponent(den, sym)
    else
        error("Unknwon Expr type: $et")
    end
end
function get_leading_exponent(expr::Field, sym::BasicSymbolic{Field}) where Field
    exprtype(sym) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $sym"))
    zero_equivalence(expr) ? Inf : 0
end


zero_equivalence(expr) = iszero(simplify(expr, expand=true)) === true

using Test
let
    @syms x::Real y::Real
    @test zero_equivalence(x*(x+y)-x-x*y+x-x*(x+1)+x)
    @test_broken zero_equivalence(exp((x+1)*x - x*x-x)-1)
end

function get_first_nonzero_term(expr, sym::BasicSymbolic)
    zero_equivalence(expr) && return 0, -1
    for i in 0:typemax(Int)
        res = get_series_term(expr, sym, i)
        if !zero_equivalence(res)
            return res, i
        end
    end
end

struct Series
    leading_exponent::Int
    cache::Vector{Any}
    expr::BasicSymbolic
    sym::BasicSymbolic
end
