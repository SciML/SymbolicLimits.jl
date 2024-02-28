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
        error("Not implemented: $expr")
    elseif et == ADD
        sum(get_series_term(arg, sym, i) for arg in arguments(expr))
    elseif et == MUL
        arg1, arg_rest = Iterators.peel(arguments(expr))
        terms = Any[get_series_term(arg1, sym, j) for j in 0:i]
        for arg in arg_rest
            new_terms = [get_series_term(arg, sym, j) for j in 0:i]
            for j in i:-1:0
                terms[j+1] = sum(terms[k+1] * new_terms[j-k+1] for k in 0:j)
            end
        end
        terms[i+1]
    elseif et == POW
        error("Not implemented: $expr")
    elseif et == DIV
        error("Not implemented: $expr")
    else
        error("Unknwon Expr type: $et")
    end
end



function get_series_term(expr::Field, sym::BasicSymbolic{Field}, i::Int) where Field
    exprtype(sym) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $sym"))
    i == 0 ? expr : zero(Field)
end

zero_equivalence(expr) = iszero(simplify(expr)) === true
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
