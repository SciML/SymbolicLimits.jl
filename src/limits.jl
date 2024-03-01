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

is_exp(expr) = false
is_exp(expr::BasicSymbolic) = exprtype(expr) == TERM && operation(expr) == exp

FUEL = Ref(1000)

# unused: for debugging only:
function S(expr, x)
    expr === x && return Set([x])
    expr isa BasicSymbolic || return Set([])
    t = exprtype(expr)
    t == SYM && return Set([])
    t in (ADD, MUL, DIV) && return mapreduce(Base.Fix2(S, x), ∪, arguments(expr))
    t == POW && arguments(expr)[2] isa Real && isinteger(arguments(expr)[2]) && return S(arguments(expr)[1], x)
    t == POW && error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
    t == TERM && operation(expr) == log && return S(only(arguments(expr)), x) ∪ Set([expr])
    t == TERM && operation(expr) == exp && return S(only(arguments(expr)), x) ∪ Set([expr])
end
_size(expr, x) = length(S(expr, x))

function indent()
    depth = length(backtrace())-36
    if depth < 12
        print(' '^(depth÷1))
        true
    else
        false
    end
end

limit(expr, x::BasicSymbolic{Field}) where Field = signed_limit(expr, x)[1]
signed_limit(expr::Field, x::BasicSymbolic{Field}) where Field = expr, sign(expr)
function signed_limit(expr::BasicSymbolic{Field}, x::BasicSymbolic{Field}) where Field
    expr0 = expr
    if FUEL[] <= 0
        error("Fuel exhausted")
    end
    FUEL[] -= 1

    indent() && println("limit($expr, $x) (size: $(_size(expr, x)))")

    expr === x && (indent() && println("<"); return (Inf, 1))

    indent() && println("A")
    Ω = most_rapidly_varying_subexpressions(expr, x)
    indent() && println("B")
    isempty(Ω) && (indent() && println("<"); return (expr, sign(expr)))
    #indent() && println("C")
    ω_val = last(Ω)
    ω_sym = SymbolicUtils.Sym{Field}(Symbol(:ω, gensym()))

    indent() && println("D")
    while !is_exp(ω_val) # equivalent to x ∈ Ω
        #indent() && println("D1")
        expr = recursive(expr) do f, ex
            ex isa BasicSymbolic{Field} || return ex
            exprtype(ex) == SYM && return ex === x ? exp(x) : ex
            operation(ex)(f.(arguments(ex))...)
        end
        #indent() && println("D2")
        expr = log_exp_simplify(expr)
        indent() && println("D3, ", Ω)
        # Ω = most_rapidly_varying_subexpressions(expr, x) NO! this line could lead to infinite recursion
        Ω = [log_exp_simplify(recursive(expr) do f, ex
                ex isa BasicSymbolic{Field} || return ex
                exprtype(ex) == SYM && return ex === x ? exp(x) : ex
                operation(ex)(f.(arguments(ex))...)
            end) for expr in Ω]
        indent() && println("D4, ", Ω)
        ω_val = last(Ω)
        #indent() && println("D5")
    end

    indent() && println("E, ", (expr, ω_val))

    # normalize ω to approach zero (it is already structurally positive)
    @assert operation(ω_val) == exp
    h = only(arguments(ω_val))
    lm = limit(h, x)
    @assert isinf(lm)
    if lm > 0
        h = -h
        ω_val = exp(h)
    end

    indent() && println("F: ", (expr, h, ω_val, Ω))

    # This ensures that mrv(expr2) == {ω}. TODO: do we need to do top-down with recursion even after replacement?
    expr2 = recursive(expr) do f, ex # This traverses from largest to smallest, as required?
        ex isa BasicSymbolic{Field} || return ex
        exprtype(ex) == SYM && return ex
        # ex ∈ Ω && return rewrite(ex, ω, h, x) # ∈ uses symbolic equality which is iffy
        if any(x -> zero_equivalence(x - ex), Ω)
            ex = rewrite(ex, ω_sym, h, x)
            ex isa BasicSymbolic{Field} || return ex
            exprtype(ex) == SYM && return ex
        end
        operation(ex)(f.(arguments(ex))...)
    end

    indent() && println("G, $expr2")

    exponent = get_leading_exponent(expr2, ω_sym, h)
    exponent === Inf && return (0, 0) # TODO: track sign
    leading_coefficient = get_series_term(expr2, ω_sym, h, exponent)
    indent() && println("H, $exponent, $leading_coefficient")
    leading_coefficient, lc_sign = signed_limit(leading_coefficient, x)
    indent() && println("I, $exponent, $leading_coefficient")
    res = if exponent < 0
        # This will fail if leading_coefficient is not scalar, oh well, we'll solve that error later. Inf sign kinda matters.
        copysign(Inf, lc_sign), lc_sign
    elseif exponent > 0
        # This will fail if leading_coefficient is not scalar, oh well, we'll solve that error later. We can always drop zero sign
        copysign(zero(Field), lc_sign), lc_sign
    else
        leading_coefficient, lc_sign
    end
    indent() && println("< ($expr0 -> $res)")
    res
end

function recursive(f, args...)
    g(args...) = f(g, args...)
    g(args...)
end

# TODO: use recursive or @rrule
log_exp_simplify(expr) = expr
function log_exp_simplify(expr::BasicSymbolic)
    exprtype(expr) == SYM && return expr
    exprtype(expr) == TERM && operation(expr) == log || return operation(expr)(log_exp_simplify.(arguments(expr))...)
    arg = log_exp_simplify(only(arguments(expr)))
    # TODO: return _log(arg)
    arg isa BasicSymbolic && exprtype(arg) == TERM && operation(arg) == exp || return log(arg)
    only(arguments(arg))
end

most_rapidly_varying_subexpressions(expr::Field, x::BasicSymbolic{Field}) where Field = []
function most_rapidly_varying_subexpressions(expr::BasicSymbolic{Field}, x::BasicSymbolic{Field}) where Field
    exprtype(x) == SYM || throw(ArgumentError("Must expand with respect to a symbol. Got $x"))
    indent() && println("most_rapidly_varying_subexpressions($expr, $x), (size: $(_size(expr, x)))")
    # TODO: this is slow. This whole algorithm is slow. Profile, benchmark, and optimize it.
    et = exprtype(expr)
    ret = if et == SYM
        if expr.name == x.name
            [expr]
        else
            []
        end
    elseif et == TERM
        op = operation(expr)
        if op == log
            arg = only(arguments(expr))
            most_rapidly_varying_subexpressions(arg, x)
        elseif op == exp
            # indent() && println("XXXXXXXXX")
            arg = only(arguments(expr))
            res = if isfinite(limit(arg, x))
                # indent() && println("Finite")
                most_rapidly_varying_subexpressions(arg, x)
            else
                # indent() && println("Infinite")
                mrv_join(x)([expr], most_rapidly_varying_subexpressions(arg, x)) # ensure that the inner most exprs stay last
            end
            # indent() && println("YYYYYYYY $res")
            res
        else
            error("Not implemented: $op")
        end
    elseif et ∈ (ADD, MUL, DIV)
        mapreduce(Base.Fix2(most_rapidly_varying_subexpressions, x), mrv_join(x), arguments(expr), init=[])
    elseif et == POW
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        if exponent isa Real && isinteger(exponent)
            most_rapidly_varying_subexpressions(base, x)
        else
            error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
        end
    else
        error("Unknwon Expr type: $et")
    end
    indent() && println("mrv($expr, $x) = $ret")
    ret
end

is_exp_or_x(expr::BasicSymbolic, x::BasicSymbolic) =
    expr === x || exprtype(expr) == TERM && operation(expr) == exp

"""
    f ≺ g iff log(f)/log(g) -> 0
"""
function compare_varience_rapidity(expr1, expr2, x)
    indent() && println("compare_varience_rapidity($expr1, $expr2, $x)")
    @assert is_exp_or_x(expr1, x)
    @assert is_exp_or_x(expr2, x)
    # expr1 === expr2 && return 0 # both x (or both same exp, either way okay, but for sure we cover the both x case)
    # expr1 === x && expr2 !== x && return compare_varience_rapidity(expr2, expr1, x)
    # @assert expr1 !== x
    # if expr2 !== x
    #     # they are both exp's, so it's safe (i.e. not a larger sub-expression) to call
    #     lim = limit(only(arguments(expr1))/only(arguments(expr2)), x) # equivalent to limit(_log(expr1)/_log(expr2), x) = limit(log(expr1)/log(expr2), x)
    # else
    #     s = only(arguments(expr1))
    #     if _occursin(ln(x), s)
    #         # also safe
    #         lim = limit(s/ln(x), x)
    #     else
    #     s/ln(x)
    # end
    # iszero(lim) && return -1
    # isfinite(lim) && return 0
    # isinf(lim) && return 1
    # #indent() && println("compare_varience_rapidity($expr1, $expr2, $x)")

    lim = limit(_log(expr1)/_log(expr2), x)
    indent() && println("LIM: ", lim)
    iszero(lim) && return -1
    isfinite(lim) && return 0
    isinf(lim) && return 1
    error("Unexpected limit result: $lim") # e.g. if it depends on other variables?
end

function mrv_join(x)
    function (mrvs1, mrvs2)
        isempty(mrvs1) && return mrvs2
        isempty(mrvs2) && return mrvs1
        cmp = compare_varience_rapidity(first(mrvs1), first(mrvs2), x)
        if cmp == -1
            mrvs2
        elseif cmp == 1
            mrvs1
        else
            vcat(mrvs1, mrvs2) # sets? unions? performance? nah. This saves us a topl-sort.
        end
    end
end

"""
rewrite `expr` in the form `Aω^c` such that `A` is less rapidly varying than `ω` and `c` is
a real number. `ω` is a symbol that represents `exp(h)`.
"""
function rewrite(expr::BasicSymbolic{Field}, ω::BasicSymbolic{Field}, h::BasicSymbolic{Field}, x::BasicSymbolic{Field}) where Field
    @assert exprtype(expr) == TERM && operation(expr) == exp
    @assert exprtype(ω) == SYM
    @assert exprtype(x) == SYM

    s = only(arguments(expr))
    t = h
    c = limit(s/t, x)
    @assert isfinite(c) && !iszero(c)
    exp(s-c*t)*ω^c # I wonder how this works with multiple variables...
end

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

_log(x) = _log(x, nothing, nothing)
_log(x, ω, h) = log(x)
function _log(x::BasicSymbolic, ω, h)
    exprtype(x) == TERM && operation(x) == exp && return only(arguments(x))
    x === ω && return h
    log(x)
end

zero_equivalence(expr) = iszero(simplify(expr, expand=true)) === true

using Test

let
    @syms x::Real
    @test limit(-1/x, x) === 0
    @test limit(-x / log(x), x) === -Inf
    @test only(mrv_join(x)([exp(x)], [x])) - exp(x) === 0
    @test signed_limit(exp(exp(-x))-1, x) == (0, 1)
    @test limit(exp(x+exp(-x))-exp(x), x) == 1
    @test limit(x^7/exp(x), x) == 0
    @test limit(x^70000/exp(x), x) == 0
    @test_broken limit(log(log(x*exp(x*exp(x))+1))-exp(exp(log(log(x))+1/x)), x) == 0
end

false && let
    @syms x::Real y::Real ω::Real
    @test zero_equivalence(x*(x+y)-x-x*y+x-x*(x+1)+x)
    @test_broken zero_equivalence(exp((x+1)*x - x*x-x)-1)

    @test get_leading_exponent(x^2, x, nothing) == 2
    @test get_series_term(log(exp(x)), x, nothing, 1) == 1
    @test get_series_term(log(exp(x)), x, nothing, 0) == 0
    @test_broken get_series_term(log(exp(x)), x, nothing, 2) == 0 # This is okay to be broken because exp(ω) is more rapidly varying than ω.

    # F = exp(x+exp(-x))-exp(x)
    # Ω = {exp(x + exp(-x)), exp(x), exp(-x)}
    # Topl-sort Ω by containment
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

    # @test rewrite(exp(x+exp(-x)), ω, -x, x) == exp(exp(-x))/ω # it works if you define `limit(args...) = -1`

    # F = exp(exp(-x))/ω - exp(x)

    # f = exp(x)
    # s = x
    # t = -x
    # c = -1
    # f = exp(s-ct)*ω^c = exp(x-c*t)*ω^-1 = exp(0)/ω = 1/ω

    # F = exp(exp(-x))/ω - 1/ω

    # ...

    # F = exp(ω)/ω - 1/ω
    let F = exp(ω)/ω - 1/ω, h=-x
        @test get_leading_exponent(F, ω, h) == 0
        @test get_series_term(F, ω, h, 0) == 1 # the correct final answer
    end

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
    test(x^2, 2, [1,0,0,0,0,0])
    test(x^2+x, 1, [1,1,0,0,0,0])

    @test recursive([1,[2,3]]) do f, arg
        arg isa AbstractArray ? sum(f, arg) : arg
    end == 6

    @test_broken only(most_rapidly_varying_subexpressions(exp(x), x)) - exp(x) === 0 # works if you define `limit(args...) = Inf`
    @test_broken all(i -> i === x, most_rapidly_varying_subexpressions(x+2(x+1), x)) # works if you define `limit(args...) = 1`

    @test log_exp_simplify(x) === x
    @test log_exp_simplify(exp(x)) === exp(x)
    @test log_exp_simplify(exp(log(x))) === exp(log(x))
    @test log_exp_simplify(log(exp(x))) === x
    @test log_exp_simplify(log(exp(log(x)))) === log(x)
    @test (log_exp_simplify(log(exp(1+x))) - (1+x)) === 0
    @test log_exp_simplify(log(log(exp(exp(x))))) === x
    @test log_exp_simplify(log(exp(log(exp(x))))) === x
end
