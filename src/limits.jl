# Paper: https://www.cybertester.com/data/gruntz.pdf (1996)

# The limit_inf of a continuous function `f` (e.g. all rational functions) is the function
# applied to the limits `y...` of its arguments (provided `f(y...)`` exists)

# Generations of limit_inf algorithms:

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

# We can't just do a series expansion of the raw input in terms of x because given a series
# expansion of `g` in terms of `x`, how do we get a series expansion of `log(g)` in terms of
# `x`?

using SymbolicUtils
using SymbolicUtils: BasicSymbolic, exprtype
using SymbolicUtils: SYM, TERM, ADD, MUL, POW, DIV

"""
    is_exp(expr)

Check if an expression is of the form `exp(...)`.

Returns `true` if `expr` is a symbolic expression with the exponential function as its operation,
`false` otherwise.
"""
is_exp(expr) = false
is_exp(expr::BasicSymbolic) = exprtype(expr) == TERM && operation(expr) == exp

# unused. This function provides a measure of the "size" of an expression, for use in proofs
# of termination and debugging nontermination only:
# function S(expr, x)
#     expr === x && return Set([x])
#     expr isa BasicSymbolic || return Set([])
#     t = exprtype(expr)
#     t == SYM && return Set([])
#     t in (ADD, MUL, DIV) && return mapreduce(Base.Fix2(S, x), ∪, arguments(expr))
#     t == POW && arguments(expr)[2] isa Real && isinteger(arguments(expr)[2]) && return S(arguments(expr)[1], x)
#     t == POW && error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
#     t == TERM && operation(expr) == log && return S(only(arguments(expr)), x) ∪ Set([expr])
#     t == TERM && operation(expr) == exp && return S(only(arguments(expr)), x) ∪ Set([expr])
# end
# _size(expr, x) = length(S(expr, x))

"""
    limit_inf(expr, x)

Compute the limit of `expr` as `x` approaches infinity and return `(limit, assumptions)`.

This is the internal API boundary between the internal limits.jl file and the public
SymbolicLimits.jl file
"""
function limit_inf(expr, x::BasicSymbolic{Field}) where {Field}
    assumptions = Set{Any}()
    limit = signed_limit_inf(expr, x, assumptions)[1]
    limit, assumptions
end

"""
    signed_limit_inf(expr, x, assumptions)

Compute the limit of `expr` as `x` approaches infinity and return `(limit, sign)`.
This function handles both symbolic expressions and scalar values, tracking assumptions
made during the computation.

For scalar expressions, returns `(expr, sign(expr))`.
For symbolic expressions, applies the Gruntz algorithm to compute the limit.

# Arguments

  - `expr`: The expression to take the limit of
  - `x`: The variable approaching infinity
  - `assumptions`: A set to track assumptions made during computation

# Returns

A tuple `(limit, sign)` where:

  - `limit`: The computed limit value
  - `sign`: The sign of the limit
"""
function signed_limit_inf(expr::Field, x::BasicSymbolic{Field}, assumptions) where {Field}
    expr, sign(expr)
end
function signed_limit_inf(expr::BasicSymbolic{Field}, x::BasicSymbolic{Field}, assumptions) where {Field}
    expr === x && return (Inf, 1)

    Ω = most_rapidly_varying_subexpressions(expr, x, assumptions)
    isempty(Ω) && return (expr, sign(expr))
    ω_val = last(Ω)
    ω_sym = SymbolicUtils.Sym{Field}(Symbol(:ω, gensym()))

    while !is_exp(ω_val) # equivalent to x ∈ Ω
        expr = recursive(expr) do f, ex
            ex isa BasicSymbolic{Field} || return ex
            exprtype(ex) == SYM && return ex === x ? exp(x) : ex
            operation(ex)(f.(arguments(ex))...)
        end
        expr = log_exp_simplify(expr)
        # Ω = most_rapidly_varying_subexpressions(expr, x) NO! this line could lead to infinite recursion
        Ω = [log_exp_simplify(recursive(expr) do f, ex
                 ex isa BasicSymbolic{Field} || return ex
                 exprtype(ex) == SYM && return ex === x ? exp(x) : ex
                 operation(ex)(f.(arguments(ex))...)
             end) for expr in Ω]
        ω_val = last(Ω)
    end

    # normalize ω to approach zero (it is already structurally positive)
    @assert operation(ω_val) == exp
    h = only(arguments(ω_val))
    lm = signed_limit_inf(h, x, assumptions)[1]
    @assert isinf(lm)
    if lm > 0
        h = -h
        ω_val = exp(h)
    end

    # This ensures that mrv(expr2) == {ω}. TODO: do we need to do top-down with recursion even after replacement?
    expr2 = recursive(expr) do f, ex # This traverses from largest to smallest, as required?
        ex isa BasicSymbolic{Field} || return ex
        exprtype(ex) == SYM && return ex
        # ex ∈ Ω && return rewrite(ex, ω, h, x) # ∈ uses symbolic equality which is iffy
        if any(x -> zero_equivalence(x - ex, assumptions), Ω)
            ex = rewrite(ex, ω_sym, h, x, assumptions)
            ex isa BasicSymbolic{Field} || return ex
            exprtype(ex) == SYM && return ex
        end
        operation(ex)(f.(arguments(ex))...)
    end

    exponent = get_leading_exponent(expr2, ω_sym, h, assumptions)
    exponent === Inf && return (0, 0) # TODO: track sign
    leading_coefficient = get_series_term(expr2, ω_sym, h, exponent, assumptions)
    leading_coefficient, lc_sign = signed_limit_inf(leading_coefficient, x, assumptions)
    res = if exponent < 0
        # This will fail if leading_coefficient is not scalar, oh well, we'll solve that error later. Inf sign kinda matters.
        copysign(Inf, lc_sign), lc_sign
    elseif exponent > 0
        # This will fail if leading_coefficient is not scalar, oh well, we'll solve that error later. We can always drop zero sign
        copysign(zero(Field), lc_sign), lc_sign
    else
        leading_coefficient, lc_sign
    end
    res
end

"""
    recursive(f, args...)

Apply function `f` recursively to its arguments, where `f` takes the recursive function as its first argument.

This utility function enables recursive operations on nested expressions by passing the recursive
function itself as the first argument to `f`.

# Example

```julia
recursive(expr) do f, ex
    # f is the recursive function, ex is the current expression
    # Apply f to subexpressions and build the result
end
```
"""
function recursive(f, args...)
    g(args...) = f(g, args...)
    g(args...)
end

"""
    log_exp_simplify(expr)

Simplify expressions by canceling `log(exp(x))` → `x` transformations.

This function performs basic log-exp simplifications that are always valid, specifically
canceling `log(exp(x))` to `x`. This is a conservative simplification that doesn't extend domains.

# Arguments

  - `expr`: The expression to simplify

# Returns

The simplified expression with log-exp cancellations applied.
"""
log_exp_simplify(expr) = expr
function log_exp_simplify(expr::BasicSymbolic)
    exprtype(expr) == SYM && return expr
    exprtype(expr) == TERM && operation(expr) == log ||
        return operation(expr)(log_exp_simplify.(arguments(expr))...)
    arg = log_exp_simplify(only(arguments(expr)))
    # TODO: return _log(arg)
    arg isa BasicSymbolic && exprtype(arg) == TERM && operation(arg) == exp ||
        return log(arg)
    only(arguments(arg))
end

"""
cancels log(exp(x)) and exp(log(x)), the latter may extend the domain
"""
strong_log_exp_simplify(expr) = expr
function strong_log_exp_simplify(expr::BasicSymbolic)
    exprtype(expr) == SYM && return expr
    exprtype(expr) == TERM && operation(expr) in (log, exp) ||
        return operation(expr)(strong_log_exp_simplify.(arguments(expr))...)
    arg = strong_log_exp_simplify(only(arguments(expr)))
    # TODO: return _log(arg)
    arg isa BasicSymbolic && exprtype(arg) == TERM && operation(arg) in (log, exp) &&
    operation(arg) != operation(expr) || return operation(expr)(arg)
    only(arguments(arg))
end

"""
    most_rapidly_varying_subexpressions(expr, x, assumptions)

Find the most rapidly varying subexpressions (MRV set) in `expr` with respect to `x`.

The MRV set consists of subexpressions that grow most rapidly as `x` approaches infinity.
This is a key component of the Gruntz algorithm for computing symbolic limits.

For scalar expressions, returns an empty list.

# Arguments

  - `expr`: The expression to analyze
  - `x`: The variable with respect to which we find rapidly varying subexpressions
  - `assumptions`: A set to track assumptions made during computation

# Returns

A list of the most rapidly varying subexpressions in `expr`.
"""
function most_rapidly_varying_subexpressions(expr::Field, x::BasicSymbolic{Field}, assumptions) where {Field}
    []
end
function most_rapidly_varying_subexpressions(
        expr::BasicSymbolic{Field}, x::BasicSymbolic{Field}, assumptions) where {Field}
    exprtype(x) == SYM ||
        throw(ArgumentError("Must expand with respect to a symbol. Got $x"))
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
            most_rapidly_varying_subexpressions(arg, x, assumptions)
        elseif op == exp
            arg = only(arguments(expr))
            res = if isfinite(signed_limit_inf(arg, x, assumptions)[1])
                most_rapidly_varying_subexpressions(arg, x, assumptions)
            else
                mrv_join(x, assumptions)([expr], most_rapidly_varying_subexpressions(arg, x, assumptions)) # ensure that the inner most exprs stay last
            end
            res
        else
            error("Not implemented: $op")
        end
    elseif et ∈ (ADD, MUL, DIV)
        mapreduce(expr -> most_rapidly_varying_subexpressions(expr, x, assumptions),
            mrv_join(x, assumptions), arguments(expr), init = [])
    elseif et == POW
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        if exponent isa Real && isinteger(exponent) && exponent > 0
            most_rapidly_varying_subexpressions(base, x, assumptions)
        else
            error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
        end
    else
        error("Unknown Expr type: $et")
    end
    ret
end

function is_exp_or_x(expr::BasicSymbolic, x::BasicSymbolic)
    expr === x || exprtype(expr) == TERM && operation(expr) == exp
end

"""
    compare_variance_rapidity(expr1, expr2, x, assumptions)

Compare the rapidity of growth between two expressions as `x` approaches infinity.

Returns:

  - `-1` if `expr1` grows slower than `expr2` (i.e., `expr1 ≺ expr2`)
  - `0` if `expr1` and `expr2` grow at the same rate (i.e., `expr1 ≍ expr2`)
  - `1` if `expr1` grows faster than `expr2` (i.e., `expr1 ≻ expr2`)

The comparison is based on the limit of `log(expr1)/log(expr2)` as `x` approaches infinity:

  - `f ≺ g` iff `log(f)/log(g) → 0`
  - `f ≍ g` iff `log(f)/log(g) → c` for some finite nonzero constant `c`
  - `f ≻ g` iff `log(f)/log(g) → ∞`

# Arguments

  - `expr1`, `expr2`: Expressions to compare (must be of the form `x` or `exp(...)`).
  - `x`: The variable approaching infinity
  - `assumptions`: A set to track assumptions made during computation

# Returns

An integer (-1, 0, or 1) indicating the relative growth rates.
"""
function compare_variance_rapidity(expr1, expr2, x, assumptions)
    @assert is_exp_or_x(expr1, x)
    @assert is_exp_or_x(expr2, x)
    # expr1 === expr2 && return 0 # both x (or both same exp, either way okay, but for sure we cover the both x case)
    # expr1 === x && expr2 !== x && return compare_variance_rapidity(expr2, expr1, x)
    # @assert expr1 !== x
    # if expr2 !== x
    #     # they are both exp's, so it's safe (i.e. not a larger sub-expression) to call
    #     lim = limit_inf(only(arguments(expr1))/only(arguments(expr2)), x) # equivalent to limit_inf(_log(expr1)/_log(expr2), x) = limit_inf(log(expr1)/log(expr2), x)
    # else
    #     s = only(arguments(expr1))
    #     if _occursin(ln(x), s)
    #         # also safe
    #         lim = limit_inf(s/ln(x), x)
    #     else
    #     s/ln(x)
    # end
    # iszero(lim) && return -1
    # isfinite(lim) && return 0
    # isinf(lim) && return 1

    lim = signed_limit_inf(_log(expr1)/_log(expr2), x, assumptions)[1]
    iszero(lim) && return -1
    isfinite(lim) && return 0
    isinf(lim) && return 1
    error("Unexpected limit_inf result: $lim") # e.g. if it depends on other variables?
end

function mrv_join(x, assumptions)
    function (mrvs1, mrvs2)
        isempty(mrvs1) && return mrvs2
        isempty(mrvs2) && return mrvs1
        cmp = compare_variance_rapidity(first(mrvs1), first(mrvs2), x, assumptions)
        if cmp == -1
            mrvs2
        elseif cmp == 1
            mrvs1
        else
            vcat(mrvs1, mrvs2) # sets? unions? performance? nah. This saves us a topo-sort.
        end
    end
end

"""
    rewrite(expr, ω, h, x, assumptions)

Rewrite `expr` in the form `A⋅ω^c` where `A` is less rapidly varying than `ω` and `c` is a real number.

This function takes an exponential expression and rewrites it in terms of a distinguished
exponential subexpression `ω`. The symbol `ω` represents `exp(h)` where `h` is the argument
of the most rapidly varying exponential.

The rewriting follows the formula: if `expr = exp(s)` and `ω = exp(h)`, then we compute
`c = lim(s/h, x, ∞)` and rewrite as `exp(s-c⋅h) ⋅ ω^c`.

# Arguments

  - `expr`: An exponential expression to rewrite (must be of the form `exp(...)`)
  - `ω`: A symbol representing the distinguished exponential `exp(h)`
  - `h`: The argument of the distinguished exponential
  - `x`: The variable approaching infinity
  - `assumptions`: A set to track assumptions made during computation

# Returns

An expression of the form `A⋅ω^c` where `A` is less rapidly varying than `ω`.
"""
function rewrite(expr::BasicSymbolic{Field}, ω::BasicSymbolic{Field},
        h::BasicSymbolic{Field}, x::BasicSymbolic{Field}, assumptions) where {Field}
    @assert exprtype(expr) == TERM && operation(expr) == exp
    @assert exprtype(ω) == SYM
    @assert exprtype(x) == SYM

    s = only(arguments(expr))
    t = h
    c = signed_limit_inf(s/t, x, assumptions)[1]
    @assert isfinite(c) && !iszero(c)
    exp(s-c*t)*ω^c # I wonder how this works with multiple variables...
end

"""
    get_series_term(expr, ω, h, i, assumptions)

Get the coefficient of `ω^i` in the series expansion of `expr` around the most rapidly varying term.

This function computes the `i`-th coefficient in the series expansion of `expr` in powers of `ω`,
where `ω` represents the expression `exp(h)`. The expansion takes the form:
`expr = c₀ + c₁⋅ω + c₂⋅ω² + ...`

This is a core component of the Gruntz algorithm for computing limits.

# Arguments

  - `expr`: The expression to expand
  - `ω`: A symbol representing the distinguished exponential `exp(h)`
  - `h`: The argument of the distinguished exponential
  - `i`: The power of `ω` for which to compute the coefficient
  - `assumptions`: A set to track assumptions made during computation

# Returns

The coefficient of `ω^i` in the series expansion of `expr`.
"""
function get_series_term(expr::BasicSymbolic{Field}, ω::BasicSymbolic{Field},
        h, i::Int, assumptions) where {Field}
    exprtype(ω) == SYM ||
        throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))

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
            exponent = get_leading_exponent(arg, ω, h, assumptions)
            t0 = get_series_term(arg, ω, h, exponent, assumptions)
            if i == 0
                _log(t0) + h*exponent # _log(t0 * ω^exponent), but get the cancelation right.
            else
                # TODO: refactor this to share code for the "sum of powers of a series" form
                sm = zero(Field)
                for k in 1:i # the sum starts at 1
                    term = i ÷ k
                    if term * k == i # integral
                        sm += (-get_series_term(
                            arg, ω, h, term+exponent, assumptions)/t0)^k/k
                    end
                end
                # TODO: All these for loops are ugly and error-prone
                # abstract this all away into a lazy series type to pay of the tech-debt.
                -sm
            end
        elseif op == exp
            i < 0 && return zero(Field)
            arg = only(arguments(expr))
            exponent = get_leading_exponent(arg, ω, h, assumptions)
            sm = i == 0 ? one(Field) : zero(Field) # k == 0 adds one to the sum
            if exponent == 0
                # e^c0 * sum (s-t0)^k/k!
                # TODO: refactor this to share code for the "sum of powers of a series" form
                for k in 1:i
                    term = i ÷ k
                    if term * k == i # integral
                        sm += get_series_term(arg, ω, h, term, assumptions)^k/factorial(k) # this could overflow... oh well. It'll error if it does.
                    end
                end
                sm * exp(get_series_term(arg, ω, h, exponent, assumptions))
            else
                @assert exponent > 0 # from the theory.
                # sum s^k/k!
                for k in 1:i
                    term = i ÷ k
                    if term * k == i && term >= exponent # integral and not structural zero
                        sm += get_series_term(arg, ω, h, term, assumptions)^k/factorial(k) # this could overflow... oh well. It'll error if it does.
                    end
                end
                sm
            end
        else
            error("Not implemented: $op")
        end
    elseif et == ADD
        sum(get_series_term(arg, ω, h, i, assumptions) for arg in arguments(expr))
    elseif et == MUL
        arg1, arg_rest = Iterators.peel(arguments(expr))
        arg2 = prod(arg_rest)
        exponent1 = get_leading_exponent(arg1, ω, h, assumptions)
        exponent2 = get_leading_exponent(arg2, ω, h, assumptions)
        sm = zero(Field)
        for j in exponent1:(i - exponent2)
            t1 = get_series_term(arg1, ω, h, j, assumptions)
            t2 = get_series_term(arg2, ω, h, i-j, assumptions)
            sm += t1 * t2
        end
        sm
    elseif et == POW
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        if exponent isa Real && isinteger(exponent) && exponent > 0
            t = i ÷ exponent
            if t * exponent == i # integral
                get_series_term(base, ω, h, t, assumptions) ^ exponent
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
        num_exponent = get_leading_exponent(num, ω, h, assumptions)
        den_exponent = get_leading_exponent(den, ω, h, assumptions)
        den_leading_term = get_series_term(den, ω, h, den_exponent, assumptions)
        @assert !zero_equivalence(den_leading_term, assumptions)
        sm = zero(Field)
        for j in num_exponent:(i + den_exponent)
            t_num = get_series_term(num, ω, h, j, assumptions)
            exponent = i+den_exponent-j
            # TODO: refactor this to share code for the "sum of powers of a series" form
            sm2 = exponent == 0 ? one(Field) : zero(Field) # k = 0 adds one to the sum
            for k in 1:exponent
                term = exponent ÷ k
                if term * k == exponent # integral
                    sm2 += (-get_series_term(
                        den, ω, h, term+den_exponent, assumptions)/den_leading_term)^k
                end
            end
            sm += sm2 * t_num
        end
        sm / den_leading_term
    else
        error("Unknown Expr type: $et")
    end
end
function get_series_term(
        expr::Field, ω::BasicSymbolic{Field}, h, i::Int, assumptions) where {Field}
    exprtype(ω) == SYM ||
        throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))
    i == 0 ? expr : zero(Field)
end

"""
    get_leading_exponent(expr, ω, h, assumptions)

Find the leading (smallest) exponent in the series expansion of `expr` in powers of `ω`.

This function determines the power of the leading term in the series expansion:
`expr = c_{e}⋅ω^e + c_{e+1}⋅ω^{e+1} + ...`
where `e` is the leading exponent (the smallest exponent with a non-zero coefficient).

Returns `Inf` if `expr` is equivalent to zero.

# Arguments

  - `expr`: The expression to analyze
  - `ω`: A symbol representing the distinguished exponential `exp(h)`
  - `h`: The argument of the distinguished exponential
  - `assumptions`: A set to track assumptions made during computation

# Returns

The leading exponent `e`, or `Inf` if `expr` is equivalent to zero.
"""
function get_leading_exponent(expr::BasicSymbolic{Field}, ω::BasicSymbolic{Field}, h, assumptions) where {Field}
    exprtype(ω) == SYM ||
        throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))

    zero_equivalence(expr, assumptions) && return Inf

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
            exponent = get_leading_exponent(arg, ω, h, assumptions)
            lt = get_series_term(arg, ω, h, exponent, assumptions)
            if !zero_equivalence(lt - one(Field), assumptions) # Is this right? Should we just use the generic loop from below for all cases?
                0
            else
                # There will never be a term with power less than 0, and the zero power term
                # is log(T0) which is handled above with the "isone" check.
                findfirst(
                    i -> zero_equivalence(get_series_term(expr, ω, h, i, assumptions), assumptions),
                    1:typemax(Int))
            end
        elseif op == exp
            0
        else
            error("Not implemented: $op")
        end
    elseif et == ADD
        exponent = minimum(get_leading_exponent(arg, ω, h, assumptions)
        for arg in arguments(expr))
        for i in exponent:typemax(Int)
            sm = sum(get_series_term(arg, ω, h, i, assumptions) for arg in arguments(expr))
            if !zero_equivalence(sm, assumptions)
                return i
            end
            i > exponent+1000 && error("This is likely due to known zero_equivalence bugs")
        end
    elseif et == MUL
        sum(get_leading_exponent(arg, ω, h, assumptions) for arg in arguments(expr))
    elseif et == POW # This is not an idiomatic representation of powers. Avoid it if possible.
        args = arguments(expr)
        @assert length(args) == 2
        base, exponent = args
        if exponent isa Real && isinteger(exponent) && exponent > 0
            exponent * get_leading_exponent(base, ω, h, assumptions)
        else
            error("Not implemented: POW with noninteger exponent $exponent. Transform to log/exp.")
        end
    elseif et == DIV
        args = arguments(expr)
        @assert length(args) == 2
        num, den = args
        # The naive answer is actually correct. See the get_series_term implementation for how.
        get_leading_exponent(num, ω, h, assumptions) -
        get_leading_exponent(den, ω, h, assumptions)
    else
        error("Unknown Expr type: $et")
    end
end
function get_leading_exponent(expr::Field, ω::BasicSymbolic{Field}, h, assumptions) where {Field}
    exprtype(ω) == SYM ||
        throw(ArgumentError("Must expand with respect to a symbol. Got $ω"))
    zero_equivalence(expr, assumptions) ? Inf : 0
end

_log(x) = _log(x, nothing, nothing)
_log(x, ω, h) = log(x)
function _log(x::BasicSymbolic, ω, h)
    exprtype(x) == TERM && operation(x) == exp && return only(arguments(x))
    x === ω && return h
    log(x)
end

"""
    zero_equivalence(expr, assumptions)

Determine if `expr` is equivalent to zero on its domain using heuristic methods.

This function uses symbolic simplification to determine if an expression is zero.
Since zero equivalence of general expressions is undecidable, this function uses heuristics
and records the result as an assumption that must hold for the computed limit to be correct.

The function applies strong log-exp simplification and algebraic expansion before testing
for zero equivalence.

# Arguments

  - `expr`: The expression to test for zero equivalence
  - `assumptions`: A set to record assumptions made (updated in-place)

# Returns

`true` if the expression is determined to be zero, `false` otherwise.

# Side Effects

Adds an assumption about the zero-equivalence of `expr` to the `assumptions` set.
"""
function zero_equivalence(expr, assumptions)
    res = iszero(simplify(strong_log_exp_simplify(expr), expand = true)) === true
    push!(assumptions, res ? iszero(expr) : !iszero(expr))
    res
end
