# SymbolicLimits

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://docs.sciml.ai/SymbolicLimits/stable/)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://docs.sciml.ai/SymbolicLimits/dev/)
[![Build Status](https://github.com/SciML/SymbolicLimits.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/SciML/SymbolicLimits.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/SciML/SymbolicLimits.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/SciML/SymbolicLimits.jl)
[![PkgEval](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/S/SymbolicLimits.svg)](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/S/SymbolicLimits.html)
[![Aqua](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)

# Limitations of computing symbolic limits

Zero equivalence of log-exp functions is undecidable and reducible to computing symbolic limits. Specifically, to
determine if the expression `x` is zero, compute the limit `limit(ϵ/(x + ϵ), ϵ, 0)`, which is 1 if `x == 0` and 0
if `x != 0`. This package implements a reduction in the reverse direction and always produces an answer and
terminates. To avoid the undecidability issue, SymbolicLimits utilizes a heuristic iszero detector and tracks all
its results as assumptions. The returned result is correct if the assumptions all hold. In practice, the heuristic
is pretty good and the assumptions typically all hold.

# API

The `limit` function is the whole of the public API of this package.

`limit(expr, var, h[, side::Symbol])`

Compute the limit of `expr` as `var` approaches `h` and return `(limit, assumptions)`. If
all the `assumptions` are true, then the returned `limit` is correct.

`side` indicates the direction from which `var` approaches `h`. It may be one of `:left`,
`:right`, or `:both`. If `side` is `:both` and the two sides do not align, an error is
thrown. Side defaults to `:both` for finite `h`, `:left` for `h = Inf`, and `:right` for
`h = -Inf`.

## Demo

```julia
using Pkg;
pkg"activate --temp";
pkg"add SymbolicLimits";
pkg"add SymbolicUtils" # slow

using SymbolicLimits, SymbolicUtils # slow

@syms x::Real

limit(exp(x+exp(-x))-exp(x), x, Inf)[1] == 1 # slow

# the rest is fast

limit(-1/x, x, Inf)[1]
limit(-x / log(x), x, Inf)[1]
limit(exp(x+exp(-x))-exp(x), x, Inf)[1]
limit(x^7/exp(x), x, Inf)[1]
limit(x^70000/exp(x), x, Inf)[1]
limit(log(log(x*exp(x*exp(x))+1))-exp(exp(log(log(x))+1/x)), x, Inf)[1]
```
