# SymbolicLimits

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://LilithHafner.github.io/SymbolicLimits.jl/stable/)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://LilithHafner.github.io/SymbolicLimits.jl/dev/)
[![Build Status](https://github.com/LilithHafner/SymbolicLimits.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/LilithHafner/SymbolicLimits.jl/actions/workflows/CI.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/LilithHafner/SymbolicLimits.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/LilithHafner/SymbolicLimits.jl)
[![PkgEval](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/S/SymbolicLimits.svg)](https://JuliaCI.github.io/NanosoldierReports/pkgeval_badges/S/SymbolicLimits.html)
[![Aqua](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)

# Demo

```julia
using Pkg; pkg"activate --temp"; pkg"add https://github.com/LilithHafner/SymbolicLimits.jl"; pkg"add SymbolicUtils" # slow

using SymbolicLimits, SymbolicUtils # slow

@syms x::Real

limit(exp(x+exp(-x))-exp(x), x) == 1 # slow

# the rest is fast

limit(-1/x, x)
limit(-x / log(x), x)
limit(exp(x+exp(-x))-exp(x), x)
limit(x^7/exp(x), x)
limit(x^70000/exp(x), x)

limit(log(log(x*exp(x*exp(x))+1))-exp(exp(log(log(x))+1/x)), x) # wrong
```
