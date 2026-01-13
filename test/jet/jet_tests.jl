using Pkg
Pkg.activate(@__DIR__)
Pkg.develop(PackageSpec(path = dirname(dirname(@__DIR__))))
Pkg.instantiate()

using SymbolicLimits
using Test
using JET

@testset "Static analysis (JET.jl)" begin
    JET.report_package("SymbolicLimits"; target_defined_modules = true)
end
