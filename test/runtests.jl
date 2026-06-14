using SymbolicLimits, SymbolicUtils
using SafeTestsets
using Test

const GROUP = get(ENV, "GROUP", "All")

if GROUP == "QA"
    using Pkg
    Pkg.activate(joinpath(@__DIR__, "qa"))
    Pkg.develop(PackageSpec(path = dirname(@__DIR__)))
    Pkg.instantiate()
    include(joinpath(@__DIR__, "qa", "qa.jl"))
end

if GROUP == "All" || GROUP == "Core"
    @testset "SymbolicLimits.jl" begin
        @safetestset "Tests that failed during initial development phase 1" begin
            include("development_phase_1.jl")
        end

        @safetestset "Tests that failed during initial development phase 2" begin
            include("development_phase_2.jl")
        end

        @safetestset "Examples from Gruntz's 1996 thesis" begin
            include("gruntz_thesis.jl")
        end

        @safetestset "Two sided limits" begin
            include("two_sided_limits.jl")
        end

        @safetestset "Limits approaching -Inf (issue #13)" begin
            include("limits_approaching_neg_inf.jl")
        end
    end
end
