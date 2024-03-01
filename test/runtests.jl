using SymbolicLimits
using Test
using Aqua

@testset "SymbolicLimits.jl" begin
    @testset "Code quality (Aqua.jl)" begin
        Aqua.test_all(SymbolicLimits)
    end
    # Write your tests here.
end
