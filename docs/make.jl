using SymbolicLimits
using Documenter

DocMeta.setdocmeta!(SymbolicLimits, :DocTestSetup, :(using SymbolicLimits); recursive=true)

makedocs(;
    modules=[SymbolicLimits],
    authors="Lilith Orion Hafner <lilithhafner@gmail.com> and contributors",
    repo="https://github.com/LilithHafner/SymbolicLimits.jl/blob/{commit}{path}#{line}",
    sitename="SymbolicLimits.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://LilithHafner.github.io/SymbolicLimits.jl",
        edit_link="main",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/LilithHafner/SymbolicLimits.jl",
    devbranch="main",
)
