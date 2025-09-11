using SymbolicLimits
using Documenter

DocMeta.setdocmeta!(SymbolicLimits, :DocTestSetup, :(using SymbolicLimits); recursive = true)

makedocs(;
    modules = [SymbolicLimits],
    authors = "Lilith Orion Hafner <lilithhafner@gmail.com> and contributors",
    sitename = "SymbolicLimits.jl",
    format = Documenter.HTML(;
        prettyurls = get(ENV, "CI", "false") == "true",
        edit_link = "main",
        assets = String[]
    ),
    pages = [
        "Home" => "index.md",
    ]
)

deploydocs(;
    repo = "github.com/SciML/SymbolicLimits.jl",
    devbranch = "main"
)
