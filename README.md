# Sphere Packing in Lean

This project attempts to formalise some notions about Sphere Packing in Lean. Important links:

* [Project Dashboard](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/)
* [Blueprint (web version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/)
* [Dependency Graph (web version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/dep_graph_document.html)
* [Blueprint (PDF version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint.pdf)
* [API Documentation](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/docs/)

This project was kickstarted at EPFL by Maryna Viazovska and Sidharth Hariharan in March 2024. It is currently being maintained by Christopher Birkbeck, Sidharth Hariharan, Bhavik Mehta and Seewoo Lee. Contributions welcome!

## Adding Files

After adding new files, run `lake exe mk_all` to update the project "directory". (TODO: make this into a CI action)

## Blueprint

This project uses the [leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool by Patrick Massot. Please refer to the README there for the installation guide.

To use it, run `leanblueprint <pdf/web/all>` to build the pdf/web/both version of the blueprint. The built blueprint PDF is located at `blueprint/print/print.pdf`, while the built blueprint website can be accessed by first running `leanblueprint serve`, then accessing the appropriate link (e.g. https://localhost:8000).

To modify the blueprint, modify `blueprint/src/content.tex` or any of the files it includes. All the usual $\LaTeX$ stuff is available, but there are additional macros specific to leanblueprint:

- `\lean{lem1, Proj.File.lem2}` indicates that the theorem (or definition) requires `lem1` and `Proj.File.lem2` **from Lean**.
- `\leanok` indicates the proof is complete.
- `\uses{thm:label1, ref:label2}` means the proof uses the theorems labelled by `\label{thm:label1}` and `\label{ref:label2}` **from LaTeX**.

## Contributing to the Project

Should you wish to make any contributions to the content of the project, please add them to a new branch and make a pull request. Your PR will need to satisfy certain status checks, be approved by a reviewer and have no conflicts with the base branch before it can be merged. Please read [CONTRIBUTING.md](/CONTRIBUTING.md) for details.
