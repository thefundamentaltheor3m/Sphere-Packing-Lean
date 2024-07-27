# Sphere Packing in Lean

This is a (very nascent) project attempting to formalise some notions about Sphere Packing in Lean. Important links:

* [Blueprint (web version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/)
* [Dependency Graph (web version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/dep_graph_document.html)
* [Blueprint (PDF version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint.pdf)
* [API Documentation](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/docs/)

Contributors: Maryna Viazovska (EPFL), Sidharth Hariharan (Imperial College London/EPFL)

We would also like to extend our sincere thanks to Kevin Buzzard and Utensil Song for their support in this endeavour.

## Adding Files

After adding new files, run `lake exe mk_all` to update the project "directory". (TODO: make this into a CI action)

## Blueprint

This project uses the [leanblueprint](https://github.com/PatrickMassot/leanblueprint) tool by Patrick Massot. Please refer to the README there for the installation guide.

To use it, run `leanblueprint <pdf/web/all>` to build the pdf/web/both version of the blueprint. The built blueprint PDF is located at `blueprint/print/print.pdf`, while the built blueprint website can be accessed by first running `leanblueprint serve`, then accessing the appropriate link (e.g. https://localhost:8000).

To modify the blueprint, modify `blueprint/src/content.tex` or any of the files it includes. All the usual $\LaTeX$ stuff is available, but there are additional macros specific to leanblueprint:

- `\lean{lem1, Proj.File.lem2}` indicates that the theorem (or definition) requires `lem1` and `Proj.File.lem2` **from Lean**.
- `\leanok` indicates the proof is complete.
- `\uses{thm:label1, ref:label2}` means the proof uses the theorems labelled by `\label{thm:label1}` and `\label{ref:label2}` **from LaTeX**.
