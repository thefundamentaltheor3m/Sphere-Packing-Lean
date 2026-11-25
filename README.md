# Sphere Packing in Lean

This project attempts to formalise some notions about Sphere Packing in Lean. Important links:

* [Landing Page](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/)
* [Zulip Chat](https://leanprover.zulipchat.com/#narrow/channel/509682-Sphere-packing-in-8-dimensions)
* [GitHub Project Page](https://github.com/users/thefundamentaltheor3m/projects/2/views/1)
* [Blueprint (web version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/)
* [Dependency Graph (web version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint/dep_graph_document.html)
* [Blueprint (PDF version)](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/blueprint.pdf)
* [API Documentation](https://thefundamentaltheor3m.github.io/Sphere-Packing-Lean/docs/)

This project was kickstarted at EPFL by Maryna Viazovska and Sidharth Hariharan in March 2024. It is currently being maintained by Christopher Birkbeck, Sidharth Hariharan, Bhavik Mehta and Seewoo Lee. Contributions welcome: see below for more details.

## Building

The project depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and [Tau Ceti](https://github.com/TauCetiProject/TauCeti). To download prebuilt oleans for both and then build:

```bash
lake exe cache get
lake build
```

As in any Mathlib project, `lake exe cache get` downloads Mathlib's oleans. Here it also downloads the oleans of the Tau Ceti modules this project imports, from Tau Ceti's public cache (see `scripts/Cache.lean`). Mathlib's own tool is still available as `lake exe mathlib/cache`. Rerun `lake exe cache get` after `lake update` or after importing a Tau Ceti module for the first time; otherwise Lake compiles that module and its Tau Ceti dependencies from source.

## Contributing to the Project

Should you wish to make any contributions to the content of the project, please add them to a new branch and make a pull request. Your PR will need to satisfy certain status checks, be approved by a reviewer and have no conflicts with the base branch before it can be merged. Please read [CONTRIBUTING.md](/CONTRIBUTING.md) for details.

## Acknowledgements

We are grateful to all contributors for their effort. We would also like to thank the Mathlib maintainers and the Lean community for their support. We are indebted to the Institute for Computer-Aided Reasoning in Mathematics for their help on matters of AI policy. Finally, we would like to thank G-Research for their generosity in partially supporting this research.
