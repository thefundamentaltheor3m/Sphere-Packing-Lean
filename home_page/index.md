---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

# Formalising Sphere Packing in Lean

In 2022, Maryna Viazovska was awarded the Fields Medal for solving the sphere packing problem in dimension $$8$$. This project formalises this result in the [Lean Theorem Prover](https://leanprover-community.github.io) following her [original paper](https://doi.org/10.4007/annals.2017.185.3.7) and [followup calculations by Lee](https://doi.org/10.48550/arXiv.2406.14659). It is an online, open-source collaboration currently being led by Christopher Birkbeck, Sidharth Hariharan, Bhavik Mehta and Seewoo Lee. If you'd like to contribute, you may find the following links useful!

* [Zulip chat](https://leanprover.zulipchat.com/#narrow/channel/509682-Sphere-packing-in-8-dimensions) for coordination
* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [Doc pages for this repository]({{ site.url }}/docs/)
* [Project dashboard](https://github.com/users/thefundamentaltheor3m/projects/2/views/1)
* [Viazovska's original paper](https://doi.org/10.4007/annals.2017.185.3.7)

## Contributing

1. Make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html).
2. Download the repository using `git clone https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean.git`.
3. Run `lake exe cache get!` to download built dependencies (this speeds up the build process).
4. Run `lake build` to build all files in this repository.
5. Read the [CONTRIBUTING.md](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/main/CONTRIBUTING.md) file in the repository for more information on how to contribute.

For more on getting started with Lean, visit the [course repository](https://github.com/b-mehta/formalising-mathematics-notes) for MATH60040/70040, Formalising Mathematics, taught by Bhavik Mehta at Imperial College London in Spring 2025.
