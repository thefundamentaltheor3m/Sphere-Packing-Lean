---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

# Formalising Sphere Packing in Lean

On 5 July, 2022, in Helsinki, Finland, the International Mathematical Union announced the names of the four mathematicians who were to be awarded the Fields Medal, the most coveted prize in the world of mathematics: Hugo Duminil-Copin, June Huh, James Maynard and Maryna Viazovska. Duminil-Copin, Huh and Maynard received this most prestigious honour for making several outstanding contributions to their specific fields of expertise---respectively, statistical physics, geometric combinatorics, and analytic number theory. Viazovska, on the other hand, was awarded the Fields Medal for a distinct, outstanding conceptual brilliancy: proving the optimality of the $E_8$ sphere packings in $\mathbb{R}^8$. Her solution exploited the myriad symmetries of the theory of modular forms to construct a special function---the so-called Magic Function---that, in combination with a previous result by Cohn and Elkies, solves the problem. Very shortly afterwards, Cohn, Kumar, Miller, Radchenko and Viazovska were able to use similar ideas to prove that the Leech lattice packing is the densest possible sphere packing in $\mathbb{R}^{24}$.

This project (a WIP) aims to formalise Viazovska's brilliant solution in the [Lean Theorem Prover](https://leanprover-community.github.io). It is an online, open-source collaboration currently being led by Christopher Birkbeck, Sidharth Hariharan, Bhavik Mehta and Seewoo Lee. If you'd like to contribute, you may find the following links useful!

* [Zulip chat](https://leanprover.zulipchat.com/) for coordination
* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [Doc pages for this repository]({{ site.url }}/docs/)
* [Viazovska's original paper](https://doi.org/10.4007/annals.2017.185.3.7)

## A Mathematical Overview

At first, the task of optimisng the density of packings of eight-dimensional spheres seems immensely daunting: how does one even visualise one eight-dimensional sphere, let alone an infinite arrangement of them, and how does one prove that one particular arrangement of them, the $E_8$ lattice packing, cannot further be improved? In 2003, Henry Cohn and Noam Elkies overcame this geometric challenge by constructing, for any $n \in \mathbb{N}$, a family of upper-bounds on all sphere packings in $\mathbb{R}^n$ indexed by functions $f : \mathbb{R}^n \to \mathbb{R}$ that satisfy certain properties. This offered a new approach to solving the sphere packing problem in $\mathbb{R}^n$: finding a 'magic function' $f : \mathbb{R}^n \to \mathbb{R}$ satisfying these properties with its corresponding upper-bound being exactly equal to the density of a known sphere packing in $\mathbb{R}^n$.

Despite numerical evidence suggesting strongly that this approach was viable in dimensions $8$ and $24$, it turned out to be immensely difficult to construct magic functions whose corresponding upper-bounds were respectively the densities of the $E_8$ and Leech lattices. One reason for this is that such functions need to exhibit a degree of symmetry in order to satisfy Cohn and Elkies's conditions. Viazovska's solution was to construct such a function using modular forms, and has since developed a rich theory of magic functions and universal optimality.

Even before Viazovska was awarded the Fields Medal, her work received wide acclaim from eminent mathematicians across the world: Peter Sarnak described it as "stunningly simple, as all great things are"; Akshay Venkatesh remarked that her Magic Function is very likely "part of some richer story" that connects to other areas of mathematics and physics; and Henry Cohn described her as a "master of special functions", comparing her to historical giants like Ramanujan and Jacobi. Formalising work as significant as Viazovska's, at the very forefront of modern mathematics, so soon after it received the most coveted honour in the mathematical world, will be a landmark achievement in formal theorem proving.

## Contributing

1. Make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html).
2. Download the repository using `git clone https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean.git`.
3. Run `lake exe cache get!` to download built dependencies (this speeds up the build process).
4. Run `lake build` to build all files in this repository.

For more information on how to get started with Lean, visit the [course repository](https://github.com/b-mehta/formalising-mathematics-notes) for MATH60040/70040, Formalising Mathematics, taught by Bhavik Mehta at Imperial College London in Spring 2025.
