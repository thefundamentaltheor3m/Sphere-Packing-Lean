import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The $`E_8` lattice" =>

# Definitions of $`E_8` lattice

There are several equivalent definitions of the $`E_8` lattice. Below, we formalise two of them,
and prove they are equivalent.

:::definition "E8-Set" (lean := "Submodule.E8")
*($`E_8`-lattice, Definition 1)* We define the *$`E_8`-lattice* (as a subset of $`\R^8`) to be
$$`\Lambda_8=\{(x_i)\in\Z^8\cup(\Z+\textstyle\frac12\displaystyle )^8|\;\sum_{i=1}^8x_i\equiv 0\;(\mathrm{mod\;2})\}.`
:::

:::definition "E8-Matrix" (lean := "E8Matrix")
*($`E_8`-lattice, Definition 2)* We define the *$`E_8` basis vectors* to be the set of vectors
$$`\B_8 = \left\{ \begin{bmatrix} 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0 \end{bmatrix}, \begin{bmatrix} 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0 \end{bmatrix}, \begin{bmatrix} 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \end{bmatrix}, \begin{bmatrix} 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \end{bmatrix}, \begin{bmatrix} 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \end{bmatrix}, \begin{bmatrix} 0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ 1 \\ 0 \end{bmatrix}, \begin{bmatrix} -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \end{bmatrix}, \begin{bmatrix} 0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \end{bmatrix} \right\}`
:::

:::theorem "E8-defs-equivalent" (lean := "span_E8Matrix") (uses := "E8-Set, E8-Matrix")
The two definitions above coincide, i.e. $`\Lambda_8 = \mathrm{span}_{\Z}(\B_8)`.
:::

:::proof "E8-defs-equivalent"
We prove each side contains the other side.

For a vector $`\vec{v} \in \Lambda_8 \subseteq \R^8`, we have $`\sum_i \vec{v}_i \equiv 0 \pmod{2}`
and $`\vec{v}_i` being either all integers or all half-integers. After some modulo arithmetic, it
can be seen that $`\B_8^{-1}\vec{v}` as integer coordinates (i.e. it is congruent to $`0` modulo
$`1`). Hence, $`\vec{v} \in \mathrm{span}_{\Z}(\B_8)`.

For the opposite direction, we write the vector as
$`\vec{v} = \sum_i c_i\B_8^i \in \mathrm{span}_{\Z}(\B_8)` with $`c_i` being integers and
$`\B_8^i` being the $`i`-th basis vector. Expanding the definition then gives
$`\vec{v} = \left(c_1 - \frac{1}{2}c_7, -c_1 + c_2 - \frac{1}{2}c_7, \cdots, -\frac{1}{2}c_7\right)`.
Again, after some modulo arithmetic, it can be seen that $`\sum_i \vec{v}_i` is indeed $`0` modulo
$`2` and are all either integers and half-integers, concluding the proof.

(Note: this proof doesn't depend on that $`\B_8` is linearly independent.)
:::

# Basic Properties of $`E_8` lattice

In this section, we establish basic properties of the $`E_8` lattice and the $`\B_8` vectors.

:::lemma_ "E8-is-basis" (lean := "span_E8Matrix_eq_top") (uses := "E8-Matrix")
$`B_8` is a $`\R`-basis of $`\R^8`.
:::

:::proof "E8-is-basis"
It suffices to prove that $`\B_8 \in \mathrm{GL}_8(\R)`. We prove this by explicitly defining the
inverse matrix $`\B_8^{-1}` and proving $`\B_8 \B_8^{-1} = I_8`, which implies that
$`\det(\B_8)` is nonzero. See the Lean code for more details.,
:::

:::lemma_ "E8-Lattice" (lean := "E8Lattice") (uses := "E8-Set, E8-defs-equivalent")
$`\Lambda_8` is an additive subgroup of $`\R^8`.
:::

:::proof "E8-Lattice"
Trivially follows from that $`\Lambda_8 \subseteq \R^8` is the $`\Z`-span of $`\B_8` and hence an
additive group.
:::

:::lemma_ "E8-vector-norms" (lean := "E8_norm_eq_sqrt_even") (uses := "E8-defs-equivalent")
All vectors in $`\Lambda_8` have norm of the form $`\sqrt{2n}`, where $`n` is a nonnegative
integer.
:::

:::proof "E8-vector-norms"
Writing $`\vec{v} = \sum_i c_i\B_8^i`, we have
$`\|v\|^2 = \sum_i \sum_j c_ic_j (\B_8^i \cdot \B_8^j)`. Computing all $`64` pairs of dot products
and simplifying, we get a massive term that is a quadratic form in $`c_i` with even integer
coefficients, concluding the proof.
:::

:::lemma_ "instDiscreteE8Lattice" (lean := "instDiscreteE8Lattice") (uses := "E8-vector-norms")
$`c\Lambda_8` is discrete, i.e. that the subspace topology induced by its inclusion into $`\R^8` is
the discrete topology.
:::

:::proof "instDiscreteE8Lattice"
Since $`\Lambda_8` is a topological group and $`+` is continuous, it suffices to prove that
$`\{0\}` is open in $`\Lambda_8`. This follows from the fact that there is an open ball
$`\B(\sqrt{2}) \subseteq \R^8` around it containing no other lattice points, since the shortest
nonzero vector has norm $`\sqrt{2}`.
:::

:::lemma_ "instLatticeE8" (lean := "instIsZLatticeE8Lattice") (uses := "instDiscreteE8Lattice, E8-is-basis")
$`c\Lambda_8` is a $`\Z`-lattice, i.e. it is discrete and spans $`\R^8` over $`\R`.
:::

:::proof "instLatticeE8"
The first part is by {bpref "instDiscreteE8Lattice"}[], and the second part follows from that
$`\B_8` is a basis ({bpref "E8-is-basis"}[]) and hence linearly independent over $`\R`.
:::

*TODO: Prove $`E_8` is unimodular.*

*TODO: Prove $`E_8` is positive-definite.*

# The $`E_8` sphere packing

:::definition "E8Packing" (lean := "E8Packing") (uses := "E8-Lattice, E8-vector-norms")
The *$`E_8` sphere packing* is the (periodic) sphere packing with separation $`\sqrt{2}`, whose set
of centres is $`\Lambda_8`.
:::

:::lemma_ "E8Packing-covol" (lean := "E8Basis_volume") (uses := "E8Packing")
$`\Vol{\Lambda_8} = \mathrm{Covol}(\R^8 / \Lambda_8) = 1`.
:::

:::proof "E8Packing-covol"
*TODO: In theory this should follow directly from $`\det(\Lambda_8) = 1`, but Lean hates me and
`EuclideanSpace` is being annoying.*
:::

:::theorem "E8Packing-density" (lean := "E8Packing_density") (uses := "theorem:psp-density, E8Packing-covol")
We have $`\Delta_{\mathcal{P}(E_8)} = \frac{\pi^4}{384}`.
:::

:::proof "E8Packing-density"
By {bpref "theorem:psp-density"}[], we have
$`\Delta_{\mathcal{P}(E_8)} = |E_8 / E_8| \cdot \frac{\Vol{\mathcal{B}_8(\sqrt{2} / 2)}}{\mathrm{Covol}(E_8)} = \frac{\pi^4}{384}`,
where the last equality follows from {bpref "E8Packing-covol"}[] and the formula for volume of a
ball: $`\Vol{\mathcal{B}_d(R)} = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)`.
:::
