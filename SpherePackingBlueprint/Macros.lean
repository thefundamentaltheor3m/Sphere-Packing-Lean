import VersoBlueprint

/-!
TeX macros shared by all blueprint chapters (the Verso counterpart of the old
`blueprint/src/macros/common.tex`). Every chapter imports this module.
-/

tex_prelude r#"
\def\R{\mathbb{R}}
\def\Z{\mathbb{Z}}
\def\C{\mathbb{C}}
\def\N{\mathbb{N}}
\def\Q{\mathbb{Q}}
\def\h{\mathfrak{H}}
\def\B{\mathcal{B}}
\def\Pa{\mathcal{P}}
\def\Vol#1{\operatorname{Vol}\!\left(#1\right)}
\def\Bd#1{\B_d\!\left(#1\right)}
\def\dd{\mathrm{d}}
\def\rad{\mathrm{rad}}
\def\set#1{\left\{ #1 \right\}}
\def\setof#1#2{\left\{ #1 \; \middle| \; #2 \right\}}
\def\abs#1{\left\lvert #1 \right\rvert}
\def\norm#1{\left\lVert #1 \right\rVert}
\def\ang#1{\left\langle #1 \right\rangle}
\def\eps{\varepsilon}
"#
