import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SpherePackingBlueprint.Chapters.SpherePackings
import SpherePackingBlueprint.Chapters.PackingsDensity
import SpherePackingBlueprint.Chapters.E8
import SpherePackingBlueprint.Chapters.FourierAnalysis
import SpherePackingBlueprint.Chapters.CohnElkies
import SpherePackingBlueprint.Chapters.ModularForms
import SpherePackingBlueprint.Chapters.FourierEigenfunctions
import SpherePackingBlueprint.Chapters.ProofOfG
import SpherePackingBlueprint.Chapters.References

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sphere Packing in Lean" =>

%%%
authors := ["Christopher Birkbeck", "Sidharth Hariharan", "Seewoo Lee", "Gareth Ma", "Bhavik Mehta", "Maryna Viazovska"]
%%%

This blueprint consists of an adaptation of Maryna Viazovska's Fields Medal-winning paper proving
that no packing of unit balls in Euclidean space $`\mathbb{R}^8` has density greater than that of
the $`E_8`-lattice packing.

This formalisation project was kickstarted at EPFL by Maryna Viazovska and Sidharth Hariharan,
and the contents of this blueprint were originally written by Maryna Viazovska on the suggestion
of Kevin Buzzard. It is being updated and restructured by those involved in the formalisation
effort. We express our sincere gratitude to Jeremy Avigad, Kevin Buzzard, David Loeffler, Pietro
Monticone, David Renshaw, Utensil Song, the Mathlib maintainers, the Institute for Computer-Aided
Reasoning in Mathematics, and everyone in the Lean Community for their invaluable contributions
and support.

{include 0 SpherePackingBlueprint.Chapters.SpherePackings}
{include 0 SpherePackingBlueprint.Chapters.PackingsDensity}
{include 0 SpherePackingBlueprint.Chapters.E8}
{include 0 SpherePackingBlueprint.Chapters.FourierAnalysis}
{include 0 SpherePackingBlueprint.Chapters.CohnElkies}
{include 0 SpherePackingBlueprint.Chapters.ModularForms}
{include 0 SpherePackingBlueprint.Chapters.FourierEigenfunctions}
{include 0 SpherePackingBlueprint.Chapters.ProofOfG}
{include 0 SpherePackingBlueprint.Chapters.References}

{blueprint_graph}
{blueprint_summary}
