import VersoManual
import VersoBlueprint.PreviewManifest
import SpherePackingBlueprint

open Verso Doc
open Verso.Genre Manual

/-- Generator entry point of the blueprint site (`lake exe vbp build`). -/
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc SpherePackingBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
