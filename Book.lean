import VersoManual

import Book.FP

open Verso.Genre Manual
open Verso Code External

open Verso Doc Elab in
open Lean (quote) in

@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do
    let version ← IO.FS.readFile "../lean-toolchain"
    let version := version.stripPrefix "leanprover/lean4:" |>.trim
    pure #[← ``(Verso.Doc.Inline.code $(quote version))]
  | _, _ => throwError "Unexpected arguments"


#doc (Manual) "Functional Algorithms Design" =>

%%%
authors := ["Alexandre Rademaker"]
authorshipNote := some "with contributions from the Lean Community and my students"
%%%

This version of the text assumes you’re using Lean 4 (specifically {versionString}[]). See the
[Quickstart section](https://lean-lang.org/documentation/setup/) of
the Lean documentation to install Lean.


{include 1 Fad.FP}
