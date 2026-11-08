import Mathlib

/-!
# Local hypothesis lookup experiment

This helper searches the Lean proof context for a hypothesis that can close the current
goal by definitional equality. It is a tactic experiment outside the FFSOL rule checker
and the library build.
-/

open Lean Elab Meta Tactic

/--
Tries the default local declarations in context order and closes the goal with the first
definitionally matching hypothesis. Raises an error if none matches.
-/
def myAssumption : TacticM Unit :=
  withMainContext do
    let goal <- getMainGoal
    let lctx <- getLCtx
    for (decl : LocalDecl) in lctx do
      if decl.kind != .default then continue
        try
          goal.assignIfDefEq (Expr.fvar decl.fvarId)
          return
        catch _ =>
          pure ()
    throwError "No matching hypothesis found"
