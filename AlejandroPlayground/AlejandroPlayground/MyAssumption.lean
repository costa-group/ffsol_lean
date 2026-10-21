import Mathlib

open Lean Elab Meta Tactic

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
