import Mathlib

/-!
# Linear arithmetic context inspection experiment

The `smart_lia` tactic logs the visible declarations and the goal, distinguishing
propositional hypotheses from other declarations. The example closes the goal with a
separate call to `linarith`. This file is outside the FFSOL rule checker and the
library build.
-/

open Lean Meta Elab Tactic

/--
Collects the free variable identifiers of a Lean metaprogramming expression.
-/
def getFVars (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

elab "smart_lia" : tactic => do
  withMainContext do
    let target ← getMainTarget

    let lctx ← getLCtx

    for localDecl in lctx do
      unless localDecl.isImplementationDetail do
        let isHypothesis ← isProp localDecl.type

        if isHypothesis then
          let vars := getFVars localDecl.type
          logInfo m!"HYP: {localDecl.userName} : {localDecl.type}"

        else
          logInfo m!"VAR: {localDecl.userName} : {localDecl.type}"
    logInfo m!"Goal: {target}"

example (x : Int) (hx : x ≤ 3) : x ≤ 10 := by
  smart_lia
  linarith
