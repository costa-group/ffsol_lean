import Mathlib

open Lean Meta Elab Tactic

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
