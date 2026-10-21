import Mathlib

open Lean Meta Elab Tactic

def runCleanupGrind : TacticM Unit := do
  let goal ← getMainGoal
  let cleanGoal ← goal.cleanup
  replaceMainGoal [cleanGoal]
  evalTactic (← `(tactic| grind))

elab "cleanup_grind" : tactic =>
  runCleanupGrind

elab "timed " t:tactic : tactic => do
  let t0 ← IO.monoNanosNow
  evalTactic t
  let t1 ← IO.monoNanosNow
  logInfo m!"{(t1 - t0).toFloat / 1e6} ms"

example
    (x y z : Nat)

    (a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ : Nat)
    (a₆ b₆ a₇ b₇ a₈ b₈ a₉ b₉ a₁₀ b₁₀ : Nat)
    (a₁₁ b₁₁ a₁₂ b₁₂ a₁₃ b₁₃ a₁₄ b₁₄ a₁₅ b₁₅ : Nat)
    (a₁₆ b₁₆ a₁₇ b₁₇ a₁₈ b₁₈ a₁₉ b₁₉ a₂₀ b₂₀ : Nat)
    (a₂₁ b₂₁ a₂₂ b₂₂ a₂₃ b₂₃ a₂₄ b₂₄ a₂₅ b₂₅ : Nat)
    (a₂₆ b₂₆ a₂₇ b₂₇ a₂₈ b₂₈ a₂₉ b₂₉ a₃₀ b₃₀ : Nat)

    (h₁ : a₁ = b₁)
    (h₂ : a₂ = b₂)
    (h₃ : a₃ = b₃)
    (h₄ : a₄ = b₄)
    (h₅ : a₅ = b₅)
    (h₆ : a₆ = b₆)
    (h₇ : a₇ = b₇)
    (h₈ : a₈ = b₈)
    (h₉ : a₉ = b₉)
    (h₁₀ : a₁₀ = b₁₀)
    (h₁₁ : a₁₁ = b₁₁)
    (h₁₂ : a₁₂ = b₁₂)
    (h₁₃ : a₁₃ = b₁₃)
    (h₁₄ : a₁₄ = b₁₄)
    (h₁₅ : a₁₅ = b₁₅)
    (h₁₆ : a₁₆ = b₁₆)
    (h₁₇ : a₁₇ = b₁₇)
    (h₁₈ : a₁₈ = b₁₈)
    (h₁₉ : a₁₉ = b₁₉)
    (h₂₀ : a₂₀ = b₂₀)
    (h₂₁ : a₂₁ = b₂₁)
    (h₂₂ : a₂₂ = b₂₂)
    (h₂₃ : a₂₃ = b₂₃)
    (h₂₄ : a₂₄ = b₂₄)
    (h₂₅ : a₂₅ = b₂₅)
    (h₂₆ : a₂₆ = b₂₆)
    (h₂₇ : a₂₇ = b₂₇)
    (h₂₈ : a₂₈ = b₂₈)
    (h₂₉ : a₂₉ = b₂₉)
    (h₃₀ : a₃₀ = b₃₀)
    (hxy : x = y)
    (hyz : y = z)

    :
    x = z := by
  timed cleanup_grind
