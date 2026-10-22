import mathlib

structure pConfig where
  p : Nat
  p_prime : p.Prime

inductive Expr (pc : pConfig) where
  | var (n : Nat)
  | const (c : ZMod pc.p)
  | add (e1 : Expr pc) (e2 : Expr pc)
  | neg (e : Expr pc)
  | mul (e1 : Expr pc) (e2 : Expr pc)
  deriving DecidableEq

inductive Cstr (pc : pConfig) where
  | eqz : Expr pc → Cstr pc
  | nez : Expr pc → Cstr pc
  deriving DecidableEq

inductive Clause (pc : pConfig) where
  | cstr : Cstr pc → Clause pc
  | or : Clause pc → Clause pc → Clause pc
  deriving DecidableEq

def Expr.eval {pc : pConfig} (ρ : Nat → ZMod pc.p) : Expr pc → ZMod pc.p
  | .var n => ρ n
  | .const c => c
  | .add e1 e2 => e1.eval ρ + e2.eval ρ
  | .mul e1 e2 => e1.eval ρ * e2.eval ρ
  | .neg e => - e.eval ρ

def Cstr.holds {pc : pConfig} (ρ : Nat → ZMod pc.p) : Cstr pc → Prop
  | .eqz e => e.eval ρ = 0
  | .nez e => e.eval ρ ≠ 0

def Clause.holds {pc : pConfig} (ρ : Nat → ZMod pc.p) : Clause pc  → Prop
  | .cstr c => c.holds ρ
  | .or c1 c2 => c1.holds ρ ∨ c2.holds ρ

abbrev Ctx (pc : pConfig) := List (Clause pc)

def Ctx.holds {pc : pConfig} (ρ : Nat → ZMod pc.p) (Γ : Ctx pc) : Prop := ∀ c ∈ Γ, c.holds ρ

-- Rule e1 * e2 + e1 * e3 = 0 ↔ e1 * (e2 + e3) = 0
def ruleDistrib {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | Clause.cstr (.eqz (.add (.mul e1 e2) (.mul e1' e3))),
    Clause.cstr (.eqz (.mul e1'' (.add e2' e3'))) =>
    e1 = e1' ∧ e1 = e1'' ∧ e2 = e2' ∧ e3 = e3'
  | _, _ => false

theorem ruleDistribSound {pc : pConfig} {Γ : Ctx pc} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
 ruleDistrib g c = true → c.holds ρ := by
  -- Otra vez, desenvolvemos y le pasamos la pelota a simpa con mul_add
  intro hdist
  simp only [ruleDistrib] at hdist
  split at hdist
  apply h at hg
  simp only [Clause.holds, Cstr.holds, Expr.eval] at *
  simp at hdist
  rcases hdist with ⟨he1, he2, he3, he4⟩
  rw [← he2, ← he3, ← he4]
  rw [← he1] at hg
  simpa only [mul_add] using hg

  contradiction
