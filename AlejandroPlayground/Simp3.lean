import mathlib

structure pConfig where
  p : Nat
  p_prime : p.Prime

/- Register that c.p is a prime number -/
instance (c : pConfig) : Fact c.p.Prime := ⟨c.p_prime⟩

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

def ruleDistribEqZero {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | Clause.cstr (.eqz (.add (.mul e1 e2) (.mul e1' e3))),
    Clause.or (.cstr (.eqz e1'')) (.cstr (.eqz (.add e2' e3'))) =>
    e1 = e1' ∧ e1 = e1'' ∧ e2 = e2' ∧ e3 = e3'
  | _, _ => false

def ruleEqZero {pc : pConfig} (g c : Clause pc) : Bool :=
  match g,c with
  | .cstr (.eqz (.mul e1 e2)), .or (.cstr (.eqz e1')) (.cstr (.eqz e2')) => e1 = e1' && e2 = e2'
  | _, _ => false

theorem ruleEqZeroSound {pc : pConfig} {Γ : Ctx pc} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
 ruleEqZero g c = true → c.holds ρ := by
  intro hr
  simp only [ruleEqZero] at hr
  split at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  rcases hr with ⟨hr1, hr2⟩
  rw[← hr1,← hr2]
  rw [Clause.holds]
  apply h at hg
  rw[Clause.holds, Cstr.holds, Expr.eval] at hg --Muchos rewrites, me suena a mucho envoltorio, quizá innecesario?
  rw[Clause.holds, Cstr.holds, Clause.holds, Cstr.holds]
  exact mul_eq_zero.mp hg -- Todo se reduce a que no hay divisores de cero en un dominio

  contradiction

theorem ruleDistribEqZeroSound {pc : pConfig} {Γ : Ctx pc} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
 ruleDistribEqZero g c = true → c.holds ρ := by
  intro hdist
  simp only [ruleDistribEqZero] at hdist
  split at hdist
  simp only [decide_eq_true_eq] at hdist
  rcases hdist with ⟨ hd1, hd2, hd3, hd4 ⟩
  rw [← hd2, ← hd3, ← hd4]
  rw [← hd1] at hg
  have hg' := h _ hg
  rename_i  e1 e2 e1' e3 e2' e3' e1''
  let ei := Clause.cstr (.eqz (.mul e1 (.add e2 e3)))
  have hi : ei.holds ρ := by
    apply ruleDistribSound h hg
    simp only [ruleDistrib]
    split
    rename_i heq heq1
    simp[ei] at heq heq1
    simp only [decide_eq_true_eq]
    rcases heq with ⟨⟨h1, h2⟩, h3, h4⟩
    rcases heq1 with ⟨h5, h6, h7⟩
    simp [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7]
    simp

  let Γ' : Ctx pc := [ei]
  have h' : Γ'.holds ρ := by
    intro c hc
    simp only [Γ', List.mem_singleton] at hc
    subst c
    exact hi
  apply ruleEqZeroSound h' (List.mem_singleton.mpr rfl)
  simp only [ruleEqZero]
  split
  rename_i e11 e12 e21 e22 he3 he4
  simp[ei] at he4 he3
  rcases he3 with ⟨ he31, he32 ⟩
  rcases he4 with ⟨ he41, he42 ⟩
  rw[← he41, ← he31, ← he32, ← he42]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  trivial
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  trivial
  contradiction

-- Ahora pruebo soundness sin recurrir a las otras rules, desenvolviendo + mathlib

theorem ruleDistribEqZeroSoundNaive {pc : pConfig} {Γ : Ctx pc} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
 ruleDistribEqZero g c = true → c.holds ρ := by
  intro hdist
  simp only [ruleDistribEqZero] at hdist
  split at hdist
  simp only [decide_eq_true_eq] at hdist
  rcases hdist with ⟨ hd1, hd2, hd3, hd4 ⟩
  rw [← hd2, ← hd3, ← hd4]
  rw [← hd1] at hg
  have hg' := h _ hg

  simp only [Clause.holds, Cstr.holds, Expr.eval] at ⊢ hg'
  rw[← mul_add] at hg'
  apply mul_eq_zero.mp
  assumption -- way easier

  contradiction


-- Muy sencillo para el certificado delegar sin usar rules
theorem ejercicio4 {pc : pConfig}
    (ρ : Nat → ZMod pc.p) (a b c d : Expr pc)
    (h : (Clause.cstr (.eqz (.add (.mul a b) (.add (.mul a c) (.mul a d))))).holds ρ) :
    (Clause.or (.cstr (.eqz a)) (.cstr (.eqz (.add b (.add c d))))).holds ρ := by

  simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, ← mul_add] using h
