import mathlib

inductive Expr (p : Nat) where
  | var (n : Nat)
  | const (c : ZMod p)
  | add (e1 : Expr p) (e2 : Expr p)
  | neg (e : Expr p)
  | mul (e1 : Expr p) (e2 : Expr p)
  deriving DecidableEq

inductive Cstr (p : Nat) where
  | eqz : Expr p → Cstr p
  | nez : Expr p → Cstr p
  deriving DecidableEq

inductive Clause (p : Nat) where
  | cstr : Cstr p → Clause p
  | or : Clause p → Clause p → Clause p
  deriving DecidableEq

def Expr.eval {p} (ρ : Nat → ZMod p) : Expr p → ZMod p
  | .var n => ρ n
  | .const c => c
  | .add e1 e2 => e1.eval ρ + e2.eval ρ
  | .mul e1 e2 => e1.eval ρ * e2.eval ρ
  | .neg e => - e.eval ρ

def Cstr.holds {p} (ρ : Nat → ZMod p) : Cstr p → Prop
  | .eqz e => e.eval ρ = 0
  | .nez e => e.eval ρ ≠ 0

def Clause.holds {p} (ρ : Nat → ZMod p) : Clause p  → Prop
  | .cstr c => c.holds ρ
  | .or c1 c2 => c1.holds ρ ∨ c2.holds ρ

abbrev Ctx (p : Nat) := List (Clause p)

def Ctx.holds {p} (ρ : Nat → ZMod p) (Γ : Ctx p) : Prop := ∀ c ∈ Γ, c.holds ρ

def ruleEqZero {p} (g c : Clause p) : Bool :=
  match g,c with
  | .cstr (.eqz (.mul e1 e2)), .or (.cstr (.eqz e1')) (.cstr (.eqz e2')) => e1 = e1' && e2 = e2'
  | _, _ => false

theorem ruleEqZeroSound {p} [Fact (Nat.Prime p)] {Γ : Ctx p} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
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
  rw[Clause.holds, Cstr.holds]
  exact mul_eq_zero.mp hg -- Todo se reduce a que no hay divisores de cero en un dominio

  contradiction

-- Intento de caso concreto de varias Expr, usando ruleEqZero.

-- Para no depender del ctx

theorem ruleEqZeroSound' {p} [Fact (Nat.Prime p)] {ρ} (g c : Clause p) (hg : g.holds ρ) :
 ruleEqZero g c = true → c.holds ρ := by
  let Γ : Ctx p := [g]
  have h : Γ.holds ρ := by
    intro c hc
    simp[Γ] at hc
    rw[hc]
    exact hg
  exact ruleEqZeroSound h (List.mem_singleton.mpr rfl)


theorem ejercicillo {p : Nat} [Fact (Nat.Prime p)]
    (ρ : Nat → ZMod p) (a b c d : Expr p)
    (h : (Clause.cstr (.eqz (.mul a (.mul b (.mul c d))))).holds ρ) :
    (Clause.or (.cstr (.eqz a)) (.or (.cstr (.eqz b))
        (.or (.cstr (.eqz c)) (.cstr (.eqz d))))).holds ρ := by

  --repeat rw[Clause.holds]
  --repeat rw[Cstr.holds]

  --let c₁ := (Clause.or (.cstr (.eqz a)) (.cstr (.eqz (.mul b (.mul c d)))))
  --have h₁ := ruleEqZeroSound' (Clause.cstr (.eqz (.mul a (.mul b (.mul c d))))) c₁ h

  --rw[Clause.holds, Cstr.holds] at h
  --repeat rw[Expr.eval] at h
  --simpa only [mul_eq_zero, or_assoc] using h
  simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, or_assoc] using h

theorem reqToDisy {p : Nat} [Fact (Nat.Prime p)]
    (ρ : Nat → ZMod p) (e1 e2 : Expr p)
    (h : (Clause.cstr (.eqz (.mul e1 e2))).holds ρ) :
    (Clause.or (.cstr (.eqz e1)) (.cstr (.eqz e2))).holds ρ := by

  apply (ruleEqZeroSound' (Clause.cstr (.eqz (.mul e1 e2)))
          (Clause.or (.cstr (.eqz e1)) (.cstr (.eqz e2))) h)
  simp[ruleEqZero]

theorem ejercicillo2 {p : Nat} [Fact (Nat.Prime p)]
    (ρ : Nat → ZMod p) (a b c d : Expr p)
    (h : (Clause.cstr (.eqz (.mul a (.mul b (.mul c d))))).holds ρ) :
    (Clause.or (.cstr (.eqz a)) (.or (.cstr (.eqz b))
        (.or (.cstr (.eqz c)) (.cstr (.eqz d))))).holds ρ := by

  rcases reqToDisy ρ _ _ h with ha | hbcd
  · left; exact ha
  · rcases reqToDisy ρ _ _ hbcd with hb | hcd
    · right; left; exact hb
    · rcases reqToDisy ρ _ _ hcd with hc | hd
      · right; right; left; exact hc
      · right; right; right; exact hd

-- Voy a hacer un pretty printer para probar

def Expr.print {p} : Expr p → String
  | .var n => "x" ++ n.toSubscriptString -- Asumo var n como xₙ
  | .const c => toString c.val
  | .add e1 e2 => s!"({e1.print} + {e2.print})"
  | .mul e1 e2 => s!"({e1.print} * {e2.print})"
  | .neg e => s!"(-{e.print})"

def Cstr.print {p} : Cstr p → String
  | .eqz e => s!"{e.print} = 0"
  | .nez e => s!"{e.print} ≠ 0"

def Clause.print {p} : Clause p → String
  | .cstr c => c.print
  | .or c1 c2 => s!"{c1.print} ∨ {c2.print}"

def Expr.meta {p : Nat} : Expr p → String
  | .var n => s!"(Expr.var {n})"
  | .const c => s!"(Expr.const {c.val})"
  | .add e₁ e₂ => s!"(Expr.add {e₁.meta} {e₂.meta})"
  | .mul e₁ e₂ => s!"(Expr.mul {e₁.meta} {e₂.meta})"
  | .neg e => s!"(Expr.neg {e.meta})"

def Cstr.meta {p : Nat} : Cstr p → String
  | .eqz e => s!"(Cstr.eqz {e.meta})"
  | .nez e => s!"(Cstr.nez {e.meta})"

def Clause.meta {p : Nat} : Clause p → String
  | .cstr c => s!"(Clause.cstr {c.meta})"
  | .or c₁ c₂ => s!"(Clause.or {c₁.meta} {c₂.meta})"

def listToMul {p} : (l : List (Expr p)) → l ≠ [] → Expr p
  | [], h => False.elim (h rfl)
  | [x], _ => x
  | x :: y :: xs, _ => .mul x (listToMul (y :: xs) (by simp))

def listToOr {p} : (l : List (Expr p)) → l ≠ [] → Clause p
  | [], h => False.elim (h rfl)
  | [x], _ => (.cstr (.eqz x))
  | x :: y :: xs, _ => .or (.cstr (.eqz x)) (listToOr (y :: xs) (by simp))

def certificate1 {p} (l : List (Expr p)) : String :=
  if h : l = [] then
    "-- Empty list, no certificate generated."
  else
    let mul := listToMul l h
    let or := listToOr l h
    s!"theorem certificate \{p : Nat} [Fact (Nat.Prime p)]
      (ρ : Nat → ZMod p)
      (h : (Clause.cstr (.eqz {mul.meta})).holds ρ) :
      {or.meta}.holds ρ := by
      simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, or_assoc] using h"

#eval IO.println (certificate1 ([
  .var 0,
  .var 1,
  .mul (.var 0) (.var 1),
  .add (.var 2) (.const 3),
  .neg (.var 0),
  .mul (.add (.var 0) (.var 1)) (.var 2)
] : List (Expr 7)))

theorem certificate {p : Nat} [Fact (Nat.Prime p)]
      (ρ : Nat → ZMod p)
      (h : (Clause.cstr (.eqz (Expr.mul (Expr.var 0) (Expr.mul (Expr.var 1) (Expr.mul (Expr.mul (Expr.var 0) (Expr.var 1)) (Expr.mul (Expr.add (Expr.var 2) (Expr.const 3)) (Expr.mul (Expr.neg (Expr.var 0)) (Expr.mul (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.var 2))))))))).holds ρ) :
      (Clause.or (Clause.cstr (Cstr.eqz (Expr.var 0))) (Clause.or (Clause.cstr (Cstr.eqz (Expr.var 1))) (Clause.or (Clause.cstr (Cstr.eqz (Expr.mul (Expr.var 0) (Expr.var 1)))) (Clause.or (Clause.cstr (Cstr.eqz (Expr.add (Expr.var 2) (Expr.const 3)))) (Clause.or (Clause.cstr (Cstr.eqz (Expr.neg (Expr.var 0)))) (Clause.cstr (Cstr.eqz (Expr.mul (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.var 2))))))))).holds ρ := by
      simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, or_assoc] using h

/- De momento aparcado.

def getFactors {p} : Expr p → List (Expr p)
  | .mul e1 e2 => getFactors e1 ++ getFactors e2
  | e => [e]

def getLiterals {p} : Clause p → List (Expr p)
  | .cstr (.eqz e) => [e]
  | .cstr (.nez e) => [e]
  | .or c1 c2 => getLiterals c1 ++ getLiterals c2

def allEqz {p} : Clause p → Bool
  | .or c1 c2 => allEqz c1 && allEqz c2
  | .cstr (.eqz _) => true
  | _ => false

def ruleProductZero {p} (g c : Clause p) : Bool :=
  match g, getLiterals c with
  | .cstr (.eqz e), literals => decide ((getFactors e).Perm literals) && allEqz c
  | _, _ => false

private theorem getFactors_length_pos {p} (e : Expr p) :
    0 < (getFactors e).length := by
    induction e <;> simp_all [getFactors, List.length_append]

private theorem holds_of_mem_literal {p}
    (ρ : ℕ → ZMod p) :
    ∀ (c : Clause p) (f : Expr p),
      allEqz c = true →
      f ∈ getLiterals c →
      (Clause.cstr (.eqz f)).holds ρ →
      c.holds ρ := by
  intro c
  induction c with
  | cstr k =>
      intro f hall hmem hf
      cases k with
      | eqz e =>
          simp [getLiterals] at hmem
          subst f
          exact hf
      | nez e =>
          simp [allEqz] at hall
  | or c1 c2 ih1 ih2 =>
      intro f hall hmem hf
      simp [allEqz] at hall
      obtain ⟨hall1, hall2⟩ := hall
      simp [getLiterals] at hmem
      change c1.holds ρ ∨ c2.holds ρ
      rcases hmem with hmem | hmem
      · exact Or.inl (ih1 f hall1 hmem hf)
      · exact Or.inr (ih2 f hall2 hmem hf)

private theorem zero_factor {p} [Fact (Nat.Prime p)]
    (ρ : ℕ → ZMod p) (e : Expr p) :
    (Clause.cstr (.eqz e)).holds ρ →
    ∃ f ∈ getFactors e,
      (Clause.cstr (.eqz f)).holds ρ := by
  sorry

def ruleProductZeroSound {p} [Fact (Nat.Prime p)] {Γ : Ctx p} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
  ruleProductZero g c = true → c.holds ρ := by
  unfold ruleProductZero
  split
  · intro hr
    simp at hr
    rcases hr with ⟨hr1, hr2⟩
    have hge := h hg
    obtain ⟨f, hfmem, hfzero⟩ := zero_factor ρ e hge
    have hlit : f ∈ getLiterals c :=
      hr1.mem_iff.mp hfmem
    exact holds_of_mem_literal ρ c f hr2 hlit hfzero

  · intro hr
    simp at hr

-/
