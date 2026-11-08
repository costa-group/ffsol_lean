import AlejandroPlayground.Printing
import AlejandroPlayground.Semantics
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.Induction

/-!
# Linear clause inference

This file checks deductions from §3.5 of the
[FFSOL paper](https://arxiv.org/abs/2604.26709v1).

-/

/--
Checks the first deduction of §3.5 on an explicit binary product. The conclusion must list the
two factors as zero equalities in the same order.
-/
def ruleEqZero {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | .cstr (.eqz (.mul e1 e2)), .or (.cstr (.eqz e1')) (.cstr (.eqz e2')) => e1 = e1' && e2 = e2'
  | _, _ => false

/--
If the accepted product premise is in a satisfied context, the corresponding disjunction holds
because a prime field has no zero divisors.
-/
theorem ruleEqZeroSound {pc : pConfig} {Γ : Ctx pc} {g c ρ}
    (h : Γ.holds ρ) (hg : g ∈ Γ) :
    ruleEqZero g c = true → c.holds ρ := by
  intro hr
  simp only [ruleEqZero] at hr
  split at hr
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with ⟨hr1, hr2⟩
    rw [← hr1, ← hr2]
    apply h at hg
    --Muchos rewrites, me suena a mucho envoltorio, quizá innecesario?
    simp only [Clause.holds, Cstr.holds, Expr.eval] at hg ⊢
    exact mul_eq_zero.mp hg -- Todo se reduce a que no hay divisores de cero en un dominio
  · contradiction

-- Intento de caso concreto de varias Expr, usando ruleEqZero.

-- Para no depender del ctx

/--
Applies binary product soundness directly to one satisfied premise, via a singleton context.
-/
theorem ruleEqZeroSound' {pc : pConfig} {ρ}
(g c : Clause pc) (hg : g.holds ρ) :
 ruleEqZero g c = true → c.holds ρ := by
  let Γ : Ctx pc := [g]
  have h : Γ.holds ρ := by
    intro c hc
    simp only [Γ, List.mem_singleton] at hc
    rw [hc]
    exact hg
  exact ruleEqZeroSound h (List.mem_singleton.mpr rfl)


/--
Proves the four-factor instance of the product rule directly using Mathlib's zero-product lemma.
-/
theorem ejercicillo {pc : pConfig}
    (ρ : Nat → ZMod pc.p) (a b c d : Expr pc)
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

/--
Derives the disjunction of two zero factors by applying the binary product checker to its
canonical conclusion.
-/
theorem reqToDisy {pc : pConfig}
    (ρ : Nat → ZMod pc.p) (e1 e2 : Expr pc)
    (h : (Clause.cstr (.eqz (.mul e1 e2))).holds ρ) :
    (Clause.or (.cstr (.eqz e1)) (.cstr (.eqz e2))).holds ρ := by
  apply (ruleEqZeroSound' (Clause.cstr (.eqz (.mul e1 e2)))
          (Clause.or (.cstr (.eqz e1)) (.cstr (.eqz e2))) h)
  simp[ruleEqZero]

/--
Proves the four-factor example by successively applying the binary product rule to the
right-associated product.
-/
theorem ejercicillo2 {pc : pConfig}
    (ρ : Nat → ZMod pc.p) (a b c d : Expr pc)
    (h : (Clause.cstr (.eqz (.mul a (.mul b (.mul c d))))).holds ρ) :
    (Clause.or (.cstr (.eqz a)) (.or (.cstr (.eqz b))
        (.or (.cstr (.eqz c)) (.cstr (.eqz d))))).holds ρ := by
  rcases reqToDisy ρ _ _ h with ha | hbcd
  · left; exact ha
  · rcases reqToDisy ρ _ _ hbcd with hb | hcd
    · right; left; exact hb
    · rcases reqToDisy ρ _ _ hcd with hc | hd
      · right; right; left; exact hc
      · right; right; right; exact hd --Not easy to generalize



/--
Builds the right-associated product of the given nonempty list, leaving a singleton factor
unchanged.
-/
def listToMul {pc : pConfig} : (l : List (Expr pc)) → l ≠ [] → Expr pc
  | [], h => False.elim (h rfl)
  | [x], _ => x
  | x :: y :: xs, _ => .mul x (listToMul (y :: xs) (by simp))

/--
Builds the right-associated disjunction of zero equalities for the given nonempty factor list.
-/
def listToOr {pc : pConfig} : (l : List (Expr pc)) → l ≠ [] → Clause pc
  | [], h => False.elim (h rfl)
  | [x], _ => (.cstr (.eqz x))
  | x :: y :: xs, _ => .or (.cstr (.eqz x)) (listToOr (y :: xs) (by simp))

/--
Renders the product premise, factor disjunction, and supplied proof body as a Lean theorem. For
an empty list it returns a comment.
-/
private def certificateWithProof {pc : pConfig} (l : List (Expr pc)) (proof : String) : String :=
  if h : l = [] then
    "-- Empty list, no certificate generated."
  else
    let mul := listToMul l h
    let or := listToOr l h
    s!"theorem certificate \{pc : pConfig}
      (ρ : Nat → ZMod pc.p)
      (h : (Clause.cstr (.eqz {mul.meta})).holds ρ) :
      {or.meta}.holds ρ := by
      {proof}"

/--
Generates a product certificate whose proof unfolds the expression semantics and simplifies with
Mathlib's zero-product lemma.
-/
def certificate1 {pc : pConfig} (l : List (Expr pc)) : String :=
  certificateWithProof l
    "simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, or_assoc] using h"

/--
The shared factor list used to exercise both product certificate generators.
-/
private def certificateExample (pc : pConfig) : List (Expr pc) := [
  .var 0,
  .var 1,
  .mul (.var 0) (.var 1),
  .add (.var 2) (.const 3),
  .neg (.var 0),
  .mul (.add (.var 0) (.var 1)) (.var 2)
]

#eval IO.println (certificate1 (certificateExample ⟨7, by decide⟩))

/--
A concrete product certificate proved by direct simplification, as in `certificate1`.
-/
theorem certificate {pc : pConfig}
      (ρ : Nat → ZMod pc.p)
      (h : (Clause.cstr (.eqz (.mul (.var 0)
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 1))
          (.mul (.add (.var 2) (.const 3))
            (.mul (.neg (.var 0)) (.mul (.add (.var 0) (.var 1)) (.var 2))))))))).holds ρ) :
      (Clause.or (.cstr (.eqz (.var 0)))
        (.or (.cstr (.eqz (.var 1)))
        (.or (.cstr (.eqz (.mul (.var 0) (.var 1))))
        (.or (.cstr (.eqz (.add (.var 2) (.const 3))))
        (.or (.cstr (.eqz (.neg (.var 0))))
          (.cstr (.eqz (.mul (.add (.var 0) (.var 1)) (.var 2))))))))).holds ρ := by
      simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, or_assoc] using h


/--
Proves the list version of the product rule for at least two factors by repeated applications of
`ruleEqZeroSound'` using induction on the length of the fact list.
-/
theorem ejercicio3 {pc : pConfig}
    (ρ : Nat → ZMod pc.p) :
    ∀ (l : List (Expr pc)) (hl : 2 ≤ l.length),
      (Clause.cstr (.eqz
        (listToMul l (List.ne_nil_iff_length_pos.mpr (lt_trans zero_lt_one hl))))).holds ρ →
      (listToOr l (List.ne_nil_iff_length_pos.mpr (lt_trans zero_lt_one hl))).holds ρ := by
  intro l lne h
  induction l using List.twoStepInduction with
  | nil => contradiction
  | singleton a => contradiction
  | cons_cons a b xs _ ih1 =>
      cases xs with
      | nil =>
          simp only [listToOr]
          simp only [listToMul] at h
          apply ruleEqZeroSound' _ _ h
          simp only[ruleEqZero]
          decide
      | cons c cs =>
          simp only [listToOr]
          simp only [listToMul] at h
          have g : Clause.holds ρ
              ((Clause.cstr (.eqz a)).or
                (.cstr (.eqz (b.mul (listToMul (c :: cs) (by simp)))))) := by
            apply ruleEqZeroSound' _ _ h
            simp only [ruleEqZero]
            decide
          rcases g with g1 | g2
          · exact Or.inl g1
          · exact Or.inr (ih1 b (by simp) g2)

/--
Renders a list of expressions as a Lean list literal for the generated call to `ejercicio3`.
-/
def ListExpr.meta {pc : pConfig} (l : List (Expr pc)) : String :=
  "[" ++ String.intercalate ", " (l.map Expr.meta) ++ "]"

/--
Generates a product certificate that invokes `ejercicio3` for two or more factors. For a
singleton, the premise already has the form of the conclusion.
-/
def certificate2 {pc : pConfig} (l : List (Expr pc)) : String :=
  let proof :=
    if 2 ≤ l.length then
      s!"exact ejercicio3 ρ
          ({ListExpr.meta l} : List (Expr pc))
          (by simp) h"
    else
      "exact h"
  certificateWithProof l proof

#eval IO.println (certificate2 (certificateExample ⟨7, by decide⟩))


/--
A concrete product certificate proved through the list theorem, as in `certificate2`.
-/
theorem certificate' {pc : pConfig}
      (ρ : Nat → ZMod pc.p)
      (h : (Clause.cstr (.eqz (.mul (.var 0)
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 1))
          (.mul (.add (.var 2) (.const 3))
            (.mul (.neg (.var 0)) (.mul (.add (.var 0) (.var 1)) (.var 2))))))))).holds ρ) :
      (Clause.or (.cstr (.eqz (.var 0)))
        (.or (.cstr (.eqz (.var 1)))
        (.or (.cstr (.eqz (.mul (.var 0) (.var 1))))
        (.or (.cstr (.eqz (.add (.var 2) (.const 3))))
        (.or (.cstr (.eqz (.neg (.var 0))))
          (.cstr (.eqz (.mul (.add (.var 0) (.var 1)) (.var 2))))))))).holds ρ := by
      exact ejercicio3 ρ (certificateExample pc) (by simp [certificateExample]) h

-- Rule e1 * e2 + e1 * e3 = 0 ↔ e1 * (e2 + e3) = 0
/--
Checks the factoring step from `a * b + a * c = 0` to `a * (b + c) = 0` by comparing the common
factor and both summands syntactically.
-/
def ruleDistrib {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | Clause.cstr (.eqz (.add (.mul e1 e2) (.mul e1' e3))),
    Clause.cstr (.eqz (.mul e1'' (.add e2' e3'))) =>
    e1 = e1' ∧ e1 = e1'' ∧ e2 = e2' ∧ e3 = e3'
  | _, _ => false

/--
The accepted factored equation follows from its premise by distributivity.
-/
theorem ruleDistribSound {pc : pConfig} {Γ : Ctx pc} {g c ρ} (h : Γ.holds ρ) (hg : g ∈ Γ) :
 ruleDistrib g c = true → c.holds ρ := by
  -- Otra vez, desenvolvemos y le pasamos la pelota a simpa con mul_add
  intro hdist
  simp only [ruleDistrib] at hdist
  split at hdist
  · apply h at hg
    simp only [Clause.holds, Cstr.holds, Expr.eval] at hg ⊢
    simp only [decide_eq_true_eq] at hdist
    rcases hdist with ⟨he1, he2, he3, he4⟩
    rw [← he2, ← he3, ← he4]
    rw [← he1] at hg
    simpa only [mul_add] using hg
  · contradiction

/--
Checks the two-summand instance of the common-factor deduction in §3.5, with conclusion `a = 0 ∨
b + c = 0`.
-/
def ruleDistribEqZero {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | Clause.cstr (.eqz (.add (.mul e1 e2) (.mul e1' e3))),
    Clause.or (.cstr (.eqz e1'')) (.cstr (.eqz (.add e2' e3'))) =>
    e1 = e1' ∧ e1 = e1'' ∧ e2 = e2' ∧ e3 = e3'
  | _, _ => false

/--
Proves the common-factor deduction by composing the factoring check with the binary product
check.
-/
theorem ruleDistribEqZeroSound {pc : pConfig} {Γ : Ctx pc} {g c ρ}
    (h : Γ.holds ρ) (hg : g ∈ Γ) :
    ruleDistribEqZero g c = true → c.holds ρ := by
  intro hdist
  simp only [ruleDistribEqZero] at hdist
  split at hdist
  · simp only [decide_eq_true_eq] at hdist
    rcases hdist with ⟨hd1, hd2, hd3, hd4⟩
    rw [← hd2, ← hd3, ← hd4]
    rw [← hd1] at hg
    rename_i e1 e2 e1' e3 e2' e3' e1''
    let ei : Clause pc := .cstr (.eqz (.mul e1 (.add e2 e3)))
    have hi : ei.holds ρ := ruleDistribSound h hg (by
      simp only [ei, ruleDistrib, decide_eq_true_eq, eq_self, and_self])
    exact ruleEqZeroSound' ei _ hi (by
      simp only [ei, ruleEqZero, Bool.and_eq_true, decide_eq_true_eq, eq_self, and_self])
  · contradiction

-- Ahora pruebo soundness sin recurrir a las otras rules, desenvolviendo + mathlib

/--
Proves the same two-summand deduction directly from distributivity and the zero-product
property.
-/
theorem ruleDistribEqZeroSoundNaive {pc : pConfig} {Γ : Ctx pc} {g c ρ}
    (h : Γ.holds ρ) (hg : g ∈ Γ) :
    ruleDistribEqZero g c = true → c.holds ρ := by
  intro hdist
  simp only [ruleDistribEqZero] at hdist
  split at hdist
  · simp only [decide_eq_true_eq] at hdist
    rcases hdist with ⟨hd1, hd2, hd3, hd4⟩
    rw [← hd2, ← hd3, ← hd4]
    rw [← hd1] at hg
    have hg' := h _ hg
    simp only [Clause.holds, Cstr.holds, Expr.eval] at hg' ⊢
    rw [← mul_add] at hg'
    apply mul_eq_zero.mp
    assumption -- way easier
  · contradiction


-- Muy sencillo para el certificado delegar sin usar rules
/--
Proves the three-summand common-factor deduction for the displayed right-associated sum, using
field identities directly.
-/
theorem ejercicio4 {pc : pConfig}
    (ρ : Nat → ZMod pc.p) (a b c d : Expr pc)
    (h : (Clause.cstr (.eqz (.add (.mul a b) (.add (.mul a c) (.mul a d))))).holds ρ) :
    (Clause.or (.cstr (.eqz a)) (.cstr (.eqz (.add b (.add c d))))).holds ρ := by
  simpa only [Clause.holds, Cstr.holds, Expr.eval, mul_eq_zero, ← mul_add] using h
