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

-- Useful defitions for this module
@[match_pattern]
def Expr.sub {pc : pConfig} (a b : Expr pc) : Expr pc := .add a (.neg b)

@[match_pattern] --Para que me funcionen los matchs
def Cstr.eq {pc : pConfig} (a b : Expr pc) : Cstr pc := .eqz (Expr.sub a b)

@[match_pattern]
def Cstr.ne {pc : pConfig} (a b : Expr pc) : Cstr pc := .nez (Expr.sub a b)

private def checkLightweightConflict {pc : pConfig}
    (c1 c2 : Cstr pc) : Bool :=
  match c1, c2 with
  | .eq (.var x) (.const a), .eq (.var y) (.const b) =>
      decide (x = y ∧ a ≠ b)
  | .eq (.var x) (.const a), .ne (.var y) (.const b) =>
      decide (x = y ∧ a = b)
  | _, _ => false

def ruleLightweightConflict {pc : pConfig}
    (c1 c2 : Cstr pc) : Bool :=
  checkLightweightConflict c1 c2 ||
  checkLightweightConflict c2 c1

theorem checkLightweightConflictSound {pc : pConfig}
    (c1 c2 : Cstr pc)
    (ρ : Nat → ZMod pc.p)
    (h : checkLightweightConflict c1 c2 = true)
    (h1 : c1.holds ρ)
    (h2 : c2.holds ρ) : False := by
  simp only [checkLightweightConflict] at h
  split at h <;> simp only [Cstr.holds, Expr.eval] at h1 h2
  · simp only [decide_eq_true_eq] at h
    rename_i x a y b
    rcases h with ⟨ h', h'' ⟩
    rw[h'] at h1
    have contra : a = b := by
      apply add_neg_eq_zero.mp at h1
      apply add_neg_eq_zero.mp at h2
      rwa[h1] at h2
    contradiction
  · simp only [decide_eq_true_eq] at h
    rename_i x a y b
    rcases h with ⟨ h', h'' ⟩
    rw[h', h''] at h1
    apply h2
    assumption
  · contradiction

theorem ruleLightweightConflictSound {pc : pConfig}
    (c1 c2 : Cstr pc)
    (ρ : Nat → ZMod pc.p)
    (h : ruleLightweightConflict c1 c2 = true)
    (h1 : c1.holds ρ)
    (h2 : c2.holds ρ) : False := by
  simp only [ruleLightweightConflict,Bool.or_eq_true] at h
  rcases h with h' | h''
  · exact checkLightweightConflictSound _ _ _ h' h1 h2
  · exact checkLightweightConflictSound _ _ _ h'' h2 h1

def ruleDomainPropagation {pc : pConfig}
    (c1 c2 : Cstr pc) : Bool :=
  match c1, c2 with
  | .eq (.var x) (.const a),
    .ne (.var y) (.const b) =>
      decide (x = y ∧ a ≠ b)
  | _, _ => false

theorem ruleDomainPropagationSound {pc : pConfig}
    (c1 c2 : Cstr pc)
    (ρ : Nat → ZMod pc.p)
    (h : ruleDomainPropagation c1 c2 = true)
    (h1 : c1.holds ρ) :
    c2.holds ρ := by
  simp only [ruleDomainPropagation] at h
  split at h
  · simp only [Cstr.holds, Expr.eval] at ⊢ h1
    simp only [decide_eq_true_eq] at h
    rcases h with ⟨ h', h'' ⟩
    intro c
    apply h''
    rw[h'] at h1
    apply add_neg_eq_zero.mp at h1
    apply add_neg_eq_zero.mp at c
    rwa[h1] at c
  · contradiction

def isMonomial {pc : pConfig} : (Expr pc) → Bool
  | .var _ => true
  | .const c => decide (c ≠ 0) -- me quito el 0
  | .mul e1 e2 => isMonomial e1 && isMonomial e2
  | .add _ _ => false
  | .neg e => isMonomial e

def varAppears {pc : pConfig} (n : Nat) :  (Expr pc) → Bool
  | .var x => decide (x = n)
  | .const _ => false
  | .mul e1 e2 => varAppears n e1 || varAppears n e2
  | .add e1 e2 => varAppears n e1 || varAppears n e2
  | .neg e => varAppears n e

def ruleMonomialZero {pc : pConfig}
    (g1 g2 c : Cstr pc) : Bool :=
  match g1, g2, c with
  | .eq (.var v) m,
    .eq (.var x) (.const a),
    .eq (.var w) (.const b) =>
      decide (v = w ∧ a = 0 ∧ b = 0) &&
      isMonomial m &&
      varAppears x m
  | _, _, _ => false

theorem zeroMonomial {pc : pConfig}
    (m : Expr pc)
    (x : Nat)
    (hm1 : isMonomial m = true)
    (hm2 : varAppears x m = true)
    (ρ : Nat → ZMod pc.p)
    (h : (Cstr.eqz (.var x)).holds ρ) :
    (Cstr.eqz m).holds ρ := by
  induction m with
  | var n =>
    unfold varAppears at hm2
    simp only [decide_eq_true_eq] at hm2
    rwa[hm2]
  | const c =>
    unfold varAppears at hm2
    contradiction
  | add e1 e2 ih1 ih2 =>
    unfold isMonomial at hm1
    contradiction
  | mul e1 e2 ih1 ih2 =>
    unfold isMonomial at hm1
    simp only [Bool.and_eq_true] at hm1
    rcases hm1 with ⟨ hm1', hm2' ⟩
    unfold varAppears at hm2
    simp only [Bool.or_eq_true] at hm2
    rcases hm2 with hm2' | hm3'
    · have g := ih1 hm1' hm2'
      simp only [Cstr.holds, Expr.eval] at ⊢ g
      rw[g]
      exact zero_mul _
    · have g := ih2 hm2' hm3'
      simp only [Cstr.holds, Expr.eval] at ⊢ g
      rw[g]
      exact mul_zero _
    | neg e ih =>
      unfold isMonomial at hm1
      unfold varAppears at hm2
      have g := ih hm1 hm2
      simp only [Cstr.holds, Expr.eval] at ⊢ g
      rw[g]
      exact neg_zero


theorem ruleMonomialZeroSound {pc : pConfig}
    (g1 g2 c : Cstr pc)
    (ρ : Nat → ZMod pc.p)
    (h : ruleMonomialZero g1 g2 c = true)
    (h1 : g1.holds ρ)
    (h2 : g2.holds ρ) :
    c.holds ρ := by
  simp only [ruleMonomialZero] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ ⟨ h', ⟨ ha, hb ⟩⟩ , h'' ⟩ , h''' ⟩
    rename_i v m x a w b
    simp only [Cstr.holds, Expr.eval] at h1 h2 ⊢
    have g' : (Cstr.eqz (.var x)).holds ρ := by
      simp only [Cstr.holds, Expr.eval]
      symm
      rw[← h2, ha]
      simp
      exact neg_zero
    have g := zeroMonomial _ _ h'' h''' _ g'
    simp only [Cstr.holds] at g
    rw[g, h'] at h1
    rw [hb]
    exact h1
  · contradiction

private def lookupValue {pc : pConfig}
    (x : Nat) : List (Cstr pc) → Option (ZMod pc.p)
  | [] => none
  | .eq (.var y) (.const a) :: eqs =>
      if x = y then some a else lookupValue x eqs
  | _ :: eqs => lookupValue x eqs

private def evalMonomial {pc : pConfig}
    (eqs : List (Cstr pc)) : Expr pc → Option (ZMod pc.p)
  | .var x => lookupValue x eqs
  | .const a => some a
  | .mul e1 e2 => do
      let a ← evalMonomial eqs e1
      let b ← evalMonomial eqs e2
      return a * b
  | .neg e => do
      let a ← evalMonomial eqs e
      return -a
  | .add _ _ => none

def ruleMonomialValue {pc : pConfig}
    (d : Cstr pc)
    (eqs : List (Cstr pc))
    (c : Cstr pc) : Bool :=
  match d, c with
  | .eq (.var v) m, .eq (.var w) (.const b) =>
      decide (v = w) &&
      isMonomial m &&
      match evalMonomial eqs m with
      | some a => decide (a = b)
      | none => false
  | _, _ => false

theorem lookupValueSound {pc : pConfig}
    (x : Nat) (eqs : List (Cstr pc))
    (a : ZMod pc.p)
    (h : lookupValue x eqs = some a) :
    Cstr.eq (.var x) (.const a) ∈ eqs := by
  induction eqs with
  | nil => simp only [lookupValue] at h; contradiction
  | cons y ys ih =>
    unfold lookupValue at h
    split at h
    · contradiction
    · split at h
      · simp at h --look for explicit thm
        rename_i heq h'
        rw[heq, h', h]
        exact List.mem_cons_self
      · apply List.mem_cons.mpr
        right
        apply ih
        rename_i eqs' h' heq
        rw [← h]
        have h'' : ys = eqs' := congrArg List.tail h'
        rw[h'']
    · rename_i x'' head eqs x' heq
      apply List.mem_cons.mpr
      right
      apply ih
      have h'' : ys = eqs := congrArg List.tail heq
      rwa[h'']

theorem evalMonomialSound {pc : pConfig}
  (eqs : List (Cstr pc))
  (m : Expr pc)
  (mv : ZMod pc.p)
  (h : evalMonomial eqs m = some mv)
  (ρ : Nat → ZMod pc.p)
  (heqs : ∀ e ∈ eqs, e.holds ρ) :
  (Cstr.eq m (.const mv)).holds ρ := by
  induction m generalizing mv with
  | var n =>
    simp only [evalMonomial] at h
    have g := lookupValueSound n eqs mv h
    apply heqs at g
    assumption
  | const c =>
    simp only [evalMonomial] at h
    injection h with h'
    rw[h']
    simp only [Cstr.holds, Expr.eval]
    apply add_neg_eq_zero.mpr
    rfl
  | add e1 e2 ih1 ih2 =>
    simp only [evalMonomial] at h
    contradiction
  | neg e ih =>
    simp only[Cstr.holds, Expr.eval] at ⊢ ih
    cases hv : evalMonomial eqs e with
    | none =>
      simp [evalMonomial, hv] at h
    | some mv' =>
      simp [evalMonomial, hv] at h
      subst mv
      have g := ih mv' hv
      apply add_neg_eq_zero.mpr
      apply add_neg_eq_zero.mp at g
      subst mv'
      rfl
  | mul e1 e2 ih1 ih2 =>
    simp only [Cstr.holds, Expr.eval] at ⊢ ih1 ih2
    cases hv1 : evalMonomial eqs e1 with
    | none =>
        simp [evalMonomial, hv1] at h
    | some mv1 =>
        cases hv2 : evalMonomial eqs e2 with
        | none =>
            simp [evalMonomial, hv1, hv2] at h
        | some mv2 =>
            simp [evalMonomial, hv1, hv2] at h
            subst mv
            have g1 := ih1 mv1 hv1
            have g2 := ih2 mv2 hv2
            apply add_neg_eq_zero.mp at g1
            apply add_neg_eq_zero.mp at g2
            apply add_neg_eq_zero.mpr
            rw [g1, g2]


theorem ruleMonomialValueSound {pc : pConfig}
    (d : Cstr pc)
    (eqs : List (Cstr pc))
    (c : Cstr pc)
    (ρ : Nat → ZMod pc.p)
    (h : ruleMonomialValue d eqs c = true)
    (hd : d.holds ρ)
    (heqs : ∀ e ∈ eqs, e.holds ρ) :
    c.holds ρ := by
  simp only [ruleMonomialValue] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ h', h''⟩ , h'''⟩
    rename_i d c v m w b
    split at h'''
    · rename_i x a heq
      simp only[decide_eq_true_eq] at h'''
      subst b w
      have g := evalMonomialSound _ _ _ heq
      simp only [Cstr.holds, Expr.eval] at ⊢ hd
      apply add_neg_eq_zero.mp at hd
      have g' := g ρ heqs
      simp only [Cstr.holds, Expr.eval] at g'
      rwa [← hd] at g'
    · contradiction
  · contradiction


  /-
  unfold ruleMonomialValue at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ h', h''⟩ , h'''⟩
    rename_i d c v m w b
    split at h'''
    · rename_i a heq
      simp only [decide_eq_true_eq] at h'''
      induction m generalizing a b w v with
      | var n =>
        unfold evalMonomial at heq
        have g := lookupValueSound _ _ _ heq
        apply heqs at g
        simp_all only [Cstr.holds, Expr.eval]
        apply add_neg_eq_zero.mp at hd
        rwa[hd]
      | const c =>
        unfold evalMonomial at heq
        injection heq with heq'
        rwa[← h', ← h''', ← heq']
      | add e1 e2 ih1 ih2 =>
        unfold isMonomial at h''
        contradiction
      | neg e ih =>
        unfold isMonomial at h''
        unfold evalMonomial at heq
        cases hv : evalMonomial eqs e with
        | none =>
            simp only [hv] at heq
            contradiction
        | some v' =>
            simp[hv] at heq
            simp_all only [Cstr.holds, Expr.eval]

  -/

  /-
  unfold ruleMonomialValue at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ h', h''⟩ , h'''⟩
    rename_i d c v m w b
    split at h'''
    · rename_i heq
      unfold evalMonomial at heq
      split at heq
      · have g := lookupValueSound _ eqs _ heq
        apply heqs at g
        simp_all only [Cstr.holds, Expr.eval]
        apply add_neg_eq_zero.mp at hd
        simp only [decide_eq_true_eq] at h'''
        rwa[← h''', hd]
      · simp only [decide_eq_true_eq] at h'''
        injection heq with heq'
        rwa[← h', ← h''', ← heq']
      · simp only [decide_eq_true_eq] at h'''

      ·
      · contradiction
  · contradiction
  -/
