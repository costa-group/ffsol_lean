import AlejandroPlayground.Printing
import AlejandroPlayground.Semantics
import Mathlib.Algebra.Field.ZMod

/-Bounds rules-/

def ruleBinary {pc : pConfig} (g c : Clause pc) : Bool :=
  match g,c with
  | .cstr (.eqz (.add (.mul (.var x) (.var y)) (.neg (.var z)))),
    .cstr (.range (.var t) l u) => x = y && y = z && z = t && l = 0 && u = 1
  | _,_ => false

theorem ruleBinarySound {pc : pConfig} (ρ : Nat → ZMod pc.p) (g c : Clause pc)
  (h : ruleBinary g c = true) : g.holds ρ → c.holds ρ := by
  intro h'
  simp only [ruleBinary] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ ⟨ ⟨ h1, h2 ⟩ , h3 ⟩ , h4 ⟩ , h5 ⟩
    simp only [Clause.holds, Cstr.holds, Expr.eval, Expr.evalInt] at h' ⊢
    rw [h1, h3, h2, h3] at h'
    rename_i t l u
    have hf : ρ t * (ρ t - 1) = 0 := by
      rw [mul_sub, mul_one, sub_eq_add_neg]
      exact h'
    rw[h4, h5]
    have hm0 : 0 < pc.midpoint := by
      rw [pc.midpoint_ok]
      omega
    have hp : 2 ≤ pc.p := pc.p_prime.two_le
    have hm1 : 1 < pc.midpoint := by
      rw [pc.midpoint_ok]
      omega
    rcases mul_eq_zero.mp hf with h0 | h1
    · simp [toSigned, h0, hm0]
    · have h : ρ t = 1 := sub_eq_zero.mp h1
      have hv : (1 : ZMod pc.p).val = 1 := ZMod.val_one'' (by omega)
      simp [toSigned, h, hv, hm1]
  · contradiction

def ruleConstant {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | .cstr (.eqz (.add (.var x) (.neg (.const v)))),
    .cstr (.range (.var t) l u) =>
      x = t && l = toSigned v && u = toSigned v
  | _, _ => false

theorem ruleConstantSound {pc : pConfig} (ρ : Nat → ZMod pc.p)
    (g c : Clause pc) (h : ruleConstant g c = true) :
    g.holds ρ → c.holds ρ := by
  intro h'
  simp only [ruleConstant] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ h1, h2 ⟩ , h3 ⟩
    simp only [Clause.holds, Cstr.holds, Expr.eval, Expr.evalInt] at h' ⊢
    rw [h1, add_neg_eq_zero] at h'
    rw [h2, h3, h']
    simp
  · contradiction

def ruleMergeRoots {pc : pConfig} (g1 g2 c : Clause pc) : Bool :=
  match g1, g2, c with
  | .cstr (.range (.var x) a1 a2),
    .cstr (.range (.var y) b1 b2),
    .cstr (.range (.var t) l u) =>
      x = y && y = t && l = max a1 b1 && u = min a2 b2
  | _, _, _ => false

theorem ruleMergeRootsSound {pc : pConfig} (ρ : Nat → ZMod pc.p)
  (g1 g2 c : Clause pc)
  (h1 : g1.holds ρ) (h2 : g2.holds ρ)
  (h : ruleMergeRoots g1 g2 c = true) : c.holds ρ := by
  simp only [ruleMergeRoots] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨ ⟨ ⟨ h3, h4 ⟩ , h5 ⟩ , h6 ⟩
    simp only [Clause.holds, Cstr.holds, Expr.evalInt] at h1 h2 ⊢
    rw[h3] at h1
    rw[h4] at h1 h2
    rw[h5, h6]
    rcases h1 with ⟨ h11, h12 ⟩
    rcases h2 with ⟨ h21, h22 ⟩
    constructor
    · exact max_le h11 h21
    · exact le_min h12 h22
  · contradiction

def sameVar {pc : pConfig} (e : Expr pc) : Option Nat :=
  match e with
  | .var x => some x
  | .const _ => none
  | .add e1 e2 =>
    match sameVar e1, sameVar e2 with
    | some x, some y => if x = y then some x else none
    | _, _ => none
  | .neg e' => sameVar e'
  | .mul e1 e2 =>
    match sameVar e1, sameVar e2 with
    | some x, some y => if x = y then some x else none
    | _, _ => none

def isExpRec {pc : pConfig} (x : Nat) : Expr pc → Option Nat
  | .var y => if decide (y = x) then some 1 else none
  | .const _ => none
  | .add _ _ => none
  | .neg _ => none --Es necesario
  | .mul e1 e2 => match isExpRec x e1, isExpRec x e2 with
    | some n1, some n2 => some (n1 + n2)
    | _ , _ => none

def ruleExp {pc : pConfig} (g c : Clause pc) : Bool :=
  match g, c with
  | .cstr (.range (.var x) l' u'), .cstr (.range e l u) =>
    if sameVar e = some x then
      match isExpRec x e with
      | some k =>
        if k = 0 then
          decide (l = 1 ∧ u = 1)
        else if k % 2 = 1 then
          decide (l = l'^k ∧ u = u'^k)
        else if u' < 0 then
          decide (l = u'^k ∧ u = l'^k)
        else if l' < 0 then
          decide (l = 0 ∧ u = max (l'^k) (u'^k))
        else
          decide (l = l'^k ∧ u = u'^k)
      | none => false
    else false
  | _, _ => false

theorem sameVarAndisExpRecSound {pc : pConfig} (ρ : Nat → ZMod pc.p) (e : Expr pc) (x : Nat)
  (k : Nat)
  (h : sameVar e = some x) (h' : isExpRec x e = some k) :
  e.eval ρ = (ρ x)^k := by
  induction e generalizing x k <;> simp only [sameVar] at h
  · injection h
    subst x
    simp only [Expr.eval]
    unfold isExpRec at h'
    simp only [decide_true, ↓reduceIte, Option.some.injEq] at h'
    rw[← h']
    symm
    exact pow_one (ρ _)
  · contradiction
  · simp only [isExpRec] at h'
    contradiction
  · contradiction
  · split at h
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      simp only [isExpRec] at h'
      split at h'
      · rcases h with ⟨ h1, h2 ⟩
        rename_i ih1 ih2 x5 x4 x3 y1 heq3 heq2 x2 x1 x' y heq1 heq
        injection h'
        rename_i h'
        rw [h2] at heq3
        have ih1' := ih1 _ _ heq3 heq1
        rw [← h1, h2] at heq2
        have ih2' := ih2 _ _ heq2 heq
        simp only [Expr.eval] at ih1' ih2' ⊢
        rw [ih1', ih2']
        rw [← pow_add, h']
      · contradiction
    · contradiction

theorem sameVarAndisExpRecSound' {pc : pConfig} (ρ : Nat → ZMod pc.p)
  (e : Expr pc) (x : Nat) (k : Nat)
  (h : sameVar e = some x) (h' : isExpRec x e = some k) :
  e.evalInt ρ = (toSigned (ρ x))^k := by
  induction e generalizing x k <;> simp only [sameVar] at h <;> unfold isExpRec at h'
  · injection h
    subst x
    simp only [decide_true, ↓reduceIte, Option.some.injEq] at h'
    rw[← h']
    rename_i n
    simp only [Expr.evalInt, pow_one (toSigned (ρ n))]
  · contradiction
  · contradiction
  · contradiction
  · split at h
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      split at h'
      · rcases h with ⟨ h1, h2 ⟩
        rename_i ih1 ih2 x5 x4 x3 y1 heq3 heq2 x2 x1 x' y heq1 heq
        injection h'
        rename_i h'
        rw [h2] at heq3
        have ih1' := ih1 _ _ heq3 heq1
        rw [← h1, h2] at heq2
        have ih2' := ih2 _ _ heq2 heq
        simp only[Expr.evalInt]
        rw [ih1', ih2']
        rw [← pow_add, h']
      · contradiction
    · contradiction


theorem ruleExpSound {pc : pConfig} (ρ : Nat → ZMod pc.p)
    (g c : Clause pc)
    (h1 : g.holds ρ) (h : ruleExp g c = true) : c.holds ρ := by
  unfold ruleExp at h
  split at h <;> try contradiction
  rename_i x u' l' e u l
  split at h <;> try contradiction
  rename_i hsame
  split at h <;> try contradiction
  rename_i k hpow
  have hEval := sameVarAndisExpRecSound' ρ e x k hsame hpow
  simp only [Clause.holds, Cstr.holds] at h1 ⊢
  simp only [Expr.evalInt] at h1
  rw [hEval]
  set z : ℤ := toSigned (ρ x)
  rcases h1 with ⟨hl, hu⟩
  split_ifs at h
  all_goals simp only [decide_eq_true_eq] at h
  · rcases h with ⟨rfl, rfl⟩
    simp_all
  · rcases h with ⟨rfl, rfl⟩
    have hkOdd : Odd k := Nat.odd_iff.mpr (by omega)
    constructor
    · exact (hkOdd.pow_le_pow).mpr hl
    · exact (hkOdd.pow_le_pow).mpr hu
  · rcases h with ⟨rfl, rfl⟩
    have hkEven : Even k := Nat.even_iff.mpr (by omega)
    constructor
    · rename_i h h1 h2 h3
      have h4 : z < 0 := by
        have hu' := le_iff_lt_or_eq.mp hu
        rcases hu' with hu1 | hu2
        · exact lt_trans hu1 h3
        · rwa [hu2]
      calc
        l' ^ k = (-l') ^ k := (hkEven.neg_pow l').symm
        _ ≤ (-z) ^ k := pow_le_pow_left₀ (by omega) (by omega) k
        _ = z ^ k := hkEven.neg_pow z
    · rename_i h h1 h2 h3
      have h4 : z < 0 := by
        have hu' := le_iff_lt_or_eq.mp hu
        rcases hu' with hu1 | hu2
        · exact lt_trans hu1 h3
        · rwa [hu2]
      calc
        z ^ k = (-z) ^ k := (hkEven.neg_pow _).symm
        _ ≤ (-u') ^ k := pow_le_pow_left₀ (by omega) (by omega) k
        _ = u' ^ k := hkEven.neg_pow _
  · rcases h with ⟨rfl, rfl⟩
    have hkEven : Even k := Nat.even_iff.mpr (by omega)
    constructor
    · rename_i h1 h2 h3 h4
      exact hkEven.pow_nonneg _
    · by_cases hz : z < 0
      · apply le_max_of_le_left
        calc
          z ^ k = (-z) ^ k := (hkEven.neg_pow z).symm
          _ ≤ (-u') ^ k := pow_le_pow_left₀ (by omega) (by omega) k
          _ = u' ^ k := hkEven.neg_pow u'
      · apply le_max_of_le_right
        exact pow_le_pow_left₀ (by omega) hu k
  · rcases h with ⟨rfl, rfl⟩
    constructor
    · rename_i h1
      exact pow_le_pow_left₀ (not_lt.mp h1) hl _
    · exact pow_le_pow_left₀ (by omega) hu k
