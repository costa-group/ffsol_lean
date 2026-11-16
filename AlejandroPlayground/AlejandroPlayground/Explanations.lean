import AlejandroPlayground.Bounds
import AlejandroPlayground.LinearClause
import AlejandroPlayground.PrimeFieldLinear
import AlejandroPlayground.EquivalenceInference

namespace Explanations

/-! ## Certificates -/

/-- The constructors encode rule names and the identifiers of their premises. -/
inductive Cert where
  | eqZero (i : Nat)
  | distrib (i : Nat)
  | distribEqZero (i : Nat)
  | lightweightConflict (i j : Nat)
  | domainPropagation (i : Nat)
  | monomialZero (i j : Nat)
  | monomialValue (definition : Nat) (values : List Nat)
  | equivalence (equalities : List Nat) (definition1 definition2 : Nat)
  | binary (i : Nat)
  | constant (i : Nat)
  | mergeRoots (i j : Nat)
  | exp (i : Nat)
  deriving Repr, DecidableEq

/-- Every explanation includes the candidate conclusion to check. -/
abbrev Step (pc : pConfig) := Clause pc × Cert

/-! ## Safe lookup of atomic premises -/

/-- Reject missing indices and disjunctive facts when an atomic premise is needed. -/
def getAtom {pc : pConfig} (Γ : Ctx pc) (i : Nat) : Option (Cstr pc) :=
  match Γ[i]? with
  | some (.cstr g) => some g
  | _ => none

private theorem getAtom_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) {i : Nat} {g : Cstr pc}
    (hg : getAtom Γ i = some g) : g.holds ρ := by
  unfold getAtom at hg
  cases hi : Γ[i]? with
  | none => simp [hi] at hg
  | some f =>
    cases f with
    | or _ _ => simp [hi] at hg
    | cstr d =>
      have hd : d = g := by simpa [hi] using hg
      subst g
      exact hΓ (.cstr d) (List.mem_of_getElem? hi)

/-- Fetch an arbitrarily long, ordered list of atomic premises. -/
def getAtoms {pc : pConfig} (Γ : Ctx pc) : List Nat → Option (List (Cstr pc))
  | [] => some []
  | i :: is => do
      let g ← getAtom Γ i
      let gs ← getAtoms Γ is
      return g :: gs

private theorem getAtoms_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) :
    ∀ (is : List Nat) (gs : List (Cstr pc)),
      getAtoms Γ is = some gs → ∀ g ∈ gs, g.holds ρ := by
  intro is
  induction is with
  | nil =>
      intro gs h
      simp [getAtoms] at h
      subst gs
      simp
  | cons i is ih =>
      intro gs h
      cases hi : getAtom Γ i with
      | none => simp [getAtoms, hi] at h
      | some g =>
        cases his : getAtoms Γ is with
        | none => simp [getAtoms, hi, his] at h
        | some rest =>
          have hgs : g :: rest = gs := by
            simpa [getAtoms, hi, his] using h
          subst gs
          intro d hd
          rcases List.mem_cons.mp hd with hd | hd
          · subst d
            exact getAtom_sound hΓ hi
          · exact ih rest his d hd

/-! ## Special adapters for rules whose original checkers operate on `Cstr` -/

/-- A canonical false clause, used to record a detected contradiction. -/
def falseClause {pc : pConfig} : Clause pc :=
  .cstr (.nez (.const 0))

def checkConflict {pc : pConfig} (Γ : Ctx pc) (i j : Nat)
    (c : Clause pc) : Bool :=
  match getAtom Γ i, getAtom Γ j with
  | some g1, some g2 =>
      ruleLightweightConflict g1 g2 && decide (c = falseClause)
  | _, _ => false

private theorem checkConflict_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) (i j : Nat) (c : Clause pc)
    (hc : checkConflict Γ i j c = true) : c.holds ρ := by
  cases hi : getAtom Γ i with
  | none => simp [checkConflict, hi] at hc
  | some g1 =>
    cases hj : getAtom Γ j with
    | none => simp [checkConflict, hi, hj] at hc
    | some g2 =>
      have hcheck : ruleLightweightConflict g1 g2 = true := by
        have hpair : ruleLightweightConflict g1 g2 &&
            decide (c = falseClause) = true := by
          simpa [checkConflict, hi, hj] using hc
        exact (Bool.and_eq_true_iff.mp hpair).1
      exact False.elim <| ruleLightweightConflictSound g1 g2 ρ hcheck
        (getAtom_sound hΓ hi) (getAtom_sound hΓ hj)

def checkDomain {pc : pConfig} (Γ : Ctx pc) (i : Nat)
    (c : Clause pc) : Bool :=
  match getAtom Γ i, c with
  | some g, .cstr c => ruleDomainPropagation g c
  | _, _ => false

private theorem checkDomain_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) (i : Nat) (c : Clause pc)
    (hc : checkDomain Γ i c = true) : c.holds ρ := by
  cases hi : getAtom Γ i with
  | none => simp [checkDomain, hi] at hc
  | some g =>
    cases c with
    | or _ _ => simp [checkDomain, hi] at hc
    | cstr d =>
      have hr : ruleDomainPropagation g d = true := by
        simpa [checkDomain, hi] using hc
      exact ruleDomainPropagationSound g d ρ hr (getAtom_sound hΓ hi)

def checkMonomialZero {pc : pConfig} (Γ : Ctx pc) (i j : Nat)
    (c : Clause pc) : Bool :=
  match getAtom Γ i, getAtom Γ j, c with
  | some g1, some g2, .cstr d => ruleMonomialZero g1 g2 d
  | _, _, _ => false

private theorem checkMonomialZero_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) (i j : Nat) (c : Clause pc)
    (hc : checkMonomialZero Γ i j c = true) : c.holds ρ := by
  cases hi : getAtom Γ i with
  | none => simp [checkMonomialZero, hi] at hc
  | some g1 =>
    cases hj : getAtom Γ j with
    | none => simp [checkMonomialZero, hi, hj] at hc
    | some g2 =>
      cases c with
      | or _ _ => simp [checkMonomialZero, hi, hj] at hc
      | cstr d =>
        have hr : ruleMonomialZero g1 g2 d = true := by
          simpa [checkMonomialZero, hi, hj] using hc
        exact ruleMonomialZeroSound g1 g2 d ρ hr
          (getAtom_sound hΓ hi) (getAtom_sound hΓ hj)

def checkMonomialValue {pc : pConfig} (Γ : Ctx pc)
    (i : Nat) (is : List Nat) (c : Clause pc) : Bool :=
  match getAtom Γ i, getAtoms Γ is, c with
  | some d, some gs, .cstr goal => ruleMonomialValue d gs goal
  | _, _, _ => false

private theorem checkMonomialValue_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) (i : Nat) (is : List Nat)
    (c : Clause pc) (hc : checkMonomialValue Γ i is c = true) :
    c.holds ρ := by
  cases hi : getAtom Γ i with
  | none => simp [checkMonomialValue, hi] at hc
  | some d =>
    cases his : getAtoms Γ is with
    | none => simp [checkMonomialValue, hi, his] at hc
    | some gs =>
      cases c with
      | or _ _ => simp [checkMonomialValue, hi, his] at hc
      | cstr goal =>
        have hr : ruleMonomialValue d gs goal = true := by
          simpa [checkMonomialValue, hi, his] using hc
        exact ruleMonomialValueSound d gs goal ρ hr
          (getAtom_sound hΓ hi) (getAtoms_sound hΓ is gs his)

def checkEquivalence {pc : pConfig} (Γ : Ctx pc)
    (is : List Nat) (i j : Nat) (c : Clause pc) : Bool :=
  match getAtoms Γ is, getAtom Γ i, getAtom Γ j, c with
  | some eqs, some g1, some g2, .cstr goal => ruleEquivalence eqs g1 g2 goal
  | _, _, _, _ => false

private theorem checkEquivalence_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} (hΓ : Γ.holds ρ) (is : List Nat) (i j : Nat)
    (c : Clause pc) (hc : checkEquivalence Γ is i j c = true) :
    c.holds ρ := by
  cases his : getAtoms Γ is with
  | none => simp [checkEquivalence, his] at hc
  | some eqs =>
    cases hi : getAtom Γ i with
    | none => simp [checkEquivalence, his, hi] at hc
    | some g1 =>
      cases hj : getAtom Γ j with
      | none => simp [checkEquivalence, his, hi, hj] at hc
      | some g2 =>
        cases c with
        | or _ _ => simp [checkEquivalence, his, hi, hj] at hc
        | cstr goal =>
          have hr : ruleEquivalence eqs g1 g2 goal = true := by
            simpa [checkEquivalence, his, hi, hj] using hc
          exact ruleEquivalenceSound eqs g1 g2 goal
            (getAtoms_sound hΓ is eqs his)
            (getAtom_sound hΓ hi) (getAtom_sound hΓ hj) hr

/-! ## Lift the existing Boolean checkers from premises to context indices -/

private theorem unarySound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    (Γ : Ctx pc) (c : Clause pc) (i : Nat)
    (rule : Clause pc → Clause pc → Bool)
    (hs : ∀ g, g ∈ Γ → rule g c = true → c.holds ρ)
    (h : (match Γ[i]? with | some g => rule g c | none => false) = true) :
    c.holds ρ := by
  cases hi : Γ[i]? with
  | none => simp [hi] at h
  | some g =>
    have hr : rule g c = true := by simpa [hi] using h
    exact hs g (List.mem_of_getElem? hi) hr

private theorem binarySound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    (Γ : Ctx pc) (c : Clause pc) (i j : Nat)
    (rule : Clause pc → Clause pc → Clause pc → Bool)
    (hs : ∀ g1 g2, g1 ∈ Γ → g2 ∈ Γ →
      rule g1 g2 c = true → c.holds ρ)
    (h : (match Γ[i]?, Γ[j]? with
      | some g1, some g2 => rule g1 g2 c
      | _, _ => false) = true) : c.holds ρ := by
  cases hi : Γ[i]? with
  | none => simp [hi] at h
  | some g1 =>
    cases hj : Γ[j]? with
    | none => simp [hi, hj] at h
    | some g2 =>
      have hr : rule g1 g2 c = true := by simpa [hi, hj] using h
      exact hs g1 g2 (List.mem_of_getElem? hi)
        (List.mem_of_getElem? hj) hr

/-- `c` is explicitly supplied; the chosen rule either accepts or rejects it. -/
def checkCert {pc : pConfig} (Γ : Ctx pc) (c : Clause pc) : Cert → Bool
  | .eqZero i =>
      match Γ[i]? with
      | some g => ruleEqZero g c
      | none => false
  | .distrib i =>
      match Γ[i]? with
      | some g => ruleDistrib g c
      | none => false
  | .distribEqZero i =>
      match Γ[i]? with
      | some g => ruleDistribEqZero g c
      | none => false
  | .lightweightConflict i j => checkConflict Γ i j c
  | .domainPropagation i => checkDomain Γ i c
  | .monomialZero i j => checkMonomialZero Γ i j c
  | .monomialValue i is => checkMonomialValue Γ i is c
  | .equivalence is i j => checkEquivalence Γ is i j c
  | .binary i =>
      match Γ[i]? with
      | some g => ruleBinary g c
      | none => false
  | .constant i =>
      match Γ[i]? with
      | some g => ruleConstant g c
      | none => false
  | .mergeRoots i j =>
      match Γ[i]?, Γ[j]? with
      | some g1, some g2 => ruleMergeRoots g1 g2 c
      | _, _ => false
  | .exp i =>
      match Γ[i]? with
      | some g => ruleExp g c
      | none => false

/-- Soundness of one accepted step, by delegation to existing rule soundness lemmas. -/
theorem checkCert_sound {pc : pConfig} {ρ : Nat → ZMod pc.p}
    {Γ : Ctx pc} {c : Clause pc}
    (w : Cert) (hΓ : Γ.holds ρ)
    (hc : checkCert Γ c w = true) : c.holds ρ := by
  cases w with
  | eqZero i =>
      exact unarySound Γ c i ruleEqZero
        (fun g hg hr => ruleEqZeroSound (Γ := Γ) (ρ := ρ) hΓ hg hr) hc
  | distrib i =>
      exact unarySound Γ c i ruleDistrib
        (fun g hg hr => ruleDistribSound (Γ := Γ) (ρ := ρ) hΓ hg hr) hc
  | distribEqZero i =>
      exact unarySound Γ c i ruleDistribEqZero
        (fun g hg hr => ruleDistribEqZeroSound (Γ := Γ) (ρ := ρ) hΓ hg hr) hc
  | lightweightConflict i j =>
      exact checkConflict_sound hΓ i j c hc
  | domainPropagation i =>
      exact checkDomain_sound hΓ i c hc
  | monomialZero i j =>
      exact checkMonomialZero_sound hΓ i j c hc
  | monomialValue i is =>
      exact checkMonomialValue_sound hΓ i is c hc
  | equivalence is i j =>
      exact checkEquivalence_sound hΓ is i j c hc
  | binary i =>
      exact unarySound Γ c i ruleBinary
        (fun g hg hr => ruleBinarySound ρ g c hr (hΓ g hg)) hc
  | constant i =>
      exact unarySound Γ c i ruleConstant
        (fun g hg hr => ruleConstantSound ρ g c hr (hΓ g hg)) hc
  | mergeRoots i j =>
      exact binarySound Γ c i j ruleMergeRoots
        (fun g1 g2 hg1 hg2 hr =>
          ruleMergeRootsSound ρ g1 g2 c (hΓ g1 hg1) (hΓ g2 hg2) hr) hc
  | exp i =>
      exact unarySound Γ c i ruleExp
        (fun g hg hr => ruleExpSound ρ g c (hΓ g hg) hr) hc

/-- All accepted conclusions are appended to preserve the original fact indices. -/
def checkAll {pc : pConfig} : Ctx pc → List (Step pc) → Option (Ctx pc)
  | Γ, [] => some Γ
  | Γ, (c, w) :: steps =>
      if checkCert Γ c w then
        checkAll (Γ ++ [c]) steps -- Pensar en coste de añadir al final
      else none

/-- Every fact in the final context follows from the initial context. -/
theorem checkAll_sound {pc : pConfig} {ρ : Nat → ZMod pc.p} :
    ∀ (steps : List (Step pc)) (Γ Γ' : Ctx pc),
      Γ.holds ρ → checkAll Γ steps = some Γ' → Γ'.holds ρ := by
  intro steps
  induction steps with
  | nil =>
      intro Γ Γ' hΓ he
      simp only [checkAll, Option.some.injEq] at he
      subst Γ'
      exact hΓ
  | cons step rest ih =>
      intro Γ Γ' hΓ he
      obtain ⟨c, w⟩ := step
      by_cases hc : checkCert Γ c w = true
      · have hnew : (Γ ++ [c]).holds ρ := by
          intro d hd
          rcases List.mem_append.mp hd with hold | hlast
          · exact hΓ d hold
          · have hd' : d = c := by simpa only [List.mem_singleton] using hlast
            subst d
            exact checkCert_sound w hΓ hc
        have he' : checkAll (Γ ++ [c]) rest = some Γ' := by
          simpa [checkAll, hc] using he
        exact ih (Γ ++ [c]) Γ' hnew he'
      · simp [checkAll, hc] at he

/-- Require that the very last proposed fact is `φ`, not merely that `φ` occurred earlier. -/
def checkFinal {pc : pConfig} (Γ : Ctx pc) (φ : Clause pc)
    (steps : List (Step pc)) : Bool :=
  match checkAll Γ steps with
  | none => false
  | some Γ' =>
      decide (φ ∈ Γ') &&
      match steps.getLast? with
      | none => false
      | some step => decide (step.1 = φ)

/-- Main end-to-end theorem: accepted explanations establish semantic consequence. -/
theorem checkFinal_sound {pc : pConfig} (Γ : Ctx pc) (φ : Clause pc)
    (steps : List (Step pc))
    (hc : checkFinal Γ φ steps = true) :
    ∀ ρ : Nat → ZMod pc.p, Γ.holds ρ → φ.holds ρ := by
  intro ρ hΓ
  cases he : checkAll Γ steps with
  | none => simp [checkFinal, he] at hc
  | some Γ' =>
      have hmem : φ ∈ Γ' := by
        have hp : decide (φ ∈ Γ') = true := by
          have hboth : (decide (φ ∈ Γ') &&
              (match steps.getLast? with
               | none => false
               | some step => decide (step.1 = φ))) = true := by
            simpa [checkFinal, he] using hc
          exact (Bool.and_eq_true_iff.mp hboth).1
        simpa only [decide_eq_true_eq] using hp
      exact checkAll_sound steps Γ Γ' hΓ he φ hmem

/-! ## Worked example: a seven-step derivation over ZMod 7

Initial facts:
  F0 : x*x - x = 0                 (x is Boolean)
  F1 : x = 1
  F2 : y = 3
  F3 : z = x*y
  F4 : w = z*z

The intermediate facts are appended to the context (no index shifts):
  F5  : 0 <= x <= 1               -- Binary(F0)
  F6  : 1 <= x <= 1               -- Constant(F1)
  F7  : 1 <= x <= 1               -- MergeRoots(F5,F6)
  F8  : z = 3                    -- MonomialValue(F3,F1,F2)
  F9  : w = 2                    -- MonomialValue(F4,F8), since 3*3 = 2 (mod 7)
  F10 : 2 <= w <= 2               -- Constant(F9)
  F11 : 4 <= w*w <= 4             -- Exp(F10)

Goal: derive F11 from the five initial facts.
-/

private def demoPc : pConfig := { p := 7, p_prime := by decide }

private def demoEq (v value : Nat) : Clause demoPc :=
  .cstr (.eq (.var v) (.const (value : ZMod demoPc.p)))

-- x = var 0, y = var 1, z = var 2, w = var 3
private def demoCtx : Ctx demoPc :=
  [ .cstr (.eqz (.add (.mul (.var 0) (.var 0)) (.neg (.var 0)))),
    demoEq 0 1,
    demoEq 1 3,
    .cstr (.eq (.var 2) (.mul (.var 0) (.var 1))),
    .cstr (.eq (.var 3) (.mul (.var 2) (.var 2))) ]

private def demoGoal : Clause demoPc :=
  .cstr (.range (.mul (.var 3) (.var 3)) 4 4)

private def demoSteps : List (Step demoPc) :=
  [ (.cstr (.range (.var 0) 0 1),                    .binary 0),
    (.cstr (.range (.var 0) 1 1),                    .constant 1),
    (.cstr (.range (.var 0) 1 1),                    .mergeRoots 5 6),
    (demoEq 2 3,                                    .monomialValue 3 [1, 2]),
    (demoEq 3 2,                                    .monomialValue 4 [8]),
    (.cstr (.range (.var 3) 2 2),                    .constant 9),
    (demoGoal,                                      .exp 10) ]

-- The certificate should be accepted.
example : checkFinal demoCtx demoGoal demoSteps = true := by decide

-- A single application of the general soundness theorem certifies the goal.
theorem demo_sound :
    ∀ ρ : Nat → ZMod demoPc.p,
      demoCtx.holds ρ → demoGoal.holds ρ := by
  exact checkFinal_sound demoCtx demoGoal demoSteps (by decide)

-- The same steps do not establish a different final claim.
example :
    checkFinal demoCtx
      (.cstr (.range (.mul (.var 3) (.var 3)) 5 5))
      demoSteps = false := by decide

-- Non-existent premise indices are rejected.
example :
    checkFinal demoCtx demoGoal
      [(.cstr (.range (.var 0) 0 1), .binary 99)] = false := by decide

#print axioms demo_sound

end Explanations
