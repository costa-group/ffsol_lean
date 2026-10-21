/-! Reflective checker for interval constraints with three rules: eq, trans, weaken.
    Core Lean only. A solver emits a list of (claim, certificate) steps; the kernel
    checks them with `decide +kernel` and `checkAll_sound` turns success into a proof. -/

/-! ## Syntax and semantics -/

inductive Expr
  | var (n : Nat) | const (z : Int) | add (a b : Expr) | mul (a b : Expr)
  deriving DecidableEq

inductive Cstr
  | mem (e : Expr) (lo hi : Int)   -- e ∈ [lo..hi]
  | ge (a b : Expr)                -- a ≥ b
  | le (a b : Expr)                -- a ≤ b
  deriving DecidableEq

/-- Value of an expression under the variable assignment `ρ`. -/
def Expr.eval (ρ : Nat → Int) : Expr → Int
  | .var n => ρ n
  | .const z => z
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ

/-- Meaning of a constraint under `ρ`. -/
def Cstr.holds (ρ : Nat → Int) : Cstr → Prop
  | .mem e lo hi => lo ≤ e.eval ρ ∧ e.eval ρ ≤ hi
  | .ge a b => b.eval ρ ≤ a.eval ρ
  | .le a b => a.eval ρ ≤ b.eval ρ

abbrev Ctx := List Cstr

/-- All constraints of the context hold under `ρ`. -/
def Ctx.holds (ρ : Nat → Int) (Γ : Ctx) : Prop := ∀ c ∈ Γ, c.holds ρ

/-! ## Interval evaluation (used by rule `eq`) -/

/-- Interval of variable `n`: taken from the first matching `mem` in the context. -/
def look (n : Nat) : Ctx → Option (Int × Int)
  | [] => none
  | .mem (.var m) lo hi :: r => if m = n then some (lo, hi) else look n r
  | _ :: r => look n r

theorem look_sound {ρ Γ n lo hi} (h : Γ.holds ρ) :
    look n Γ = some (lo, hi) → lo ≤ ρ n ∧ ρ n ≤ hi := by
  induction Γ with
  | nil => simp [look]
  | cons g r ih =>
    have hr : Ctx.holds ρ r := fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hg := h g (List.mem_cons_self ..)
    match g, hg with
    | .mem (.var m) lo' hi', hg =>
      simp only [look]
      split
      · next hm => subst hm; intro e; cases e; exact hg
      · exact ih hr
    | .mem (.const _) _ _, _ => simpa [look] using ih hr
    | .mem (.add _ _) _ _, _ => simpa [look] using ih hr
    | .mem (.mul _ _) _ _, _ => simpa [look] using ih hr
    | .ge _ _, _ => simpa [look] using ih hr
    | .le _ _, _ => simpa [look] using ih hr

/-- Interval containing the value of `e`, or `none` if we cannot tell.
    `mul` is only handled for non-negative intervals. -/
def bounds (Γ : Ctx) : Expr → Option (Int × Int)
  | .var n => look n Γ
  | .const z => some (z, z)
  | .add a b => do
      let (la, ha) ← bounds Γ a
      let (lb, hb) ← bounds Γ b
      pure (la + lb, ha + hb)
  | .mul a b => do
      let (la, ha) ← bounds Γ a
      let (lb, hb) ← bounds Γ b
      if 0 ≤ la ∧ 0 ≤ lb then pure (la * lb, ha * hb) else none

/-- If `bounds` answers `(lo, hi)`, the value of `e` really lies in `[lo, hi]`. -/
theorem bounds_sound {ρ Γ} (h : Γ.holds ρ) (e : Expr) :
    ∀ lo hi, bounds Γ e = some (lo, hi) → lo ≤ e.eval ρ ∧ e.eval ρ ≤ hi := by
  induction e with
  | var n => intro lo hi hb; exact look_sound h hb
  | const z => intro lo hi hb; simp [bounds] at hb; simp only [Expr.eval]; omega
  | add a b iha ihb =>
    intro lo hi hb
    simp only [bounds] at hb
    cases ha : bounds Γ a with
    | none => simp [ha] at hb
    | some pa =>
      cases hb' : bounds Γ b with
      | none => simp [ha, hb'] at hb
      | some pb =>
        simp [ha, hb'] at hb
        have h1 := iha _ _ ha
        have h2 := ihb _ _ hb'
        simp only [Expr.eval]; omega
  | mul a b iha ihb =>
    intro lo hi hb
    simp only [bounds] at hb
    cases ha : bounds Γ a with
    | none => simp [ha] at hb
    | some pa =>
      cases hb' : bounds Γ b with
      | none => simp [ha, hb'] at hb
      | some pb =>
        simp only [ha, hb'] at hb
        by_cases hpos : 0 ≤ pa.1 ∧ 0 ≤ pb.1
        · simp [hpos] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have h1 := iha _ _ ha
          have h2 := ihb _ _ hb'
          simp only [Expr.eval]
          constructor
          · exact Int.mul_le_mul h1.1 h2.1 hpos.2 (Int.le_trans hpos.1 h1.1)
          · exact Int.mul_le_mul h1.2 h2.2 (Int.le_trans hpos.2 h2.1)
              (Int.le_trans (Int.le_trans hpos.1 h1.1) h1.2)
        · simp [hpos] at hb

/-! ## Rule `eq`:  y ≥ e, y ≤ e, e ∈ [l,h] ⊆ [lo,hi]  ⊢  y ∈ [lo,hi] -/

/-- `g1`, `g2` are the two premises taken from `Γ`; `c` is the claim. -/
def ruleEqWith (g1 g2 : Cstr) (Γ : Ctx) (c : Cstr) : Bool :=
  match g1, g2, c with
  | .ge (.var y1) e1, .le (.var y2) e2, .mem (.var y) lo hi =>
      y1 = y && y2 = y && e1 = e2 &&              -- both premises: y = e
      (match bounds Γ e1 with                     -- derive e ∈ [l,h] from Γ
       | some (l, h) => decide (lo ≤ l) && decide (h ≤ hi)
       | none => false)
  | _, _, _ => false

theorem ruleEqWith_sound {ρ Γ g1 g2 c} (h : Γ.holds ρ) (h1 : g1 ∈ Γ) (h2 : g2 ∈ Γ) :
    ruleEqWith g1 g2 Γ c = true → c.holds ρ := by
  have hg1 := h _ h1
  have hg2 := h _ h2
  unfold ruleEqWith
  split
  · next y1 e1 y2 e2 y lo hi =>
    intro hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨hy1, hy2⟩, he⟩, hb⟩ := hr
    subst hy1 hy2 he
    split at hb
    · next l h' hbd =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have := bounds_sound h _ _ _ hbd
      simp only [Cstr.holds, Expr.eval] at hg1 hg2 ⊢
      omega
    · simp at hb
  · simp

/-! ## Rule `trans`:  a ≥ b, b ≥ d  ⊢  a ≥ d -/

def ruleTransWith (g1 g2 c : Cstr) : Bool :=
  match g1, g2, c with
  | .ge a b, .ge b' d, .ge a' d' => a = a' && b = b' && d = d'
  | _, _, _ => false

theorem ruleTransWith_sound {ρ} {Γ : Ctx} {g1 g2 c} (h : Γ.holds ρ) (h1 : g1 ∈ Γ) (h2 : g2 ∈ Γ) :
    ruleTransWith g1 g2 c = true → c.holds ρ := by
  have hg1 := h _ h1
  have hg2 := h _ h2
  unfold ruleTransWith
  split
  · next a b b' d a' d' =>
    intro hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨⟨ha, hb⟩, hd⟩ := hr
    subst ha hb hd
    simp only [Cstr.holds] at hg1 hg2 ⊢
    omega
  · simp

/-! ## Rule `weaken`:  e ∈ [l,h], [l,h] ⊆ [lo,hi]  ⊢  e ∈ [lo,hi] -/

def ruleWeakenWith (g c : Cstr) : Bool :=
  match g, c with
  | .mem e l h, .mem e' lo hi => e = e' && decide (lo ≤ l) && decide (h ≤ hi)
  | _, _ => false

theorem ruleWeakenWith_sound {ρ} {Γ : Ctx} {g c} (h : Γ.holds ρ) (h1 : g ∈ Γ) :
    ruleWeakenWith g c = true → c.holds ρ := by
  have hg := h _ h1
  unfold ruleWeakenWith
  split
  · next e l h' e' lo hi =>
    intro hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨⟨he, hl⟩, hh⟩ := hr
    subst he
    simp only [Cstr.holds] at hg ⊢
    omega
  · simp

/-! ## Certificates and the checker -/

/-- One constructor per rule; the numbers are positions of the premises in Γ. -/
inductive Cert
  | eq (i j : Nat)      -- Γ[i] : y ≥ e,  Γ[j] : y ≤ e
  | trans (i j : Nat)   -- Γ[i] : a ≥ b,  Γ[j] : b ≥ d
  | weaken (i : Nat)    -- Γ[i] : e ∈ [l,h]

/-- Fetch the premises named by the certificate and run the corresponding rule. -/
def checkCert (Γ : Ctx) (c : Cstr) : Cert → Bool
  | .eq i j => match Γ[i]?, Γ[j]? with
      | some g1, some g2 => ruleEqWith g1 g2 Γ c
      | _, _ => false
  | .trans i j => match Γ[i]?, Γ[j]? with
      | some g1, some g2 => ruleTransWith g1 g2 c
      | _, _ => false
  | .weaken i => match Γ[i]? with
      | some g => ruleWeakenWith g c
      | none => false

/-- Accepting a certificate means the claim follows from the context. -/
theorem checkCert_sound {ρ Γ c} (w : Cert) (h : Γ.holds ρ) :
    checkCert Γ c w = true → c.holds ρ := by
  cases w with
  | eq i j =>
    simp only [checkCert]; split
    · next g1 g2 e1 e2 =>
      exact ruleEqWith_sound h (List.mem_of_getElem? e1) (List.mem_of_getElem? e2)
    · simp
  | trans i j =>
    simp only [checkCert]; split
    · next g1 g2 e1 e2 =>
      exact ruleTransWith_sound h (List.mem_of_getElem? e1) (List.mem_of_getElem? e2)
    · simp
  | weaken i =>
    simp only [checkCert]; split
    · next g e1 => exact ruleWeakenWith_sound h (List.mem_of_getElem? e1)
    · simp

/-! ## Derivations: a list of steps, each proved claim is pushed onto the context -/

abbrev Step := Cstr × Cert

/-- Check the steps in order; `none` if any step fails, else the final context. -/
def checkAll : Ctx → List Step → Option Ctx
  | Γ, [] => some Γ
  | Γ, (c, w) :: rest => if checkCert Γ c w then checkAll (c :: Γ) rest else none

/-- If all steps pass, every constraint of the final context holds. -/
theorem checkAll_sound {ρ} : ∀ (steps : List Step) (Γ Γ' : Ctx),
    Γ.holds ρ → checkAll Γ steps = some Γ' → Γ'.holds ρ := by
  intro steps
  induction steps with
  | nil => intro Γ Γ' h e; simp [checkAll] at e; subst e; exact h
  | cons s rest ih =>
    intro Γ Γ' h e
    obtain ⟨c, w⟩ := s
    simp only [checkAll] at e
    split at e
    · next hc =>
      refine ih (c :: Γ) Γ' ?_ e
      intro d hd
      cases List.mem_cons.mp hd with
      | inl hd => subst hd; exact checkCert_sound w h hc
      | inr hd => exact h d hd
    · simp at e

/-! ## Example: x ∈ [1..10], y = x*x, z ≥ y  ⊢  y ∈ [1,100], y ∈ [0,200], z ≥ x*x -/

def x : Expr := .var 0
def y : Expr := .var 1
def z : Expr := .var 2

def Γ₀ : Ctx := [.mem x 1 10, .ge y (.mul x x), .le y (.mul x x), .ge z y]

/-- The solver's certificate. The context grows at the front, so indices shift:
    before step 3 it is [y∈[0,200], y∈[1,100], x∈[1,10], y≥x*x, y≤x*x, z≥y]. -/
def deriv : List Step :=
  [ (.mem y 1 100,     .eq 1 2),       -- from Γ₀[1], Γ₀[2]
    (.mem y 0 200,     .weaken 0),     -- from the step-1 result
    (.ge z (.mul x x), .trans 5 3) ]   -- z ≥ y (5), y ≥ x*x (3)

/-- Shippable theorem: one kernel evaluation of `checkAll` proves all three facts. -/
theorem final : ∀ ρ, Γ₀.holds ρ →
    (Cstr.mem y 1 100).holds ρ ∧ (Cstr.mem y 0 200).holds ρ ∧ (Cstr.ge z (.mul x x)).holds ρ := by
  intro ρ h
  have e : checkAll Γ₀ deriv =
      some (.ge z (.mul x x) :: .mem y 0 200 :: .mem y 1 100 :: Γ₀) := by decide +kernel
  have := checkAll_sound deriv Γ₀ _ h e
  exact ⟨this _ (by simp), this _ (by simp), this _ (by simp)⟩

#print axioms final

-- Bad certificates are rejected: wrong claim, wrong indices.
example : checkAll Γ₀ [(.mem y 1 99, .eq 1 2)] = none := by decide +kernel
example : checkAll Γ₀ [(.mem y 1 100, .eq 0 2)] = none := by decide +kernel
