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

private def checkEqs {pc : pConfig} : (List (Cstr pc)) → Option (Nat → Nat) --Creamos la correspondencia
  | [] => some id
  | (.eq (.var a) (.var b)) :: xs => do -- de momento provisional con .eq
      let ρ ← checkEqs xs
      return fun x => if x = a then b else ρ x -- Sobreescribimos, ρ[a → b]
  | _ => none

private def sustVars {pc : pConfig} (e1 e2 : Expr pc) (ρ : Nat → Nat) : Bool :=
  -- Dadas e1 e2, devuelve true si al cambiar las variables de e1 usando ρ sale e2
  -- Por induccion estructural
  match e1, e2 with
  | .var a, .var b => decide (ρ a = b)
  | .const a, .const b => decide (a = b)
  | .add a1 a2, .add b1 b2 => sustVars a1 b1 ρ && sustVars a2 b2 ρ
  | .mul a1 a2, .mul b1 b2 => sustVars a1 b1 ρ && sustVars a2 b2 ρ
  | .neg a, .neg b => sustVars a b ρ
  | _, _ => false --No coinciden ni los ASTs. OJO aqui miramos igualdad sintactica solo!!!
  -- Quizá si nos interesa permitir representaciones diversas habrá que pasar todo a
  -- una forma CANONICA!!! de momento asumimos que ya esta en esa forma...

def ruleEquivalence {pc : pConfig} (eqs : List (Cstr pc)) (g1 g2 c : Cstr pc) : Bool :=
  match g1, g2, c with
  | .eq (.var y) f,
    .eq (.var y') f',
    .eq  (.var z) (.var z') =>
      match checkEqs eqs with
      | some ρ => decide (z = y ∧ z' = y') && sustVars f f' ρ
      | none => false
  | _, _, _ => false

--Para probar f = f' modulo xi = xi' abajo
private theorem sustVarsSound {pc : pConfig} (ρ₀ : Nat → ZMod pc.p) (ρ : Nat → Nat)
    (hv : ∀ i, ρ₀ i = ρ₀ (ρ i)) : ∀ e e' : Expr pc, sustVars e e' ρ = true →
      e.eval ρ₀ = e'.eval ρ₀ := by
  intro e
  induction e with
  | var i =>
      intro e' h
      cases e' <;> simp [sustVars] at h
      rename_i j
      simp only [Expr.eval]
      calc
        ρ₀ i = ρ₀ (ρ i) := hv i
        _ = ρ₀ j := congrArg ρ₀ h

  | const c =>
      intro e' h
      cases e' <;> simp [sustVars] at h
      simpa only [Expr.eval] using h

  | add a b iha ihb =>
      intro e' h
      cases e' <;> simp [sustVars] at h
      rename_i c d
      rcases h with ⟨hc, hd⟩
      simp only [Expr.eval]
      rw [iha c hc, ihb d hd]

  | mul a b iha ihb =>
      intro e' h
      cases e' <;> simp [sustVars] at h
      rename_i c d
      rcases h with ⟨hc, hd⟩
      simp only [Expr.eval]
      rw [iha c hc, ihb d hd]

  | neg a iha =>
      intro e' h
      cases e' <;> simp [sustVars] at h
      rename_i b
      simp only [Expr.eval]
      rw [iha b h]


--Pongo directamente que g1 y g2 hold para ahorrarme el ctx
theorem ruleEquivalenceSound {pc : pConfig} {ρ₀} (eqs : List (Cstr pc)) (g1 g2 c : Cstr pc)
  (heqs : ∀ e ∈ eqs, e.holds ρ₀) (hg1 : g1.holds ρ₀) (hg2 : g2.holds ρ₀) :
  ruleEquivalence eqs g1 g2 c = true → c.holds ρ₀ := by
  intro h
  simp only [ruleEquivalence] at h
  split at h
  split at h
  rename_i g1 g2 c y f y' f' z z' x ρ heq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩

  -- Vamos a probar primero que xi = xi'
  have hxi : ∀ i : Nat, (Cstr.eq (.var i) (.var (ρ i))).holds ρ₀ := by
    clear h3
    intro i
    simp only [Cstr.holds, Expr.eval]
    induction eqs generalizing ρ with
    | nil =>
        simp [checkEqs] at heq
        rw[← heq, id_def]
        exact add_neg_cancel (ρ₀ i)
    | cons c cs ih =>
        unfold checkEqs at heq
        split at heq
        · simp at heq
          rw[← heq, id_def]
          exact add_neg_cancel (ρ₀ i)
        · rename_i x a b xs heq'
          cases hxs : checkEqs xs with
          | none =>
              simp [hxs] at heq
          | some q =>
              simp [hxs] at heq
              rw[← heq]
              by_cases ia : i = a
              · rw[ia]
                simp
                --Necesitamos ver a = b
                have hab : (Cstr.eqz ((Expr.var a).add (Expr.var b).neg)).holds ρ₀ := by
                  apply heqs
                  simp
                  left
                  cases heq'
                  rfl
                simp only [Cstr.holds, Expr.eval] at hab
                assumption
              · simp [ia]
                cases heq'
                -- Aqui paso inductivo
                apply ih
                intro e he
                exact heqs e (List.mem_cons_of_mem _ he)
                assumption
        · contradiction

  -- El tema aqui es ver que f = f' modulo xi = xi'. Con eso está hecho.
  simp only [Cstr.holds, Expr.eval] at hxi --Luego cambiar enunciado de sustVarsSound para no tener que estar cambiando hxi
  have hxi' :  ∀ (i : ℕ), ρ₀ i = ρ₀ (ρ i) := fun i => (add_neg_eq_zero.mp (hxi i))
  have hf : f.eval ρ₀ = f'.eval ρ₀ := sustVarsSound ρ₀ ρ hxi' _ _ h3

  rw [Cstr.holds] at *
  repeat rw [Expr.eval] at *
  have hg2' := add_eq_zero_iff_eq_neg.mp hg2
  rw [h1, h2,hg2', ← hf] --Algo raro pasa aqui que le cuesta muchisimo simplificar. Igual es por el ZMod. De momento lo hago a mano
  abel_nf
  abel_nf at hg1
  exact hg1

  contradiction

  contradiction
