import AlejandroPlayground.Printing
import AlejandroPlayground.Semantics
import Mathlib.Tactic.Abel

/-!
# Equivalence inference

Section 3.3 of the [FFSOL paper](https://arxiv.org/abs/2604.26709v1) propagates equality
between two signals defined by the same polynomial on pairwise equal inputs. For
`y = f(x₁, …, xₙ)` and `y' = f(x₁', …, xₙ')`, the rule concludes `y = y'` from
the input equalities and the two defining equations.

## Scope

`ruleEquivalence` checks an explicitly supplied, oriented renaming. The two expression trees
must agree after renaming, including operation order and grouping. The certificate generator
instantiates the same polynomial at two lists of signal indices and emits a Lean theorem that
applies `ruleEquivalenceSound`. The multiplication example exercises that path.
-/

--Creamos la correspondencia
/--
Builds a variable-index renaming from oriented premises `x = x'`, fixing unlisted indices. It
rejects other literal shapes.
-/
private def checkEqs {pc : pConfig} : List (Cstr pc) → Option (Nat → Nat)
  | [] => some id
  | (.eq (.var a) (.var b)) :: xs => do -- de momento provisional con .eq
      let ρ ← checkEqs xs
      return fun x => if x = a then b else ρ x -- Sobreescribimos, ρ[a → b]
  | _ => none

/--
Checks whether the second expression is the first with each variable index renamed by `ρ`.
Constructors, coefficient values, and the order of subexpressions must agree.
-/
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

/--
Checks the §3.3 conclusion `y = y'` against the defining equations `g1` and `g2` and the input
equalities `eqs`. The output variables must occur in the conclusion in the given order.

**Rule.** From the equalities `xᵢ = xᵢ'` for each input, together with
`y = f(x₁, …, xₙ)` and `y' = f(x₁', …, xₙ')`, infer `y = y'`. The checker compares
the two expression trees after the variable renaming supplied by the input equalities.

**Example.** From `x₀ = x₂`, `x₁ = x₃`, `x₄ = x₀ * x₁`, and `x₅ = x₂ * x₃`,
infer `x₄ = x₅`.
-/
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
/--
If the renaming preserves every variable's value under `ρ₀`, expressions accepted by `sustVars`
have the same value under `ρ₀`.
-/
private theorem sustVarsSound {pc : pConfig} (ρ₀ : Nat → ZMod pc.p) (ρ : Nat → Nat)
    (hv : ∀ i, ρ₀ i = ρ₀ (ρ i)) : ∀ e e' : Expr pc, sustVars e e' ρ = true →
      e.eval ρ₀ = e'.eval ρ₀ := by
  intro e
  induction e with
  | var i =>
      intro e' h
      cases e' <;> simp only [sustVars, Bool.false_eq_true, decide_eq_true_eq] at h
      rename_i j
      simp only [Expr.eval]
      calc
        ρ₀ i = ρ₀ (ρ i) := hv i
        _ = ρ₀ j := congrArg ρ₀ h
  | const c =>
      intro e' h
      cases e' <;> simp only [sustVars, Bool.false_eq_true, decide_eq_true_eq] at h
      simpa only [Expr.eval] using h
  | add a b iha ihb =>
      intro e' h
      cases e' <;> simp only [sustVars, Bool.false_eq_true, Bool.and_eq_true] at h
      rename_i c d
      rcases h with ⟨hc, hd⟩
      simp only [Expr.eval]
      rw [iha c hc, ihb d hd]
  | mul a b iha ihb =>
      intro e' h
      cases e' <;> simp only [sustVars, Bool.false_eq_true, Bool.and_eq_true] at h
      rename_i c d
      rcases h with ⟨hc, hd⟩
      simp only [Expr.eval]
      rw [iha c hc, ihb d hd]
  | neg a iha =>
      intro e' h
      cases e' <;> simp only [sustVars, Bool.false_eq_true] at h
      rename_i b
      simp only [Expr.eval]
      rw [iha b h]


--Pongo directamente que g1 y g2 hold para ahorrarme el ctx
/--
If the input equalities and the two defining equations hold, an accepted equivalence conclusion
holds under the same valuation.
-/
theorem ruleEquivalenceSound {pc : pConfig} {ρ₀} (eqs : List (Cstr pc)) (g1 g2 c : Cstr pc)
  (heqs : ∀ e ∈ eqs, e.holds ρ₀) (hg1 : g1.holds ρ₀) (hg2 : g2.holds ρ₀) :
  ruleEquivalence eqs g1 g2 c = true → c.holds ρ₀ := by
  intro h
  simp only [ruleEquivalence] at h
  split at h
  · split at h
    · rename_i g1 g2 c y f y' f' z z' x ρ heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨h1, h2⟩, h3⟩
      -- Vamos a probar primero que xi = xi'
      have hxi : ∀ i : Nat, (Cstr.eq (.var i) (.var (ρ i))).holds ρ₀ := by
        clear h3
        intro i
        simp only [Cstr.holds, Expr.eval]
        induction eqs generalizing ρ with
        | nil =>
            simp only [checkEqs, Option.some.injEq] at heq
            rw[← heq, id_def]
            exact add_neg_cancel (ρ₀ i)
        | cons c cs ih =>
            unfold checkEqs at heq
            split at heq
            · simp only [Option.some.injEq] at heq
              rw[← heq, id_def]
              exact add_neg_cancel (ρ₀ i)
            · rename_i x a b xs heq'
              cases hxs : checkEqs xs with
              | none =>
                  simp [hxs] at heq
              | some q =>
                  simp only [hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                    Option.some.injEq] at heq
                  rw[← heq]
                  by_cases ia : i = a
                  · rw[ia]
                    simp only [↓reduceIte]
                    --Necesitamos ver a = b
                    have hab : (Cstr.eqz ((Expr.var a).add (Expr.var b).neg)).holds ρ₀ := by
                      apply heqs
                      simp only [List.mem_cons]
                      left
                      cases heq'
                      rfl
                    simp only [Cstr.holds, Expr.eval] at hab
                    assumption
                  · simp only [ite_eq_right ia]
                    cases heq'
                    -- Aqui paso inductivo
                    exact ih (fun e he => heqs e (List.mem_cons_of_mem _ he)) q hxs
            · contradiction
      -- El tema aqui es ver que f = f' modulo xi = xi'. Con eso está hecho.
      --Luego cambiar enunciado de sustVarsSound para no tener que estar cambiando hxi
      simp only [Cstr.holds, Expr.eval] at hxi
      have hxi' :  ∀ (i : ℕ), ρ₀ i = ρ₀ (ρ i) := fun i => (add_neg_eq_zero.mp (hxi i))
      have hf : f.eval ρ₀ = f'.eval ρ₀ := sustVarsSound ρ₀ ρ hxi' _ _ h3
      rw [Cstr.holds] at *
      repeat rw [Expr.eval] at *
      have hg2' := add_eq_zero_iff_eq_neg.mp hg2
      --Algo raro pasa aqui que le cuesta muchisimo simplificar. Igual es por el ZMod.
      -- De momento lo hago a mano
      rw [h1, h2, hg2', ← hf]
      abel_nf
      abel_nf at hg1
      exact hg1
    · contradiction
  · contradiction

-- CERTIFICADO

/--
States that every variable in the expression has an index strictly below `n`, the arity of the
polynomial template.
-/
def Expr.InRange {pc : pConfig} (n : Nat) : Expr pc → Prop
  | .var i => i < n
  | .const _ => True
  | .add e1 e2 => e1.InRange n ∧ e2.InRange n
  | .mul e1 e2 => e1.InRange n ∧ e2.InRange n
  | .neg e => e.InRange n

/--
Instantiates the variable at position `i` with the variable indexed by `xs[i]`. An index outside
the list is left unchanged.
-/
def sustFVars {pc : pConfig} (f : Expr pc) (xs : List Nat) : Expr pc :=
  let n := xs.length
  match f with
  | .var i => if h : i < n then .var (xs[i]) else f
  | .const _ => f
  | .add e1 e2 => .add (sustFVars e1 xs) (sustFVars e2 xs)
  | .mul e1 e2 => .mul (sustFVars e1 xs) (sustFVars e2 xs)
  | .neg e => .neg (sustFVars e xs)

/--
Emits a Lean theorem for the §3.3 inference on the two instantiations of `f`. The input lists
must have equal length and cover every variable index in `f`. `f` is assumed to have all its
variables in the range `[0, xs.length)`. Then, `f` is instantiated at `xs` and `xs'` to produce
the two defining equations, by substituting the variable at position `i` with the variable indexed
by `xs[i]` or `xs'[i]`.

**Input.** `xs` and `xs'` give the two lists of input variable indices. `y` and `y'`
are the output variable indices. The remaining inputs are the expression template `f` and
proofs that the lists have equal length and that every index in `f` is in range.

**Output.** A string containing a theorem named `equivalence_certificate`. Its hypotheses
are the pairwise input equalities and the two output equations. Its conclusion is `y = y'`.
The generated proof applies `ruleEquivalenceSound` and uses `rfl` to prove that the
Boolean checker accepts the step when Lean elaborates the declaration.

**Example.** With `xs = [0]`, `xs' = [1]`, `y = 2`, `y' = 3`, and `f = -x₀`,
the generated theorem proves `x₂ = x₃` from `x₀ = x₁`, `x₂ = -x₀`, and `x₃ = -x₁`.

```lean
#eval do
  let pc : pConfig := ⟨7, by decide⟩
  let f : Expr pc := .neg (.var 0)
  IO.println (EquivalenceInference.certificate [0] [1] 2 3 f
    (by decide) (by simp [f, Expr.InRange]))
```

The output below is line-wrapped for readability.

```lean
theorem equivalence_certificate {pc : pConfig}
    (ρ₀ : Nat → ZMod pc.p)
    (heqs : ∀ e ∈ ([(Cstr.eqz (Expr.add (Expr.var 0) (Expr.neg (Expr.var 1))))]
      : List (Cstr pc)), e.holds ρ₀)
    (hg1 : ((Cstr.eqz (Expr.add (Expr.var 2) (Expr.neg (Expr.neg (Expr.var 0)))))
      : Cstr pc).holds ρ₀)
    (hg2 : ((Cstr.eqz (Expr.add (Expr.var 3) (Expr.neg (Expr.neg (Expr.var 1)))))
      : Cstr pc).holds ρ₀) :
    ((Cstr.eqz (Expr.add (Expr.var 2) (Expr.neg (Expr.var 3)))) : Cstr pc).holds ρ₀ := by
  exact ruleEquivalenceSound
    ([(Cstr.eqz (Expr.add (Expr.var 0) (Expr.neg (Expr.var 1))))] : List (Cstr pc))
    ((Cstr.eqz (Expr.add (Expr.var 2) (Expr.neg (Expr.neg (Expr.var 0))))) : Cstr pc)
    ((Cstr.eqz (Expr.add (Expr.var 3) (Expr.neg (Expr.neg (Expr.var 1))))) : Cstr pc)
    ((Cstr.eqz (Expr.add (Expr.var 2) (Expr.neg (Expr.var 3)))) : Cstr pc)
    heqs hg1 hg2 (by rfl)
```
-/
def EquivalenceInference.certificate {pc : pConfig}
    (xs xs' : List Nat)
    (y y' : Nat)
    (f : Expr pc)
    (_ : xs.length = xs'.length)
    (_ : f.InRange xs.length) : String :=
    -- Muy Importante: f es una expresión que representa al polinomio f.
    -- La idea es que las variables de f van de 0 a n-1, siendo n la longitud
    -- de xs y xs'. Supongo que f(xi) se obtiene sustituyendo la variable
    -- .var i por .var xs[i], y f(xi') se obtiene sustituyendo la variable
    --.var i por .var xs'[i]. De moemnto esas condiciones van como premisas,
    -- pero es provisional como todo.
    -- Primer paso, construir la lista de ecuaciones xi = xi' para cada i
    let eqs : List (Cstr pc) := List.zipWith (fun x x' => Cstr.eq (.var x) (.var x')) xs xs'
    -- Ahora el string
    let eqsStr := "[" ++ String.intercalate ", " (eqs.map Cstr.meta) ++ "]"
    -- Segundo paso, y = f(xi), y' = f(xi')
    let f_xs := sustFVars f xs
    let f_xs' := sustFVars f xs'
    let fStr := Cstr.meta (Cstr.eq (.var y) f_xs)
    let fStr' := Cstr.meta (Cstr.eq (.var y') f_xs')
    -- Tercer paso, la conclusión y = y'
    let concl : Cstr pc := Cstr.eq (.var y) (.var y')
    let conclStr := Cstr.meta concl
    -- Finalmente, concatenar todo
    String.intercalate "\n" [
      "theorem equivalence_certificate {pc : pConfig}",
      "    (ρ₀ : Nat → ZMod pc.p)",
      s!"    (heqs : ∀ e ∈ ({eqsStr} : List (Cstr pc)), e.holds ρ₀)",
      s!"    (hg1 : ({fStr} : Cstr pc).holds ρ₀)",
      s!"    (hg2 : ({fStr'} : Cstr pc).holds ρ₀) :",
      s!"    ({conclStr} : Cstr pc).holds ρ₀ := by",
      "  exact ruleEquivalenceSound",
      s!"    ({eqsStr} : List (Cstr pc))",
      s!"    ({fStr} : Cstr pc)",
      s!"    ({fStr'} : Cstr pc)",
      s!"    ({conclStr} : Cstr pc)",
      "    heqs hg1 hg2 (by rfl)" -- Habrá que estar seguros que rfl siempre puede.
    ]
    -- Por ultimo, puede haber problemas si xs tiene duplicados, de momento paso.

-- Ejemplo de certificado

#eval do
  let pc : pConfig := ⟨7, by decide⟩
  let f : Expr pc := .mul (.var 0) (.var 1)
  IO.println <| EquivalenceInference.certificate
    [0, 1]    -- xs
    [2, 3]    -- xs'
    4 5       -- y, y'
    f
    (by decide)
    (by simp [f, Expr.InRange])

/--
Checks the concrete §3.3 certificate for two product signals whose corresponding input signals
agree.
-/
theorem equivalence_certificate {pc : pConfig}
    (ρ₀ : Nat → ZMod pc.p)
    (heqs : ∀ e ∈ ([.eq (.var 0) (.var 2), .eq (.var 1) (.var 3)] : List (Cstr pc)),
      e.holds ρ₀)
    (hg1 : (Cstr.eq (.var 4) (.mul (.var 0) (.var 1))).holds ρ₀)
    (hg2 : (Cstr.eq (.var 5) (.mul (.var 2) (.var 3))).holds ρ₀) :
    (Cstr.eq (.var 4) (.var 5)).holds ρ₀ := by
  exact ruleEquivalenceSound _ _ _ _ heqs hg1 hg2 (by rfl)

-- Aceptado
