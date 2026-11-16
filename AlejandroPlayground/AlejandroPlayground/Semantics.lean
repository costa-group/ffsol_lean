import AlejandroPlayground.Syntax
import Mathlib.Data.ZMod.Basic
/-!
# Satisfaction and premise contexts

A valuation assigns a prime-field value to each variable index. The satisfaction predicates
interpret the syntax in that valuation. In the sense of §2.2 of the
[FFSOL paper](https://arxiv.org/abs/2604.26709v1), a soundness theorem shows that every
valuation satisfying the supplied premises also satisfies an accepted conclusion.
-/

/--
Evaluates an expression under the valuation `ρ`, performing all arithmetic in `ZMod pc.p`.
-/
def Expr.eval {pc : pConfig} (ρ : Nat → ZMod pc.p) : Expr pc → ZMod pc.p
  | .var n => ρ n
  | .const c => c
  | .add e1 e2 => e1.eval ρ + e2.eval ρ
  | .mul e1 e2 => e1.eval ρ * e2.eval ρ
  | .neg e => - e.eval ρ

/-
signed_int(f) = f    if 0 <= f < p/2 + 1
    "p/2" here is unsigned integer division rounding towards 0
signed_int(f) = f-p  if p/2 + 1 <= f < p
-/
def toSigned {pc : pConfig} (x : ZMod pc.p) : Int :=
  if x.val < pc.midpoint then
    (x.val : Int)        -- 0, 1, ... midpoint-1
  else
    (x.val : Int) - (pc.p : Int)  -- -1 (p-1), -2 (p-2), ... -midpoint (p-midpoint)

def Expr.evalInt {pc : pConfig} (ρ : Nat → ZMod pc.p) : Expr pc → Int
  | .var n => toSigned (ρ n)
  | .const c => toSigned c
  | .add e1 e2 => e1.evalInt ρ + e2.evalInt ρ
  | .mul e1 e2 => e1.evalInt ρ * e2.evalInt ρ
  | .neg e => - e.evalInt ρ

/--
Interprets an equation as zero evaluation and a disequation as nonzero evaluation.
-/
def Cstr.holds {pc : pConfig} (ρ : Nat → ZMod pc.p) : Cstr pc → Prop
  | .eqz e => e.eval ρ = 0
  | .nez e => e.eval ρ ≠ 0
  | .range e l u => let v := e.evalInt ρ; (l ≤ v) ∧ (v ≤ u)

/--
Interprets a literal by its satisfaction predicate and an `or` node by logical disjunction.
-/
def Clause.holds {pc : pConfig} (ρ : Nat → ZMod pc.p) : Clause pc  → Prop
  | .cstr c => c.holds ρ
  | .or c1 c2 => c1.holds ρ ∨ c2.holds ρ

/--
A list of clauses supplied as premises for a local deduction.
-/
abbrev Ctx (pc : pConfig) := List (Clause pc)

/--
States that every clause in `Γ` holds under `ρ`. The empty context holds under every valuation.
-/
def Ctx.holds {pc : pConfig} (ρ : Nat → ZMod pc.p) (Γ : Ctx pc) : Prop := ∀ c ∈ Γ, c.holds ρ
