import AlejandroPlayground.Syntax
import Mathlib.Data.ZMod.Basic

/-!
# Rendering expressions and clauses

The `print` functions produce human-readable formulas. The `meta` functions emit Lean
constructor terms for the certificate generators.
A coefficient is printed as the natural representative of its value in the source field.
The generated terms are interpreted in the field specified by the certificate theorem.
-/

-- Voy a hacer un pretty printer para probar

/--
Renders a polynomial expression using subscripted variable indices and parenthesized operations.
-/
def Expr.print {pc : pConfig} : Expr pc → String
  | .var n => "x" ++ n.toSubscriptString -- Asumo var n como xₙ
  | .const c => toString c.val
  | .add e1 e2 => s!"({e1.print} + {e2.print})"
  | .mul e1 e2 => s!"({e1.print} * {e2.print})"
  | .neg e => s!"(-{e.print})"

/--
Renders a theory literal as an equation or disequation against zero.
-/
def Cstr.print {pc : pConfig} : Cstr pc → String
  | .eqz e => s!"{e.print} = 0"
  | .nez e => s!"{e.print} ≠ 0"

/--
Renders the literals of a clause as a disjunction in their original order.
-/
def Clause.print {pc : pConfig} : Clause pc → String
  | .cstr c => c.print
  | .or c1 c2 => s!"{c1.print} ∨ {c2.print}"

/--
Emits Lean constructor syntax for an expression, preserving its tree and using numerals for
constants.
-/
def Expr.meta {pc : pConfig} : Expr pc → String
  | .var n => s!"(Expr.var {n})"
  | .const c => s!"(Expr.const {c.val})"
  | .add e₁ e₂ => s!"(Expr.add {e₁.meta} {e₂.meta})"
  | .mul e₁ e₂ => s!"(Expr.mul {e₁.meta} {e₂.meta})"
  | .neg e => s!"(Expr.neg {e.meta})"

/--
Emits a Lean term using `Cstr.eqz` or `Cstr.nez` and the rendered expression.
-/
def Cstr.meta {pc : pConfig} : Cstr pc → String
  | .eqz e => s!"(Cstr.eqz {e.meta})"
  | .nez e => s!"(Cstr.nez {e.meta})"

/--
Emits Lean constructor syntax for a clause, preserving its binary disjunction tree.
-/
def Clause.meta {pc : pConfig} : Clause pc → String
  | .cstr c => s!"(Clause.cstr {c.meta})"
  | .or c₁ c₂ => s!"(Clause.or {c₁.meta} {c₂.meta})"
