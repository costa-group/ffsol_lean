import AlejandroPlayground.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Syntax of prime-field constraints

This file represents polynomial expressions, theory literals, and clauses as used in
§§2.1–2.2 and §3 of the [FFSOL paper](https://arxiv.org/abs/2604.26709v1).
-/

/--
A polynomial expression over `ZMod pc.p` built from variable indices, constants, sums, negation,
and products.
-/
inductive Expr (pc : pConfig) where
  | var (n : Nat)
  | const (c : ZMod pc.p)
  | add (e1 : Expr pc) (e2 : Expr pc)
  | neg (e : Expr pc)
  | mul (e1 : Expr pc) (e2 : Expr pc)
  deriving DecidableEq

/--
An equation or disequation against zero, representing a theory literal in FFSOL.
-/
inductive Cstr (pc : pConfig) where
  | eqz : Expr pc → Cstr pc
  | nez : Expr pc → Cstr pc
  deriving DecidableEq

/--
A single theory literal or a binary disjunction of clauses.
-/
inductive Clause (pc : pConfig) where
  | cstr : Cstr pc → Clause pc
  | or : Clause pc → Clause pc → Clause pc
  deriving DecidableEq

-- Useful defitions for this module
/--
Represents subtraction by addition of the negated right-hand side, with support for matching
this shape.
-/
@[match_pattern]
def Expr.sub {pc : pConfig} (a b : Expr pc) : Expr pc := .add a (.neg b)

/--
Represents the equation `a = b` by requiring `a - b` to vanish.
-/
@[match_pattern] --Para que me funcionen los matchs
def Cstr.eq {pc : pConfig} (a b : Expr pc) : Cstr pc := .eqz (Expr.sub a b)

/--
Represents the disequation `a ≠ b` by requiring `a - b` to be nonzero.
-/
@[match_pattern]
def Cstr.ne {pc : pConfig} (a b : Expr pc) : Cstr pc := .nez (Expr.sub a b)
