import AlejandroPlayground.EquivalenceInference
import AlejandroPlayground.LinearClause
import AlejandroPlayground.PrimeFieldLinear

/-!
# FFSOL inference rules

This entry point imports the local rule checkers for prime-field linear reasoning (§3.2),
equivalence inference (§3.3), and linear clause inference (§3.5) in the
[FFSOL paper](https://arxiv.org/abs/2604.26709v1). The imported modules state what each accepted
step entails and, where available, provide generators for individual Lean certificates.
-/
