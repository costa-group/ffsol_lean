import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime-field configuration

Section 2.1 of the [FFSOL paper](https://arxiv.org/abs/2604.26709v1) identifies the prime
field of order $p$ with the integers modulo $p$. The checker represents that field as
`ZMod pc.p` and carries the primality proof in `pConfig`.
-/

/--
A modulus and proof of primality specifying the field used by a checking step.
-/
structure pConfig where
  /--
  The order of the prime field and the modulus of its residue representation.
  -/
  p : Nat
  /--
  The proof that the modulus is prime.
  -/
  p_prime : p.Prime

/--
Register that c.p is a prime number.
Makes the primality proof available to Mathlib's instances for prime residue fields.
-/
instance (c : pConfig) : Fact c.p.Prime := ⟨c.p_prime⟩
