import Mathlib

/-!
# Erdős Problem #403 — sums of distinct factorials that are powers of 2

**Problem (Burr–Erdős; [ErGr80, p.79]).** Does
`2^m = a₁! + a₂! + ⋯ + aₖ!` with `a₁ < a₂ < ⋯ < aₖ` have only finitely many solutions?

**Answer: yes** (Frankl and Shen Lin, independently, 1976 — both proofs *unpublished*;
Lin's was a Bell Labs internal memorandum, "On Two Problems of Erdős Concerning Sums of
Distinct Factorials"). The largest solution is `2⁷ = 2! + 3! + 5! = 128`. Lin further showed
the largest power of `2` dividing a sum of distinct factorials *containing* `2!` is `2²⁵⁴`.

Because the original proofs are lost to the literature, this is a **reconstruction**, not a
transcription. The engine is Legendre's formula at `p = 2`: `v₂(n!) = n − s₂(n)` (mathlib:
`sub_one_mul_padicValNat_factorial`), the size sandwich `aₖ! ≤ S < 2·aₖ!`, and a bounded-carry
argument controlling `v₂` of the sum. The finite endgame is decidable via the factorial number
system (a sum of distinct factorials is exactly a factorial-base numeral with all digits ≤ 1).

A "sum of distinct factorials" is modelled by a `Finset ℕ` of indices (distinctness of the
`aᵢ` is automatic). Note `0! = 1! = 1`, so e.g. `{0,1}` sums to `2`.
-/

namespace Erdos403

open Finset
open scoped Nat

/-- The sum of distinct factorials indexed by `S`: `∑_{a ∈ S} a!`. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

/-- The extremal witness: `2! + 3! + 5! = 2 + 6 + 120 = 128 = 2⁷`.
(`native_decide` because `Finset.sum` reduces through `Quot` and the kernel `decide` gets
stuck; this is isolated to the witness and doesn't touch the main theorems.) -/
theorem witness : factSum {2, 3, 5} = 2 ^ 7 := by native_decide

/-- **Erdős #403 (finiteness)** — this is exactly what the problem asks.
Only finitely many sums of distinct factorials are powers of `2`. -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite := by
  sorry

/-- **Erdős #403 (sharp form)** — the largest such power of `2` is `2⁷`.
Equivalently every solution has `m ≤ 7`, and `m = 7` is attained by `witness`. -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := by
  sorry

end Erdos403
