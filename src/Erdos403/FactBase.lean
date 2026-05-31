import Mathlib
import Erdos403.Basic

/-!
# The factorial number system (for Erdős #403)

The unique mixed-radix representation `n = ∑_{i≥1} dᵢ·i!` with `0 ≤ dᵢ ≤ i`, where
`dᵢ = (n / i!) mod (i+1)`. A number is a **sum of distinct factorials** (indices `≥ 1`) iff every
digit is `≤ 1`. This is the engine for the sharp form `m ≤ 7` of #403: the question becomes a
digit condition on `2^m`.

This file builds the infrastructure (Phase A of `PLAN.md`):
* `factDigit` and its bound,
* the reconstruction `n = ∑ dᵢ·i!` (telescoping div/mod),
* (later) the distinct-factorials criterion and decidability.
-/

namespace Erdos403

open Finset
open scoped Nat

/-- The `i`-th factorial-base digit of `n`: `dᵢ(n) = ⌊n / i!⌋ mod (i+1)`. -/
def factDigit (i n : ℕ) : ℕ := (n / i !) % (i + 1)

/-- Digits are bounded: `dᵢ(n) ≤ i`. -/
theorem factDigit_le (i n : ℕ) : factDigit i n ≤ i := by
  have : factDigit i n < i + 1 := Nat.mod_lt _ (Nat.succ_pos i)
  omega

/-- **Reconstruction with remainder.** For every cutoff `B`,
`(∑_{1 ≤ i ≤ B} dᵢ(n)·i!) + ⌊n/(B+1)!⌋·(B+1)! = n`. The trailing term telescopes away once
`(B+1)! > n`. -/
theorem factDigit_recon (n : ℕ) :
    ∀ B, (∑ i ∈ Finset.Ico 1 (B + 1), factDigit i n * i !) + n / (B + 1)! * (B + 1)! = n := by
  intro B
  induction B with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
    -- reduce the new top term + new remainder to the old remainder, then apply `ih`
    have hfac : (k + 1 + 1)! = (k + 2) * (k + 1)! := by
      rw [Nat.factorial_succ]
    have hdiv : n / (k + 1 + 1)! = n / (k + 1)! / (k + 2) := by
      rw [hfac, Nat.div_div_eq_div_mul, Nat.mul_comm]
    set q := n / (k + 1)! with hq
    have key : factDigit (k + 1) n * (k + 1)! + n / (k + 1 + 1)! * (k + 1 + 1)!
        = q * (k + 1)! := by
      rw [hdiv, hfac, factDigit, ← hq]
      have hmd : q % (k + 2) + q / (k + 2) * (k + 2) = q := Nat.mod_add_div' q (k + 2)
      calc q % (k + 2) * (k + 1)! + q / (k + 2) * ((k + 2) * (k + 1)!)
          = (q % (k + 2) + q / (k + 2) * (k + 2)) * (k + 1)! := by ring
        _ = q * (k + 1)! := by rw [hmd]
    rw [add_assoc, key]
    exact ih

/-- **Reconstruction.** If `n < (B+1)!` then `n = ∑_{1 ≤ i ≤ B} dᵢ(n)·i!`. -/
theorem factDigit_sum (n B : ℕ) (hB : n < (B + 1)!) :
    n = ∑ i ∈ Finset.Ico 1 (B + 1), factDigit i n * i ! := by
  have h := factDigit_recon n B
  have : n / (B + 1)! = 0 := Nat.div_eq_of_lt hB
  rw [this, Nat.zero_mul, Nat.add_zero] at h
  exact h.symm

/-- The factorials below `i` (positive indices) sum to less than `i!`. -/
theorem sum_lt_factorial_of_lt (T : Finset ℕ) (hT : ∀ a ∈ T, 1 ≤ a) (i : ℕ) :
    ∑ a ∈ T.filter (· < i), a ! < i ! := by
  have hsub : T.filter (· < i) ⊆ Finset.Ico 1 i := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_Ico.mpr ⟨hT a ha.1, ha.2⟩
  have h1 : ∑ a ∈ T.filter (· < i), a ! ≤ ∑ a ∈ Finset.Ico 1 i, a ! :=
    Finset.sum_le_sum_of_subset hsub
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have he0 : T.filter (· < 0) = ∅ := by ext x; simp
    rw [he0, Finset.sum_empty]; simp
  · have hsplit : 1 + ∑ a ∈ Finset.Ico 1 i, a ! = ∑ a ∈ Finset.range i, a ! := by
      have h0 : (0 : ℕ) ∈ Finset.range i := Finset.mem_range.mpr hi
      have herase : (Finset.range i).erase 0 = Finset.Ico 1 i := by
        ext x; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]; omega
      have hae := Finset.add_sum_erase (Finset.range i) (fun a => a !) h0
      rw [herase] at hae
      simpa using hae
    have hr := sum_range_factorial_le i
    have hpos : 1 ≤ i ! := Nat.factorial_pos i
    omega

/-- **The digits of a sum of distinct factorials are its indicators.** For `T` a finite set of
positive integers, `d_i(∑_{a∈T} a!) = [i ∈ T] ∈ {0,1}`. (The "representable ⟹ all digits ≤ 1"
direction, with the exact value.) -/
theorem factDigit_sum_factorial (T : Finset ℕ) (hT : ∀ a ∈ T, 1 ≤ a) {i : ℕ} (hi : 1 ≤ i) :
    factDigit i (∑ a ∈ T, a !) = if i ∈ T then 1 else 0 := by
  classical
  set e : ℕ := if i ∈ T then 1 else 0 with he
  -- set equalities used to refold the trichotomy filters
  have hset1 : (T.filter (¬ · < i)).filter (· = i) = T.filter (· = i) := by
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, _⟩, hq⟩; exact ⟨hx, hq⟩
    · rintro ⟨hx, hq⟩; exact ⟨⟨hx, by omega⟩, hq⟩
  have hset2 : (T.filter (¬ · < i)).filter (¬ · = i) = T.filter (i < ·) := by
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, hp⟩, hq⟩; exact ⟨hx, by omega⟩
    · rintro ⟨hx, hr⟩; exact ⟨⟨hx, by omega⟩, by omega⟩
  have hEi : ∑ a ∈ T.filter (· = i), a ! = e * i ! := by
    rw [Finset.filter_eq', he]; split_ifs <;> simp
  -- decompose the sum as  (∑_{<i}) + (e·i! + ∑_{>i})
  have hpart : ∑ a ∈ T, a !
      = (∑ a ∈ T.filter (· < i), a !) + (e * i ! + ∑ a ∈ T.filter (i < ·), a !) := by
    rw [← Finset.sum_filter_add_sum_filter_not T (· < i) (fun a => a !)]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (T.filter (¬ · < i)) (· = i) (fun a => a !),
      hset1, hset2, hEi]
  -- divisibility of the high part
  have hCdvd : (i + 1)! ∣ ∑ a ∈ T.filter (i < ·), a ! := by
    refine Finset.dvd_sum (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    exact Nat.factorial_dvd_factorial (by omega)
  obtain ⟨j, hj⟩ := hCdvd
  have hlow : ∑ a ∈ T.filter (· < i), a ! < i ! := sum_lt_factorial_of_lt T hT i
  -- ∑_T = (∑_{<i}) + i!·(e + (i+1)·j),  with ∑_{<i} < i!
  have hn : ∑ a ∈ T, a ! = (∑ a ∈ T.filter (· < i), a !) + i ! * (e + (i + 1) * j) := by
    rw [hpart, hj, Nat.factorial_succ]; ring
  have hdiv : (∑ a ∈ T, a !) / i ! = e + (i + 1) * j := by
    rw [hn, Nat.add_mul_div_left _ _ (Nat.factorial_pos i), Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [factDigit, hdiv]
  have hemod : e < i + 1 := by rw [he]; split_ifs <;> omega
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hemod]

/-- A sum of distinct factorials (positive indices) has all digits `≤ 1`. -/
theorem factDigit_factSum_le_one (T : Finset ℕ) (hT : ∀ a ∈ T, 1 ≤ a) {i : ℕ} (hi : 1 ≤ i) :
    factDigit i (∑ a ∈ T, a !) ≤ 1 := by
  rw [factDigit_sum_factorial T hT hi]; split_ifs <;> omega

/-- **The `0!` bridge.** Since `0! = 1!`, allowing index `0` adds at most one unit. So if `n` is a
sum of distinct factorials (`n = factSum S`, indices `≥ 0`), then *either* `n` *or* `n - 1` has all
factorial digits `≤ 1` (the latter when `0 ∈ S`, peeling `0! = 1`). -/
theorem factSum_digit_dichotomy (S : Finset ℕ) {n : ℕ} (hn : factSum S = n) :
    (∀ i, 1 ≤ i → factDigit i n ≤ 1) ∨ (∀ i, 1 ≤ i → factDigit i (n - 1) ≤ 1) := by
  rw [factSum] at hn
  by_cases h0 : 0 ∈ S
  · right
    intro i hi
    have hpos : ∀ a ∈ S.erase 0, 1 ≤ a := by
      intro a ha; rw [Finset.mem_erase] at ha; omega
    have heq : ∑ a ∈ S.erase 0, a ! = n - 1 := by
      have hae := Finset.add_sum_erase S (fun a => a !) h0
      simp only [Nat.factorial_zero] at hae
      omega
    rw [← heq]; exact factDigit_factSum_le_one _ hpos hi
  · left
    intro i hi
    have hpos : ∀ a ∈ S, 1 ≤ a := by
      intro a ha
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exact absurd ha h0
      · exact h
    rw [← hn]; exact factDigit_factSum_le_one _ hpos hi

/-- **Non-representability criterion.** If *both* `n` and `n - 1` carry a factorial digit `≥ 2`
(at a positive index), then `n` is not a sum of distinct factorials: no `S` has `factSum S = n`.
This is the interface the sharp endgame calls on `n = 2^m`. -/
theorem not_factSum_of_digits (n : ℕ)
    (h1 : ∃ i, 1 ≤ i ∧ 2 ≤ factDigit i n)
    (h2 : ∃ i, 1 ≤ i ∧ 2 ≤ factDigit i (n - 1)) :
    ∀ S : Finset ℕ, factSum S ≠ n := by
  intro S hS
  rcases factSum_digit_dichotomy S hS with h | h
  · obtain ⟨i, hi, hd⟩ := h1; have := h i hi; omega
  · obtain ⟨i, hi, hd⟩ := h2; have := h i hi; omega

end Erdos403
