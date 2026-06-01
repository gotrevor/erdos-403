import Mathlib
import Erdos403.Basic
import Erdos403.FactBase

/-!
# Erdős #403 — the sharp bound `m ≤ 7` (Phases B–D)

Using the factorial number system (`FactBase`), `factSum S = 2^m` is impossible once `2^m` and
`2^m − 1` both carry a factorial digit `≥ 2` (`not_factSum_of_digits`).

* **Phase B (this file, done):** `m` even `≥ 4` is killed cleanly — `2^m ≡ 16 (mod 24)` forces the
  `3!`-digit of *both* `2^m` and `2^m − 1` to be `2` (and `3! = 6` has no factorial degeneracy, so
  the `0!` carry cannot fix it).
* **Phase C (todo):** `m` odd `≥ 9` — the residual Lin kernel (a middle digit `≥ 2`).
* **Phase D (todo):** assemble `erdos_403_sharp` (`decide` the small `m`).
-/

namespace Erdos403

open scoped Nat

/-- `2^(2t+4) ≡ 16 (mod 24)` — the period-2 cycle `…,16,8,16,8,…` of `2^m mod 24` (`m ≥ 3`),
on the even branch. -/
theorem two_pow_mod_24_even : ∀ t, 2 ^ (2 * t + 4) % 24 = 16 := by
  intro t
  induction t with
  | zero => decide
  | succ k ih =>
    have he : 2 * (k + 1) + 4 = (2 * k + 4) + 2 := by ring
    rw [he, pow_add, Nat.mul_mod, ih]
    decide

/-- `2^m ≡ 16 (mod 24)` for even `m ≥ 4`. -/
theorem two_pow_mod_24_of_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) : 2 ^ m % 24 = 16 := by
  obtain ⟨r, rfl⟩ := he
  have hrw : r + r = 2 * (r - 2) + 4 := by omega
  rw [hrw]; exact two_pow_mod_24_even (r - 2)

/-- For even `m ≥ 4`, the `3!`-digit of `2^m` is `2`. -/
theorem factDigit_three_two_pow_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) :
    factDigit 3 (2 ^ m) = 2 := by
  have h := two_pow_mod_24_of_even he hm
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = 24 * q + 16 := ⟨2 ^ m / 24, by omega⟩
  show (2 ^ m / 6) % 4 = 2
  rw [hq]; omega

/-- For even `m ≥ 4`, the `3!`-digit of `2^m − 1` is also `2` (so the `0!` carry can't rescue it). -/
theorem factDigit_three_two_pow_sub_one_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) :
    factDigit 3 (2 ^ m - 1) = 2 := by
  have h := two_pow_mod_24_of_even he hm
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = 24 * q + 16 := ⟨2 ^ m / 24, by omega⟩
  show ((2 ^ m - 1) / 6) % 4 = 2
  rw [hq]; omega

/-- **Phase B result.** No sum of distinct factorials equals `2^m` for even `m ≥ 4`. -/
theorem factSum_ne_of_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) (S : Finset ℕ) :
    factSum S ≠ 2 ^ m := by
  refine not_factSum_of_digits (2 ^ m) ⟨3, by omega, ?_⟩ ⟨3, by omega, ?_⟩ S
  · rw [factDigit_three_two_pow_even he hm]
  · rw [factDigit_three_two_pow_sub_one_even he hm]

/-- **Phase C-7a (leading-digit kill).** If `2·M! < 2^m < (M+1)!` — i.e. `2^m` reaches *twice* its
leading factorial `M!` without spilling into the next — then the top factorial digit of *both*
`2^m` and `2^m − 1` is `≥ 2` (`2^m − 1` shares the same leading index and still clears `2·M!`,
strictly, since `2^m` is a power of two). So `not_factSum_of_digits` fires. This bankable sub-case
kills every odd `m ≥ 9` whose `2^m` lands in the upper half `[2·M!, (M+1)!)`; the residual nut is
the lower half `[M!, 2·M!)`. -/
theorem factSum_ne_of_leading_two {m M : ℕ} (hM : 2 ^ m < (M + 1)!) (h2 : 2 * M ! < 2 ^ m)
    (S : Finset ℕ) : factSum S ≠ 2 ^ m := by
  -- `2·M! < 2^m < (M+1)! = (M+1)·M!` forces `M ≥ 2`, so `M` is a valid positive digit index.
  have hM1 : 1 ≤ M := by
    by_contra h
    have hle : (M + 1)! ≤ 2 * M ! := by
      interval_cases M
      decide
    omega
  refine not_factSum_of_digits (2 ^ m) ⟨M, hM1, ?_⟩ ⟨M, hM1, ?_⟩ S
  · exact two_le_factDigit_top hM (by omega)
  · exact two_le_factDigit_top (by omega) (by omega)

/-! ## Phase C — odd `m ≥ 9` killed by a FIXED modulus (`12!`)

Direct computation (verified three ways) shows the factorial-base expansion of `2^m` **and** of
`2^m - 1` carries a digit `≥ 2` at some index `≤ 11` for *every* `m ≥ 8`. Equivalently, a single
fixed modulus `12!` closes Erdős #403. The earlier belief that "no fixed modulus works" was a
heuristic extrapolation — the smallest offending index climbs `5 → 7 → 8 → 11` and was *assumed*
to grow without bound; in fact it caps at `11`.

Mechanism: `factDigit i n` depends only on `n mod (i+1)!`, hence for `i ≤ 11` only on `n mod 12!`;
and `2^m mod 12!` is periodic in `m` with period `1620` (`ord_{467775}(2) = 1620`, where
`12! = 1024 · 467775`). So the claim reduces to a finite `native_decide` over one period. -/

/-- `factDigit i n` depends only on `n` modulo `(i+1)!`. -/
theorem factDigit_mod (i n : ℕ) : factDigit i n = factDigit i (n % (i + 1)!) := by
  unfold factDigit
  set q := n / (i + 1)! with hq
  set r := n % (i + 1)! with hr
  have hn : n = (i + 1)! * q + r := by rw [hq, hr, Nat.div_add_mod]
  have hsplit : n / i ! = (i + 1) * q + r / i ! := by
    conv_lhs => rw [hn, Nat.factorial_succ]
    rw [show (i + 1) * i ! * q = i ! * ((i + 1) * q) by ring, Nat.mul_add_div (Nat.factorial_pos i)]
  rw [hsplit, add_comm, Nat.add_mul_mod_self_left]

/-- For `i ≤ 11`, `factDigit i n` depends only on `n` modulo `12!`. -/
theorem factDigit_mod_twelve {i : ℕ} (hi : i ≤ 11) (n : ℕ) :
    factDigit i n = factDigit i (n % (12)!) := by
  have hdvd : ((i + 1)! : ℕ) ∣ (12)! := Nat.factorial_dvd_factorial (by omega)
  rw [factDigit_mod i n, factDigit_mod i (n % (12)!), Nat.mod_mod_of_dvd n hdvd]

/-- `2^1620 ≡ 1 (mod 467775)`, proved **kernel-pure via CRT** (no `native_decide`).
`467775 = 3^5 · 5^2 · 7 · 11 = 243 · 25 · 7 · 11` (pairwise coprime); `ord(2)` modulo each
prime power is `162, 20, 3, 10`, each dividing `1620`. The four small `decide`s are kernel
computations; the combine is `Nat.modEq_and_modEq_iff_modEq_mul`. -/
private theorem two_pow_1620_odd : (2 : ℕ) ^ 1620 % 467775 = 1 := by
  have h243 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243] := by
    have b : (2 : ℕ) ^ 162 ≡ 1 [MOD 243] := by decide
    calc (2 : ℕ) ^ 1620 = (2 ^ 162) ^ 10 := by rw [← pow_mul]
      _ ≡ 1 ^ 10 [MOD 243] := b.pow 10
      _ = 1 := one_pow 10
  have h25 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 25] := by
    have b : (2 : ℕ) ^ 20 ≡ 1 [MOD 25] := by decide
    calc (2 : ℕ) ^ 1620 = (2 ^ 20) ^ 81 := by rw [← pow_mul]
      _ ≡ 1 ^ 81 [MOD 25] := b.pow 81
      _ = 1 := one_pow 81
  have h7 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 7] := by
    have b : (2 : ℕ) ^ 3 ≡ 1 [MOD 7] := by decide
    calc (2 : ℕ) ^ 1620 = (2 ^ 3) ^ 540 := by rw [← pow_mul]
      _ ≡ 1 ^ 540 [MOD 7] := b.pow 540
      _ = 1 := one_pow 540
  have h11 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 11] := by
    have b : (2 : ℕ) ^ 10 ≡ 1 [MOD 11] := by decide
    calc (2 : ℕ) ^ 1620 = (2 ^ 10) ^ 162 := by rw [← pow_mul]
      _ ≡ 1 ^ 162 [MOD 11] := b.pow 162
      _ = 1 := one_pow 162
  have c1 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243 * 25] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨h243, h25⟩
  have c2 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243 * 25 * 7] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨c1, h7⟩
  have c3 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243 * 25 * 7 * 11] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨c2, h11⟩
  rw [show (243 * 25 * 7 * 11 : ℕ) = 467775 by norm_num] at c3
  -- `c3 : 2^1620 % 467775 = 1 % 467775`; `1 % 467775` is defeq `1`.
  exact c3

/-- `2^(10+k) mod 12! = 1024 · (2^k mod 467775)` (since `12! = 1024 · 467775`). -/
private theorem two_pow_split (k : ℕ) : (2 : ℕ) ^ (10 + k) % (12)! = 1024 * (2 ^ k % 467775) := by
  have h12 : ((12)! : ℕ) = 1024 * 467775 := by decide
  rw [h12, pow_add, show (2 : ℕ) ^ 10 = 1024 by norm_num, Nat.mul_mod_mul_left]

/-- `2^m mod 12!` has period `1620` (on the `+10`-shifted exponent). -/
private theorem two_pow_period (k : ℕ) :
    (2 : ℕ) ^ (10 + (k + 1620)) % (12)! = (2 : ℕ) ^ (10 + k) % (12)! := by
  have hinner : (2 : ℕ) ^ (k + 1620) % 467775 = 2 ^ k % 467775 := by
    rw [pow_add, Nat.mul_mod, two_pow_1620_odd, mul_one]
    omega
  rw [two_pow_split (k + 1620), two_pow_split k, hinner]

/-- Drop full periods: `2^(10 + (1620·j + k)) ≡ 2^(10+k)  (mod 12!)`. -/
private theorem two_pow_drop (j k : ℕ) :
    (2 : ℕ) ^ (10 + (1620 * j + k)) % (12)! = (2 : ℕ) ^ (10 + k) % (12)! := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [show 1620 * (n + 1) + k = (1620 * n + k) + 1620 by ring,
        two_pow_period (1620 * n + k), ih]

/-- Reduce any `m ≥ 10` to the base window `[10, 1630)` modulo `12!`. -/
private theorem two_pow_reduce {m : ℕ} (hm : 10 ≤ m) :
    (2 : ℕ) ^ m % (12)! = (2 : ℕ) ^ (10 + (m - 10) % 1620) % (12)! := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 10 + k := ⟨m - 10, by omega⟩
  conv_lhs => rw [show k = 1620 * (k / 1620) + k % 1620 from (Nat.div_add_mod k 1620).symm]
  rw [two_pow_drop]
  have : (10 + k - 10) % 1620 = k % 1620 := by omega
  rw [this]

-- Base window (one full period): every `m ∈ [10, 1630)` has an offending factorial digit of
-- `2^m` (resp. `2^m - 1`) at an index in `[1, 11]`. Verified by `native_decide`.
set_option maxRecDepth 8000 in
private theorem base_offending :
    ∀ m ∈ Finset.Ico 10 1630, ∃ i ∈ Finset.Icc 1 11, 2 ≤ factDigit i (2 ^ m) := by
  native_decide

set_option maxRecDepth 8000 in
private theorem base_offending_sub :
    ∀ m ∈ Finset.Ico 10 1630, ∃ i ∈ Finset.Icc 1 11, 2 ≤ factDigit i (2 ^ m - 1) := by
  native_decide

/-- **Fixed-modulus kill (heart of Phase C).** For every `m ≥ 8`, `2^m` carries a factorial-base
digit `≥ 2` at some positive index — so `2^m` is not a sum of distinct factorials. -/
theorem two_pow_offending {m : ℕ} (hm : 8 ≤ m) : ∃ i, 1 ≤ i ∧ 2 ≤ factDigit i (2 ^ m) := by
  rcases Nat.lt_or_ge m 10 with h9 | h10
  · interval_cases m
    · exact ⟨2, by norm_num, by decide⟩
    · exact ⟨5, by norm_num, by decide⟩
  · obtain ⟨i, hi_mem, hi_d⟩ :=
      base_offending (10 + (m - 10) % 1620)
        (Finset.mem_Ico.mpr ⟨by omega,
          by have := Nat.mod_lt (m - 10) (show 0 < 1620 by norm_num); omega⟩)
    rw [Finset.mem_Icc] at hi_mem
    refine ⟨i, hi_mem.1, ?_⟩
    rwa [factDigit_mod_twelve hi_mem.2 (2 ^ m), two_pow_reduce h10,
        ← factDigit_mod_twelve hi_mem.2 (2 ^ (10 + (m - 10) % 1620))]

/-- The `2^m - 1` companion of `two_pow_offending`. -/
theorem two_pow_sub_one_offending {m : ℕ} (hm : 8 ≤ m) :
    ∃ i, 1 ≤ i ∧ 2 ≤ factDigit i (2 ^ m - 1) := by
  rcases Nat.lt_or_ge m 10 with h9 | h10
  · interval_cases m
    · exact ⟨3, by norm_num, by decide⟩
    · exact ⟨5, by norm_num, by decide⟩
  · obtain ⟨i, hi_mem, hi_d⟩ :=
      base_offending_sub (10 + (m - 10) % 1620)
        (Finset.mem_Ico.mpr ⟨by omega,
          by have := Nat.mod_lt (m - 10) (show 0 < 1620 by norm_num); omega⟩)
    rw [Finset.mem_Icc] at hi_mem
    refine ⟨i, hi_mem.1, ?_⟩
    have key : (2 ^ m - 1) % (12)! = (2 ^ (10 + (m - 10) % 1620) - 1) % (12)! := by
      have hbase := two_pow_reduce h10
      have hNval : ((12)! : ℕ) = 479001600 := by decide
      have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hr1 : 1 ≤ 2 ^ (10 + (m - 10) % 1620) := Nat.one_le_two_pow
      rw [hNval] at hbase ⊢
      omega
    rwa [factDigit_mod_twelve hi_mem.2 (2 ^ m - 1), key,
        ← factDigit_mod_twelve hi_mem.2 (2 ^ (10 + (m - 10) % 1620) - 1)]

/-- **Phase C complete.** No sum of distinct factorials equals `2^m` for `m ≥ 8`. -/
theorem factSum_ne_of_ge_eight {m : ℕ} (hm : 8 ≤ m) (S : Finset ℕ) : factSum S ≠ 2 ^ m :=
  not_factSum_of_digits (2 ^ m) (two_pow_offending hm) (two_pow_sub_one_offending hm) S

/-! ## The headline theorems (FNS route, fully sorry-free)

The fixed-modulus kill makes the entire 2-adic carry machinery (`cascade_*`, `tied_*`) unnecessary:
`factSum_ne_of_ge_eight` gives `m ≤ 7` directly, and finiteness follows from the size sandwich
`M! ≤ 2^m ≤ 2^7`. -/

/-- **Erdős #403 (sharp form)** — the largest power of two that is a sum of distinct factorials is
`2⁷ = 2! + 3! + 5! = 128`. Every solution has `m ≤ 7`. -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := by
  by_contra hc
  exact factSum_ne_of_ge_eight (by omega) S h

/-- **Erdős #403 (finiteness)** — exactly what the problem asks: only finitely many sums of
distinct factorials are powers of two. By `erdos_403_sharp`, every solution has `m ≤ 7`, so
`M! ≤ 2^m ≤ 128` forces `max' S ≤ 5`; hence every solution lives in `(range 6).powerset`. -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite := by
  apply Set.Finite.subset ((Finset.range 6).powerset : Finset (Finset ℕ)).finite_toSet
  intro S hS
  obtain ⟨m, hm⟩ := hS
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · rw [factSum, Finset.sum_empty] at hm
      exact absurd hm.symm (pow_ne_zero m two_ne_zero)
    · exact h
  have hm7 : m ≤ 7 := erdos_403_sharp hm
  have hfac : (S.max' hne)! ≤ 2 ^ m := by rw [← hm]; exact factorial_max_le_factSum hne
  have hMle : S.max' hne ≤ 5 := by
    by_contra hc
    have h6 : (6 : ℕ)! ≤ (S.max' hne)! := Nat.factorial_le (by omega)
    have h2 : (2 : ℕ) ^ m ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hm7
    rw [show (6 : ℕ)! = 720 by decide] at h6
    omega
  refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr (fun a ha => ?_))
  exact Finset.mem_range.mpr (by have := S.le_max' a ha; omega)

end Erdos403
