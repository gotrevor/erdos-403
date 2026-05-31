# Erdős #403 — plan of attack (multi-session)

Goal: discharge the two remaining sorries — `tied_carry_ceiling` (the bound) and `erdos_403_sharp`
(`m ≤ 7`) — and thereby `erdos_403_finite` unconditionally. Trevor green-lit the full grind
(items **1 = the bound** and **2 = the sharp endgame**), multiple sessions OK.

## The reframing that reshapes everything (session 3)

Both remaining goals collapse to **one** question about the *factorial number system* (FNS):

> The unique factorial-base digits of `n` are `d_i(n) = (n / i!) mod (i+1)` (`0 ≤ d_i ≤ i`),
> with `n = ∑_{i≥1} d_i(n)·i!`.
> `n` is a **sum of distinct factorials, indices ≥ 1** ⟺ `∀ i, d_i(n) ≤ 1`.

Allowing index `0` (`0! = 1! = 1`) adds exactly one optional unit, and `0!+1! = 2!` lets that unit
"carry". Net effect (proved by case-chase on the bottom):

> `n` is a sum of distinct factorials (indices ≥ 0) ⟺ `(∀ i≥2, d_i(n) ≤ 1)` **or** `(∀ i≥2, d_i(n-1) ≤ 1)`.
> (`d_1` is always `≤ 1` — radix 2 — so only `i ≥ 2` digits bind.)

So **`erdos_403_sharp` becomes: for `m ≥ 8`, both `2^m` and `2^m − 1` have a factorial digit `≥ 2`
at some index `≥ 2`.** And `erdos_403_finite` follows from *any* bound on `m`.

### What this buys us — verified against the enumeration (session 3)
Computed `d_2, d_3` of `2^m` and `2^m − 1` (and the leading digit) for `m = 1..15`:

- **Even `m ≥ 4`: FULLY killed (Phase B done).** `2^m ≡ 16 (mod 24)` ⟹ `d_3(2^m) = 2` **and**
  `d_3(2^m − 1) = 2`. `3! = 6` has no factorial degeneracy, so the `0!` carry rescues neither branch.
  `not_factSum_of_digits` ⇒ `factSum_ne_of_even`.
- **Odd `m`: small digits are useless.** For odd `m`, `d_2 = d_3 = ≤1` on *both* `2^m` and `2^m − 1`
  (`d_2(2^m)=1, d_3(2^m)=1, d_2(2^m−1)=0, d_3(2^m−1)=1`). (My earlier note that odd `m` loses a
  branch to `d_3` was WRONG — corrected here.) So odd `m` needs a *higher* digit `≥ 2` in **both**
  numbers (the full `not_factSum_of_digits`).

### The residual kernel — odd `m ≥ 9` (genuinely Lin)
Two regimes (by the leading digit `d_M = ⌊2^m/M!⌋`, `M` = largest factorial index `≤ 2^m`):
- **Leading digit `≥ 2`** (i.e. `2^m ≥ 2·M!`): branch 1 dies by the leading digit; `2^m − 1` then
  also has leading digit `≥ 2` (unless `2^m = 2M!`, tiny). **Provable sub-case** via the size
  sandwich + a "leading digit" FNS lemma. Kills e.g. `m = 9, 11, 15`.
- **Leading digit `= 1`** (`2^m ∈ [M!, 2M!)`, the size sandwich): need a **middle** digit `≥ 2`.
  This is the irreducible cascade (e.g. `m = 13`: leading digit 1, but `d_6(2^13) = 4`). **The hard
  core**, no `0!` wrinkle, no tied/untied split — just "some middle digit of `2^m` is `≥ 2`."

## Architecture / file layout

- `Erdos403/Basic.lean` — current: sandwich, Legendre, unique-min half, ties, `min'_le_two`,
  finiteness assembly (modulo `tied_carry_ceiling`). Keep.
- `Erdos403/FactBase.lean` — **new**: factorial number system. `factDigit`, reconstruction
  `n = ∑ d_i·i!`, the `≤1` ⇔ distinct-factorials criterion, the `0!` (`n`-or-`n−1`) bridge,
  decidability. This is item 2's foundation and also the language for item 1.
- `Erdos403/Sharp.lean` — **new, later**: the digit facts about `2^m` (even/odd kills), the residual
  middle-digit lemma (item 1), and the `decide` over small `m` ⇒ `erdos_403_sharp`.

## Ordered steps

### Phase A — FNS infrastructure (item 2 foundation) — START HERE
1. `factDigit (i n) := (n / i !) % (i+1)`. Basic lemmas: `factDigit i n ≤ i`.
2. **Reconstruction**: `n = ∑_{i ∈ Ico 1 (B+1)} factDigit i n · i!` for `B` with `n < (B+1)!`
   (induction; mirrors `Nat.digits`/`Nat.ofDigits`).
3. **Distinct-factorials criterion (idx ≥ 1)**: `(∃ T ⊆ Ico 1 (B+1), ∑_{a∈T} a! = n) ↔ ∀ i, factDigit i n ≤ 1`.
   Forward: greedy is forced (`∑_{a<M} a! < M!`). Backward: `T = {i | d_i = 1}`.
4. **`0!` bridge**: relate `factSum (S : Finset ℕ)` (indices ≥ 0, our def) to the idx-≥1 criterion via
   the `n`-or-`n−1` statement. Handle `0!=1!` collision cleanly.
5. **Decidability**: `Decidable (∃ S, factSum S = n)` via the digit test, so `decide`/`native_decide`
   can settle specific `n = 2^m`.

### Phase B — the even/odd modular kills (item 1, easy half)
6. `d_2`, `d_3` lemmas for `2^m` and `2^m−1` (the mod-12 facts above), reducing each parity class to a
   single one-number all-digits-≤1 test. (`decide`-friendly small modular computations.)

### Phase C — the residual, odd `m ≥ 9` (item 1)
7a. **Leading-digit FNS lemma + sub-case (provable).** Prove `factDigit M n = ⌊n/M!⌋` for `M` the
    top index with `n < (M+1)!`, and `factDigit M n ≥ 2 ↔ 2·M! ≤ n`. Then odd `m` with `2^m ≥ 2·M!`
    is killed (leading digit `≥ 2` in `2^m` and `2^m − 1`). Bank this first.
7b. **Middle-digit hard core (Lin).** Remaining: odd `m ≥ 9` with `2^m ∈ [M!, 2M!)`. Show some
    middle `d_i ≥ 2`. The ~50% multi-session nut. Sub-approaches: (a) strong induction tracking the
    residual `2^k − const` shape; (b) bound consecutive tied levels via the exact-value constraint;
    (c) a size+digit argument special to the leading-digit-1 regime.

    **Session-4 brute-force recon (`m = 9..63`, trust it):** lower-half odd cases are sparse
    (`m = 13,19,29,33,37,41,…`). Two hard facts that reshape the attack:
    - **No fixed witness digit.** The index of the first `d_i ≥ 2` wanders with `m`
      ({5,6} at 13, {8} at 19, {7,8,9,10} at 29, {5,8,10,11,12} at 33). `d_{M-1} ≥ 2` *fails*
      (m=29). So the even-`m` trick (a periodic modular digit) **cannot** work here — 7b must be a
      *counting / valuation contradiction*: assume **all** digits `≤ 1` and derive `2^m` is
      unrepresentable, not "exhibit digit `i`".
    - **`2^m` and `2^m−1` agree on all digits at index `≥ 5`.** (The `−1` borrow only churns the
      bottom — `2^m` is even, trailing FNS zeros absorb the borrow below index 5.) ⟹ once a middle
      digit `≥ 2` is shown for `2^m`, the *same index* serves `2^m−1`, modulo a small
      "borrow-doesn't-reach-index-`i`" lemma. **Halves `not_factSum_of_digits`'s two obligations.**
    - **Why it's genuinely Lin (the cancellation trap):** the *small* solutions live on even-`K`
      2-adic cancellation — `2^5 = 2!+3!+4!` has `v₂(2!) = v₂(3!) = 1`, an even tie that *lifts*
      `v₂` of the partial sum (`2!+3! = 8`). So the naive "smallest index `i₀ ∈ S` ⟹
      `v₂(sum) = v₂(i₀!) ≈ i₀ < m`, contradiction" argument **breaks** exactly when the minimal
      `v₂(i!)` level has an even number of occupants. A real 7b proof must bound how much cancellation
      the all-digits-≤1 constraint permits (`v₂(i!) = v₂((i-1)!)` iff `i` even — tie structure is
      explicit). This is the kernel; ~50%, multi-session. Lead approach: track the minimal-`v₂`
      level and its parity under the digit constraint, not strong induction on `2^k − const`.

### Phase D — assembly
8. `erdos_403_sharp`: combine B + C to get a bound, then `decide` the finitely many `m ≤ B` ⇒ `m ≤ 7`.
9. Re-route `erdos_403_finite` through `erdos_403_sharp` (drop the `tied_carry_ceiling` dependency):
   `m ≤ 7 ⇒ factSum ≤ 128 ⇒ M ≤ 5`, finite. Delete/retire `tied_carry_ceiling`.

## Status ledger
- [x] A1 factDigit + bound — `factDigit`, `factDigit_le`
- [x] A2 reconstruction — `factDigit_recon` (telescoping), `factDigit_sum`
- [x] A3 distinct-factorials criterion (idx ≥ 1) — `factDigit_sum_factorial` (digits = indicators),
      `factDigit_factSum_le_one`
- [x] A4 `0!` bridge — `factSum_digit_dichotomy`, packaged as `not_factSum_of_digits`
- [~] A5 decidability — subsumed: `not_factSum_of_digits` is the interface (no full `Decidable` needed)
- [x] B6 even `m` — **fully killed** (`factSum_ne_of_even`): `2^m ≡ 16 (mod 24)` ⟹ `d_3 = 2` for
      *both* `2^m` and `2^m − 1`, so `not_factSum_of_digits` fires. (Odd `m` keeps `d_3 = 1`; residual.)
- [x] C7a leading-digit kill — `factSum_ne_of_leading_two` (Sharp.lean): odd `m` with
      `2·M! < 2^m < (M+1)!` dies (both top digits `≥ 2`). Axiom-clean. **Banked (session 4).**
- [ ] C7b residual nut: **odd `m ≥ 9` with `2^m ∈ [M!, 2M!)`** — a *middle* digit `≥ 2` (the hard kernel)
- [x] D8 sharp assembly — `erdos_403_sharp` (`m ≤ 7`) **proven modulo the kernel** (session 4), via
      `sharp_of_unique_min` (`m≤3`) + `tied_sharp_ceiling` + `four_two_pow_lt_factorial`. No
      factorial-base/`decide` needed.
- [x] D9 unify kernels — `erdos_403_finite` **and** `erdos_403_sharp` now both reduce to the **single**
      `tied_sharp_ceiling` sorry (`B=2` explicit). `tied_carry_ceiling` proven from it. **Sorries 2→1.**

**Note (session 4):** the Basic.lean *valuation* track (above) is the one carrying finiteness + sharp
(1 sorry). The Sharp.lean *FNS* track (even-`m` kill, C-7a) is a parallel alternative whose residual
C-7b is the *same* kernel (`tied_sharp_ceiling`); keep C-7a as a clean standalone but the live target
is the single kernel.

**Phase A done (session 3), all axiom-clean.** The endgame now only needs, for each `m ≥ 8`, a
positive-index factorial digit `≥ 2` in *both* `2^m` and `2^m − 1` (→ `not_factSum_of_digits`).

## ⚠️ Session-4 reconciliation: the two tracks share one kernel

A deep read of `Basic.lean` (the sessions 1-2 valuation track) reshapes the strategy. **`Basic.lean`
already proves everything except a single `sorry`:**
- `v2_factSum_of_unique_min` + `m_le_max_of_unique_min`: the **unique-min case is fully closed**
  (`v₂(factSum S) = v₂(a₀!) ≤ a₀ ≤ M`, axiom-clean). This is exactly the "no-cancellation kill."
- `min'_le_two`: every solution has `min' S ∈ {0,1,2}` (else `3 ∣ 2^m`).
- `erdos_403_finite` is **proven modulo the lone `tied_carry_ceiling` sorry** (the bounded-carry
  estimate for the *tied-pair* bottom case).

**The FNS track (`Sharp.lean`) and `tied_carry_ceiling` bottom out at the SAME kernel.** The
session-3 hope that FNS would "supersede / retire `tied_carry_ceiling`" was over-optimistic:
- FNS Phase B (even `m`) + C-7a (upper-half odd `m`) kill their cases via a **fixed digit** — those
  were *never* the kernel (they're the unique-min-ish / leading-digit cases).
- FNS C-7b (lower-half odd `m`, leading digit 1) **is** the tied-pair bounded-carry kernel in
  disguise. No free lunch. So C-7b is not an easier path around `tied_carry_ceiling`; pursue the
  kernel **once**, in whichever framing is cleaner.

**Sharpened kernel (the real handle, session-4 brute-force + min'_le_two):** every `m ≥ 2` solution
has a representation whose **bottom pair is exactly `{2,3}`** (the `0!=1!` twin maps
`[0,1,…] ↔ [2,…]`; e.g. `2^7`: `[0,1,3,5] ↔ [2,3,5]`). So WLOG the tied bottom is `{2,3}`,
contributing `2!+3! = 8 = 2³`. The cascade is **self-similar** — each `v₂`-level is a pair
`{2j,2j+1}`, and `8` carries up exactly when the next occupied level already holds a factorial
(witness: `{2,3}→8` at `v₂=3`, meets `5!=120` at `v₂=3`, `8+120=128=2⁷`). The kernel is: *bound how
far this carry chains.* Empirically `m − max' S ≤ 2`, so `tied_carry_ceiling` holds with `B = 2`.
This lone bound is the **unpublished Lin/Frankl estimate** — genuinely hard, multi-session, no clean
one-lemma proof found. **Recommendation:** discharge `tied_carry_ceiling` directly in `Basic.lean`
(bottom now pinned to `{2,3}` — a cleaner framing than session-3 had), or bank
finiteness-modulo-Lin + sharp-modulo-Lin as the honest deliverable. The FNS kills remain valuable:
they narrow `tied_carry_ceiling`'s residual scope to "tied ∧ lower-half-odd."

## The kernel, in its cleanest form (session-4 quantitative)

The whole problem reduces to **one absolute-constant carry bound**:
> **`carry_gap`**: `∃ B, ∀ S nonempty, v₂(factSum S) ≤ max' S + B`.

This *immediately* gives `carry_ceiling` (`factSum S = 2^m ⟹ m = v₂(2^m) = v₂(factSum S) ≤ max'S+B`)
— no tied/unique-min split, no powers of two. So `carry_gap` ⟹ `erdos_403_finite`.

**Quantitative evidence** (exhaustive over tied-bottom `S ⊆ {0..K}`):
- general gap `v₂(factSum S) − max'S`: **plateaus at 4** for `K = 9..16` (extremal `{6,7,9}`:
  `6!+7!+9! = 2¹³·45`, `max=9`). So `carry_gap` holds with **`B = 4`** (conjectured absolute).
- restricted to *power-of-two* factSums: gap **≤ 2** (only `m ∈ {0,1,2,3,5,7}`; extremal `{2,3,5}→2⁷`,
  `max=5`). With `min'_le_two`, those have bottom pinned to `{2,3}` (or `{0,1}` twin).

**Why `B` is bounded — the skipped-level mechanism (the proof intuition):** `v₂(i!)` takes each value
on a pair `{2j,2j+1}` and *skips* values between pairs (`…,8,8,10,10,11,11,15,15,…` — no `9`, no
`12,13,14`). A bottom pair carries up to a level; it can carry *again* only if that level already
holds a factorial; but most levels are skipped, so the chain stalls fast. This is the heart of the
unpublished Lin/Frankl estimate.

**Why there's no cheap proof:** the only free bound is `v₂(factSum S) ≤ log₂(factSum S) ≈ M log M`
(the sandwich gives `factSum S < 2·M!`), which is *far* above `M + B`. Closing the gap to an absolute
constant genuinely needs the cascade analysis above — confirmed by independently re-deriving the
valuation framework (session 4) and the prior sessions' `Basic.lean`. **Recommended attack:** prove
`carry_gap` by tracking the carry level-by-level using the pair structure (`v2_factorial_*` lemmas in
`Basic.lean`), exploiting that occupied levels are sparse. Multi-session; a clean target for an
automated prover (Aristotle) since it's pure `ℕ` number theory with no powers of two.

## Confidence
A: ~85% (standard, just laborious). B: ~80% (modular, but FNS-digit-of-`2^m` lemmas need care).
C: ~50% (the real Lin kernel, now better-scoped). D: ~90% once A–C land.
Net "fully sorry-free #403": ~45%, but every phase is independently valuable and verifiable.
