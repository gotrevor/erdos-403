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

## The kernel, in its cleanest form (session-4 quantitative) — ⚠️ PARTLY REFUTED (session 6)

The whole problem reduces to **one carry bound**:
> **`carry_gap`**: `∃ B, ∀ S nonempty, v₂(factSum S) ≤ max' S + B`.

This *immediately* gives `carry_ceiling` (`factSum S = 2^m ⟹ m = v₂(2^m) = v₂(factSum S) ≤ max'S+B`)
— no tied/unique-min split, no powers of two. So `carry_gap` ⟹ `erdos_403_finite`.

> ### ⚠️ Session-6 refutation: the UNCONDITIONAL `carry_gap` is FALSE.
> The session-4 "plateaus at 4, `B = 4` absolute" claim was a **small-`K` artifact**. The
> *unconditional* gap `v₂(factSum S) − max' S` is **UNBOUNDED**: the family `{2ᵗ−2, 2ᵗ−1, 2ᵗ+1}`
> gives gap `2t − 2` (verified: `t=3 {6,7,9}` gap 4, `t=4 {14,15,17}` gap 6, …, `t=8 {254,255,257}`
> gap 14). The brute force only *looked* flat because those witnesses have `max ≈ 2ᵗ`, off-screen for
> `K ≤ 12`. **Consequence:** the **power-of-two (odd-part-`1`) hypothesis is ESSENTIAL** — the gap is
> `≤ 2` *only* when `factSum S = 2^m` (the unbounded family has odd part ≠ 1). So:
> - The kernel CANNOT be the clean unconditional `carry_gap`. It must carry the `factSum = 2^m`
>   hypothesis (i.e. `cascade_two`'s exact shape). RECONSTRUCTION.md was correct all along.
> - The session-4 **Aristotle suggestion is void** for the unconditional version; any handoff must be
>   the *conditional* statement (odd-part-1 in the hypotheses), which is the harder, genuinely-Lin one.

**Why power-of-2 is the lever (the skipped-level mechanism, corrected):** `v₂(i!)` takes each value on
a pair `{2j,2j+1}` and *skips* between pairs (`…,8,8,10,10,11,11,15,15,…` — no `9,12,13,14`). A bottom
pair carries up only if the next occupied level already holds a factorial; but the *unbounded* family
shows occupied levels alone don't stall the chain — what stalls it is that the **odd part must be
exactly 1**, which the high triple `{2ᵗ−2,2ᵗ−1,2ᵗ+1}` violates. This is the heart of Lin's estimate.

## Confidence (updated session 6)
A: done. B: even-`m` done (now also as the in-`Basic` mod-6 reduction). C: ~45% (the real Lin kernel,
now scoped to **tied ∧ M≥6 ∧ odd `m`**, with the unconditional shortcut refuted). D: ~90% once C lands.
Net "fully sorry-free #403": ~40%; every phase independently valuable and verifiable.

---

# 📋 Session-6 forward plan — the odd-`m` kernel (current)

**Where we are.** `erdos_403_finite`/`_sharp` reduce to ONE `sorry`: `cascade_two`, branch
`min'=2 ∧ 3∈S ∧ 5∈S ∧ 4∉S ∧ M≥6`, and (session 6) **now also `Odd m`** — the even half is closed in
`Basic.lean` by a mod-6 argument (`factSum ≡ 2 mod 6 ⟹ 2^m ≡ 2 mod 6 ⟹ m odd`; helpers
`six_dvd_factorial`, `four_pow_mod_six`, axiom-clean). Goal of the branch: derive `False` (since
`m ≥ M+3` there, `m ≤ M+2` is vacuous).

**Two settled negatives (don't re-attempt — both verified this session):**
1. **No fixed modulus / finite digit-set closes odd `m`.** First FNS digit `≥2` wanders, index grows
   `~log m/log log m` (reaches 11 at `m=223`). Mod-bashing provably cannot finish. (Confirms handoff.)
2. **Size alone cannot finish.** The tight window `[M!, ∑_{a≤M}a!]` (mult-width `1+1/M`) kills most
   `M`, but a sparse infinite set survives (`M=63,64,90,161,255,256,…`, where `log₂ M!` is just above
   an integer). Those survivors have candidate `m ≈ 290 ≫ M+2`, so only the valuation bound `m≤M+2`
   kills them. ⟹ the valuation/carry argument is irreducible; no size shortcut.

**The one viable line: the conditional carry cascade (Lin), in `Basic.lean`.**
Target lemma (the whole kernel):
> `cascade_pow2`: `factSum S = 2^m ∧ min' S = 2 ∧ 3 ∈ S ⟹ m ≤ max' S + 2`.

Mechanism to formalize (the bottom-up parity cascade, odd-part-1 essential):
`2^m = 2!+3!+∑_{a≥4∈S}a! = 8 + ∑_{a≥4}a!` ⟹ `∑_{a≥4}a!/8 = 2^{m-3}−1` (odd). `a!/8` is odd iff
`a∈{4,5}` ⟹ parity pins exactly one of `{4,5}` in `S`, then recurse one level up with the target
valuation bumped. **Invariant to prove:** the carry can chain up to level `ℓ` only by occupying a
*pair* `{2j,2j+1}`, and the residual-odd constraint forces termination by `m ≤ M+2`.

### Staged milestones (each independently committable, build-green)
- **C-α (1 session): the `÷8` reduction lemma.** Formalize `factSum S = 8 + ∑_{a≥4∈S}a!` and
  `∑_{a≥4∈S} a!/8 = 2^{m-3} − 1` as a clean rewrite (needs `8 ∣ a!` for `a≥4`, have
  `eight_dvd_factorial`; and `8 ∤ (2!+3!)`-style accounting). Output: a `cascade_step` lemma turning
  the goal into "the reduced sum is `2^{m-3}−1`, odd."
- **C-β (1–2 sessions): the parity-pins-a-pair step.** Prove: given the reduced odd target, the next
  occupied indices are forced to be a consecutive pair `{2j,2j+1}` (or none), via `v₂(a!/8)` parity.
  This is the inductive step. Key sub-lemma: `v₂(a!)` is constant on `{2j,2j+1}` and strictly jumps
  across — already partly in `Basic.lean` (`v2_factorial_*`); `rg` them first (`read-repo-before-rederiving`).
- **C-γ (2–3 sessions, the nut): termination ⟹ `m ≤ M+2`.** Strong induction on `M − (current level)`:
  the cascade strips pairs upward; at the top pair (containing `M`) the residual-odd-`1` constraint
  has no room to carry further, capping the gap at 2. This is the genuinely-Lin step; budget 2–3
  sessions and expect dead ends. Fallback if stuck: prove the *weaker* `m ≤ M + C` for some explicit
  larger `C` (still gives finiteness via `exists_factorial_gt_two_pow`; sacrifices only sharp `m≤7`).
- **C-δ (assembly): wire `cascade_pow2` into `cascade_two`**, delete the `sorry`. `#print axioms`
  must drop `sorryAx`. Then `erdos_403_finite`/`_sharp` are unconditional.

### Alternative vehicle (parallel, lower priority): FNS doubling transducer
`2^m→2^{m+1}` is a carry transducer on factorial-base digits (`dᵢ' = (2dᵢ+c)mod(i+1)`, carry∈{0,1}).
Prove: all-digits-≤1 cannot recur for odd `m≥9`. Cleaner statement, but the growing radix `(i+1)`
makes the invariant harder to pin than the cascade; keep as a backup framing, not the lead.

### Aristotle (only if Trevor green-lights — currently a "no")
The *conditional* `cascade_pow2` (pure `ℕ`, with `factSum=2^m` in the hypotheses) is a well-posed,
isolated target once C-α/C-β land. NOT the unconditional `carry_gap` (refuted). Trevor's call.

### Sequencing & checkpoints
1. C-α next session (low-risk, banks a clean rewrite). 2. C-β (the pair-pinning induction). 3. C-γ
the nut. Checkpoint after C-β: if the pair-pinning induction is clean, confidence on C-γ rises; if it
fights `v₂` bookkeeping, consider the `m ≤ M+C` weaker fallback to at least close *finiteness*
unconditionally and leave only *sharp* `m≤7` open.
