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
- [ ] C7 residual: **odd `m ≥ 9`** — a middle digit `≥ 2` (the hard kernel)
- [ ] D8 sharp assembly
- [ ] D9 reroute finite, retire `tied_carry_ceiling`

**Phase A done (session 3), all axiom-clean.** The endgame now only needs, for each `m ≥ 8`, a
positive-index factorial digit `≥ 2` in *both* `2^m` and `2^m − 1` (→ `not_factSum_of_digits`).

## Confidence
A: ~85% (standard, just laborious). B: ~80% (modular, but FNS-digit-of-`2^m` lemmas need care).
C: ~50% (the real Lin kernel, now better-scoped). D: ~90% once A–C land.
Net "fully sorry-free #403": ~45%, but every phase is independently valuable and verifiable.
