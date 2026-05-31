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

### What this buys us (clean partial kills — all elementary mod-arithmetic)
- `d_2(2^m) = 2^{m-1} mod 3 = 2` for **even** `m` — but fixable by the `0!+1!=2!` carry, so not decisive alone.
- `d_3(2^m) = 2` for **even** `m` (since `2^m mod 12 = 4`, `⌊4/3⌋…` ⇒ digit 2); `d_3` is **not**
  fixable by the `0!` carry (no factorial degeneracy makes a second `3!`). Kills **branch 1** for even `m`.
- `d_3(2^m − 1) = 2` for **odd** `m` (`2^m mod 12 = 8`, `2^m−1 ≡ 7`, `⌊7/3⌋ = 2`). Kills **branch 2**
  for odd `m`.

So for odd `m`: representable ⟺ `∀i≥2 d_i(2^m) ≤ 1` (branch 2 dead). For even `m`: representable ⟺
`∀i≥2 d_i(2^m − 1) ≤ 1` (branch 1 dead). Each large case is reduced to **a single all-digits-≤1 test
on one number.**

### The residual kernel (still genuinely Lin)
For the surviving branch we must show some `d_i ≥ 2` (`i ≥ 2`). The *leading* digit
`d_M = ⌊n/M!⌋` (`M` = largest factorial ≤ `n`) is `≤ 1` ⟺ `n ∈ [M!, 2M!)` — exactly the size
sandwich. For the `n` where the leading digit is 1 (infinitely many `m`), a **middle** digit must be
`≥ 2`; that is the irreducible cascade. **Now isolated to a single all-digits-≤1 test, no `0!` wrinkle,
no tied/untied split.** This is where the real work (item 1) lives.

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

### Phase C — the residual middle-digit lemma (item 1, hard half = Lin)
7. Show: if `2^m ∈ [M!, 2M!)` (leading digit 1) and `m ≥ 8`, some middle `d_i ≥ 2`. Attack via the
   cascade/recursion, now in clean FNS language. **This is the ~50% multi-session nut.** Possible
   sub-approaches: (a) strong induction tracking the residual `2^k − const` shape; (b) bound the number
   of consecutive tied levels via the exact-value (not just `v₂`) constraint; (c) a cleverer
   size+digit argument specific to the surviving (leading-digit-1) `m`.

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
- [ ] B6 even/odd modular kills
- [ ] C7 residual middle-digit (the hard kernel)
- [ ] D8 sharp assembly
- [ ] D9 reroute finite, retire `tied_carry_ceiling`

**Phase A done (session 3), all axiom-clean.** The endgame now only needs, for each `m ≥ 8`, a
positive-index factorial digit `≥ 2` in *both* `2^m` and `2^m − 1` (→ `not_factSum_of_digits`).

## Confidence
A: ~85% (standard, just laborious). B: ~80% (modular, but FNS-digit-of-`2^m` lemmas need care).
C: ~50% (the real Lin kernel, now better-scoped). D: ~90% once A–C land.
Net "fully sorry-free #403": ~45%, but every phase is independently valuable and verifiable.
