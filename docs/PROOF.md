# Erdős problem 635 — proof (written from the mathematics, before formalizing)

## Statement

Fix `t ≥ 1`. For every `ε > 0` there is `N0` such that for all `N ≥ N0` and all
`A ⊆ {1,…,N}` with the property

> (H) there are no `a < b` in `A` with `b − a ≥ t` and `(b − a) | b`,

we have `|A| ≤ (1/2 + ε) N`.

## Notation

`P` is a **fixed finite** set of primes, all `≥ t` (it depends on `t` and `ε` only, not on `N`).

* `μ = Σ_{p∈P} 1/p`,
* `w(n) = #{p ∈ P : p | n} = Σ_{p∈P} 1[p | n]`,
* `[N] = {1,…,N}` (in Lean: `Finset.Ioc 0 N`), and `#{n ∈ [N] : d | n} = ⌊N/d⌋`, with
  `N/d − 1 < ⌊N/d⌋ ≤ N/d`.

Choosing `P` fixed (instead of all primes up to `N^{1/3}`) makes all error terms constants
`O(|P|)`, which is all that is needed for an `o(1)` statement.

## Step 0. A finite set of primes ≥ t with large reciprocal sum

Claim: for all `t` and real `K` there is a finite set `P` of primes `≥ t` with `Σ_{p∈P} 1/p ≥ K`.

Let `g(i) = 1/i` if `i` is prime and `0` otherwise. `g ≥ 0` and `Σ g` diverges
(Mathlib: `not_summable_one_div_on_primes`), so the partial sums `Σ_{i<n} g(i)` tend to `+∞`
(`not_summable_iff_tendsto_nat_atTop_of_nonneg`); pick `n` with `Σ_{i<n} g(i) ≥ K + t`.
Put `P = {i < n : i prime, i ≥ t}`. Pointwise
`g(i) ≤ 1[i prime, i ≥ t]/i + 1[i < t]` (if `i` is prime and `< t`, use `1/i ≤ 1`), hence
`K + t ≤ Σ_{i<n} g(i) ≤ Σ_{p∈P} 1/p + #{i < t} ≤ Σ_{p∈P} 1/p + t`.

## Step 1. No two consecutive multiples

Claim: if `p ≥ t`, `p ≥ 1` and `A ⊆ [N]` satisfies (H), then with `B = {a ∈ A : p | a}`,
`2|B| ≤ ⌊N/p⌋ + 1`.

Proof. `B` and `B + p` are disjoint: if `b = a + p` with `a, b ∈ B ⊆ A` then `a < b`,
`b − a = p ≥ t` and `p | b`, contradicting (H). Both are sets of multiples of `p` inside
`(0, N + p]`, of which there are `⌊(N+p)/p⌋ = ⌊N/p⌋ + 1`. So `2|B| = |B ∪ (B+p)| ≤ ⌊N/p⌋ + 1`. ∎

## Step 2. `A` has few prime divisors from `P` in total

Double counting and Step 1 (each `p ∈ P` is `≥ t` and `≥ 2`):

`Σ_{a∈A} w(a) = Σ_{p∈P} #{a∈A : p | a} ≤ Σ_{p∈P} (N/p + 1)/2 = Nμ/2 + |P|/2.`   (1)

## Step 3. Moments of `w` on `[N]`

First moment: `S1 := Σ_{n≤N} w(n) = Σ_{p∈P} ⌊N/p⌋ ≥ Σ_p (N/p − 1) = Nμ − |P|.`

Second moment: `w(n)² = Σ_{p,q∈P} 1[p|n]·1[q|n]`, so `S2 := Σ_{n≤N} w(n)² = Σ_{p,q} c(p,q)`
with `c(p,q) = #{n ≤ N : p | n and q | n}`.

* `p = q`: `c = ⌊N/p⌋ ≤ N/p`.
* `p ≠ q` (distinct primes, coprime): `p|n ∧ q|n ⇔ pq | n`, so `c = ⌊N/(pq)⌋ ≤ N/(pq)`.

In both cases `c(p,q) ≤ N/(pq) + 1[p=q]·N/p`. Summing,
`S2 ≤ N Σ_{p,q} 1/(pq) + N Σ_p 1/p = Nμ² + Nμ.`

Variance (Turán–Kubilius for the fixed set `P`):

`V := Σ_{n≤N} (w(n) − μ)² = S2 − 2μ·S1 + Nμ² ≤ Nμ² + Nμ − 2μ(Nμ − |P|) + Nμ² = Nμ + 2μ|P|.`   (2)

(used `μ ≥ 0` to multiply the lower bound of `S1`).

## Step 4. Deficiency on `A`

For real `x` and `s > 0`: `−x ≤ x²/s + s/4`, because `x²/s + s/4 + x = (x + s/2)²/s ≥ 0`.
With `x = w(a) − μ`, summing over `a ∈ A ⊆ [N]` and using (2) and `|A| ≤ N`:

`Σ_{a∈A} (μ − w(a)) ≤ V/s + |A|·s/4 ≤ (Nμ + 2μ|P|)/s + N·s/4.`   (3)

## Step 5. Combine

`|A|·μ = Σ_{a∈A} w(a) + Σ_{a∈A} (μ − w(a))`, so by (1) and (3), for every `s > 0`:

`|A|·μ ≤ Nμ/2 + |P|/2 + (Nμ + 2μ|P|)/s + N·s/4.`   (4)

## Step 6. Choice of parameters

Given `ε > 0`, use Step 0 to pick `P` (primes `≥ t`) with `μ ≥ 4/ε² + 1` (so `μ > 0`), and take
`s = 4/ε`. Then

* `(Nμ + 2μ|P|)/s = εNμ/4 + εμ|P|/2`,
* `N·s/4 = N/ε = εN·(4/ε²)/4 ≤ εNμ/4`.

So (4) gives `|A|μ ≤ Nμ/2 + εNμ/2 + (|P|/2 + εμ|P|/2)`.
Let `N0 = ⌈|P|/(εμ) + |P|⌉`. For `N ≥ N0`, multiplying `|P|/(εμ) + |P| ≤ N` by `εμ > 0`:
`|P| + εμ|P| ≤ εNμ`, hence `|P|/2 + εμ|P|/2 ≤ εNμ/2` and

`|A|μ ≤ (1/2 + ε) N μ`.

Dividing by `μ > 0`: `|A| ≤ (1/2 + ε) N`. ∎

## Remarks

* The hypothesis `t ≥ 1` is not used (the argument works for `t = 0` too).
* Only primes are used so that `p | n ∧ q | n ⇔ pq | n` for `p ≠ q`; Step 1 holds for any `p ≥ max(t,1)`.
* `N0` is explicit in terms of `P`, but `P` comes from the divergence of `Σ 1/p`, non-effectively
  as formalized.

# Part II. Lower bound, asymptotic, and the case `t = 1` (file `E635/LowerBound.lean`)

## Step 7. Lower bound: the odd numbers

Let `O = {1, 3, 5, …} ∩ [1, N] = {2k + 1 : 0 ≤ k < ⌈N/2⌉}`; `|O| = ⌈N/2⌉ = ⌊(N + 1)/2⌋ ≥ N/2`.
If `a = 2i + 1 < b = 2j + 1` are in `O`, then `b − a = 2(j − i)` is even while `b` is odd, so
`b − a ∤ b`. Hence `O` satisfies (H) for **every** threshold `t` (in particular every `t ≥ 1`).

## Step 8. The extremal function and the asymptotic

Let `M(t, N)` be the largest `|A|` over `A ⊆ [1, N]` satisfying (H) (in Lean: the `sup` of `card`
over the admissible members of the finite powerset of `[1, N]`; the empty set is admissible, so the
sup is attained). Step 7 gives `N/2 ≤ ⌈N/2⌉ ≤ M(t, N)` for all `N`, and Steps 0–6 applied to an
extremal `A` give `M(t, N) ≤ (1/2 + ε) N` for `N ≥ N0(t, ε)`. Hence, for `c > 0`, taking `ε = c/2`,
`0 ≤ M(t, N) − N/2 ≤ (c/2) N = c · (N/2)` eventually, i.e. `M(t, N) − N/2 = o(N/2)`, which is the
definition of `M(t, N) ~ N/2` (`Asymptotics.IsEquivalent`).

## Step 9. Exact value for `t = 1`

For `t = 1` the condition `b − a ≥ 1` is automatic, and two consecutive integers `k, k + 1` cannot
both lie in `A` because `(k + 1) − k = 1 | k + 1`. Map `a ∈ A ⊆ [1, N]` to `(a − 1) div 2`, which
lies in `[0, ⌈N/2⌉)`. Two elements `a < b` with the same image satisfy `{a, b} = {2m + 1, 2m + 2}`,
so `b = a + 1`, which is excluded. The map is therefore injective and `|A| ≤ ⌈N/2⌉`. With Step 7,
`M(1, N) = ⌈N/2⌉` exactly.

For `t ≥ 2` the maximum can exceed `⌈N/2⌉` (brute force: `M(2, 14) = 9`, `M(3, 7) = 6`); only the
asymptotic `M(t, N) ~ N/2` is proved for general `t`.
