# Erdős Problem 635 in Lean 4

A complete, `sorry`-free Lean 4 / Mathlib formalization of the upper bound in
[Erdős Problem 635](https://www.erdosproblems.com/635), together with the matching lower bound,
the resulting asymptotic `M(t, N) ~ N/2` for the extremal size, and the exact value for `t = 1`.

## The problem

Let `t ≥ 1` and let `A ⊆ {1, …, N}` be a set such that whenever `a < b` are in `A` with
`b − a ≥ t`, the difference `b − a` does not divide `b`. Is it true that
`|A| ≤ (1/2 + o_t(1)) N`?

This repository proves that the answer is **yes**, and that it is sharp: the odd numbers give an
admissible set of size `⌈N/2⌉` for every `t` and `N`, so the maximum `M(t, N)` satisfies
`M(t, N) ~ N/2` for every fixed `t ≥ 1`; for `t = 1`, `M(1, N) = ⌈N/2⌉` exactly. It does **not**
determine `M(t, N)` exactly for `t ≥ 2` (where it can exceed `⌈N/2⌉`, e.g. `M(2, 14) = 9`) or the
size of the error term `M(t, N) − N/2`.

It also proves the explicit finite inequality `M(t, N) ≤ ⌈N/2⌉ + |B₁| + |B₂|` (Theorem A of the
accompanying note, finite form; see below), from which the error term `O(N / log N)` follows by
standard analytic estimates that are not formalized here.

## Lean statements

### Upper bound

File `E635/Main.lean`, theorem `erdos_635` (root namespace):

```lean
theorem erdos_635 (t : ℕ) (ht : 1 ≤ t) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) →
      (A.card : ℝ) ≤ (1 / 2 + ε) * N
```

`o_t(1)` is rendered as "for every `ε > 0`, for all sufficiently large `N`", with the threshold
allowed to depend on `t` and `ε`. Since `a < b`, the natural-number subtraction `b - a` is the true
difference. The hypothesis `ht` is not used by the proof (the statement also holds for `t = 0`);
it is kept to match the problem.

### Lower bound, extremal function, asymptotic, `t = 1`

File `E635/LowerBound.lean` (root namespace unless prefixed by `E635.`):

```lean
theorem erdos_635_lower (t : ℕ) (_ht : 1 ≤ t) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) ∧
      A.card = (N + 1) / 2 ∧ (N : ℝ) / 2 ≤ A.card

noncomputable def E635.maxAdmissible (t N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun A => Good t A)).sup card

theorem E635.maxAdmissible_eq_iff {t N m : ℕ} :
    maxAdmissible t N = m ↔
      (∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) ∧ A.card = m) ∧
      (∀ A : Finset ℕ, A ⊆ Icc 1 N →
        (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) → A.card ≤ m)

theorem erdos_635_isEquivalent (t : ℕ) (ht : 1 ≤ t) :
    (fun N : ℕ => (E635.maxAdmissible t N : ℝ)) ~[Filter.atTop] (fun N : ℕ => (N : ℝ) / 2)

theorem erdos_635_t_one (N : ℕ) : E635.maxAdmissible 1 N = (N + 1) / 2
```

`(N + 1) / 2` is natural-number division, i.e. `⌈N/2⌉`. `E635.Good t A` is the hypothesis of the
problem, spelled out verbatim in `maxAdmissible_eq_iff` (the defining property of the maximum, split
into `card_le_maxAdmissible` and `exists_card_eq_maxAdmissible`). `~[Filter.atTop]` is Mathlib's
`Asymptotics.IsEquivalent`: `M(t, N) − N/2 = o(N/2)`.

### Finite core of the explicit bound `M(t, N) ≤ ⌈N/2⌉ + |B₁| + |B₂|`

Files `E635/Lines.lean`, `E635/DoubleCount.lean`, `E635/Weights.lean`, `E635/FiniteBound.lean`
(namespace `E635`). `lines T n` is the set of primes `p ≥ T` dividing `n`; `odds N` is the set of
odd numbers in `[1, N]`.

```lean
theorem one_per_line {t : ℕ} {A : Finset ℕ} (hgood : Good t A) {o p : ℕ}
    (ho : o % 2 = 1) (hp : 0 < p) (hpt : t ≤ p) (hpo : p ∣ o) (hlt : p < o) :
    ¬ (o - p ∈ A ∧ o + p ∈ A)

-- weight systems: w ≥ 0 and ∑_{p ∈ lines T o} w o p ≤ 1 for every o ∈ odds N
def IsWeight (T N : ℕ) (w : ℕ → ℕ → ℝ) : Prop :=
  (∀ o p, 0 ≤ w o p) ∧ ∀ o ∈ odds N, ∑ p ∈ lines T o, w o p ≤ 1
noncomputable def cov (T N : ℕ) (w : ℕ → ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ p ∈ lines T e, (w (e - p) p + if e + p ≤ N then w (e + p) p else 0)

theorem card_le_of_weight {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) {w : ℕ → ℕ → ℝ}
    (hw : IsWeight T N w) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hgood : Good t A) :
    A.card ≤ (N + 1) / 2 + (A.filter (fun e => e % 2 = 0 ∧ cov T N w e < 1)).card

theorem maxAdmissible_le_of_weight {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T)
    {w : ℕ → ℕ → ℝ} (hw : IsWeight T N w) :
    maxAdmissible t N ≤ (N + 1) / 2 + (badSet T N w).card

-- B1 T N = {e ∈ [1, N] : e even, 2 · rad_{≥T}(e)² < 3e}
-- B2 T N = {p · (N / p) : p prime, T ≤ p, 4p ≤ N, N / p even}
theorem badSet_subset {T N : ℕ} (hT : 3 ≤ T) : badSet T N (logWeight T) ⊆ B1 T N ∪ B2 T N

theorem maxAdmissible_le_B1_B2 {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) :
    maxAdmissible t N ≤ (N + 1) / 2 + (B1 T N).card + (B2 T N).card
```

`badSet T N w` is `{e ∈ [1, N] : e even, cov T N w e < 1}` and `logWeight T o p = log p / log rad_{≥T}(o)`
(the weights of Theorem A of the accompanying note; take `T = max t 3`). The analytic estimates of
`|B₁|` and `|B₂|` (Rankin's trick, prime counting) are not formalized.

## Proof outline

The full write-up is in [`docs/PROOF.md`](docs/PROOF.md); the Lean files follow it step by step.

1. Fix a **finite** set `P` of primes `≥ t` with `μ = Σ_{p∈P} 1/p` large (possible because
   `Σ 1/p` diverges, `not_summable_one_div_on_primes`). `P` depends only on `t` and `ε`.
2. For `p ∈ P`, the multiples of `p` in `A` and their translates by `p` are disjoint (a pair
   `a, a + p` would violate the hypothesis), so `A` contains at most `(⌊N/p⌋ + 1)/2` multiples of `p`.
3. Double counting: with `w(n) = #{p ∈ P : p ∣ n}`, `Σ_{a∈A} w(a) ≤ Nμ/2 + |P|/2`.
4. A Turán–Kubilius type variance bound for the fixed set `P`:
   `Σ_{n≤N} (w(n) − μ)² ≤ Nμ + 2μ|P|`.
5. The pointwise inequality `μ − w ≤ (w − μ)²/s + s/4` (`s > 0`) bounds the total deficiency
   `Σ_{a∈A} (μ − w(a))` by `(Nμ + 2μ|P|)/s + Ns/4`.
6. Adding 3 and 5: `|A|·μ ≤ Nμ/2 + |P|/2 + (Nμ + 2μ|P|)/s + Ns/4`.
7. Taking `μ ≥ 4/ε² + 1`, `s = 4/ε` and `N ≥ ⌈|P|/(εμ) + |P|⌉` gives `|A| ≤ (1/2 + ε) N`.

All error terms are constants `O(|P|)`; no asymptotics of prime sums beyond divergence are needed.

Lower bound and asymptotic (`docs/PROOF.md`, Part II):

8. If `a < b` are odd, `b − a` is even and `b` is odd, so `b − a ∤ b`: the odd numbers in `[1, N]`
   are admissible for every `t`, and there are `⌈N/2⌉ ≥ N/2` of them.
9. Hence `N/2 ≤ M(t, N) ≤ (1/2 + ε) N` eventually, i.e. `M(t, N) ~ N/2`.
10. For `t = 1`, no two consecutive integers lie in `A` (`1 ∣ k + 1`), so `a ↦ (a − 1)/2` is
    injective from `A` into `[0, ⌈N/2⌉)`, giving `M(1, N) = ⌈N/2⌉`.

## Files

| File | Content |
| --- | --- |
| `E635/Consecutive.lean` | step 2 (`two_mul_card_multiples_le`) |
| `E635/PrimeSum.lean` | step 1 (`exists_primes`) |
| `E635/SecondMoment.lean` | `w`, `mu`, first and second moments, variance bound |
| `E635/Main.lean` | `card_mul_mu_le` (step 6) and `erdos_635` |
| `E635/LowerBound.lean` | `erdos_635_lower`, `maxAdmissible`, `erdos_635_isEquivalent`, `erdos_635_t_one` |
| `E635/Lines.lean` | `lines`, the "one per line" lemma and neighbour facts |
| `E635/DoubleCount.lean` | weight systems, `cov`, `card_le_of_weight`, `maxAdmissible_le_of_weight` |
| `E635/Weights.lean` | `radT`, `logWeight`, `isWeight_logWeight` |
| `E635/FiniteBound.lean` | `B1`, `B2`, `badSet_subset`, `maxAdmissible_le_B1_B2` |
| `E635/Axioms.lean` | `#print axioms` for the main theorems |
| `docs/PROOF.md` | the mathematical proof |

## Versions

* Lean `v4.36.0` (`lean-toolchain`: `leanprover/lean4:v4.36.0`)
* Mathlib `v4.36.0`, pinned to commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
  (`lakefile.toml` and `lake-manifest.json`)

## Reproduction

```bash
# with elan installed
lake exe cache get     # download prebuilt Mathlib oleans
lake build             # builds the E635 library, including E635/Axioms.lean
```

On a heavily loaded Windows machine, building several modules that import `Mathlib` in parallel
occasionally failed with a spurious `failed to read file '…/Mathlib/….olean.private'`. Building
the modules one at a time (`lake build E635.<Module>`, then `lake build`) worked.

## Axiom audit

`lake build` compiles `E635/Axioms.lean`, which prints:

```
info: E635/Axioms.lean:5:0: 'erdos_635' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:6:0: 'erdos_635_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:7:0: 'erdos_635_isEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:8:0: 'erdos_635_t_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:9:0: 'E635.card_le_maxAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:10:0: 'E635.exists_card_eq_maxAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:11:0: 'E635.maxAdmissible_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:12:0: 'E635.one_per_line' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:13:0: 'E635.card_le_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:14:0: 'E635.maxAdmissible_le_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:15:0: 'E635.badSet_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E635/Axioms.lean:16:0: 'E635.maxAdmissible_le_B1_B2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard axioms of Lean/Mathlib are used. The sources contain no `sorry`, `admit`,
`axiom` or `native_decide`.

## Attribution

* **Mathematics.** This repository does not claim the mathematical solution. On erdosproblems.com
  the resolution of the upper bound is attributed to GPT-5.2 Pro / Liam Price (January 2026).
  The proof in `docs/PROOF.md` was written from the public outline of that argument before
  formalizing; the specific choices (fixed finite prime set, no Cauchy–Schwarz) are ours. The
  lower bound (odd numbers) and the `t = 1` argument are elementary observations.
* **Earlier Lean proof.** A Lean proof generated by Aristotle was published earlier (January 2026)
  as a link in the erdosproblems.com forum thread for this problem. It was **not** consulted:
  this formalization was written independently from `docs/PROOF.md`.
* **Formalization:** `<AUTHOR>`.

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
