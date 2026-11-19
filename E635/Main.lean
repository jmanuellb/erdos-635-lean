import E635.Consecutive
import E635.SecondMoment
import E635.PrimeSum

/-!
# Erdős problem 635

If `A ⊆ {1,…,N}` is such that `b - a ∤ b` whenever `a < b` are in `A` with `b - a ≥ t`,
then `|A| ≤ (1/2 + o_t(1)) N`.
-/

namespace E635

open Finset

/-- The key inequality for a fixed finite set `P` of primes `≥ t` and a free parameter `s > 0`. -/
theorem card_mul_mu_le {t N : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ t ≤ p) {A : Finset ℕ}
    (hA : A ⊆ Ioc 0 N) (hgood : Good t A) {s : ℝ} (hs : 0 < s) :
    (A.card : ℝ) * mu P ≤
      (N : ℝ) / 2 * mu P + (P.card : ℝ) * (1 / 2) +
        ((N : ℝ) * mu P + 2 * mu P * P.card) / s + (N : ℝ) * (s / 4) := by
  -- (1) the sum of `w` over `A` is small
  have h1 : ∑ a ∈ A, w P a ≤ (N : ℝ) / 2 * mu P + (P.card : ℝ) * (1 / 2) := by
    rw [sum_w]
    have h : ∀ p ∈ P, (∑ a ∈ A, if p ∣ a then (1 : ℝ) else 0) ≤
        (N : ℝ) / 2 * ((1 : ℝ) / p) + 1 / 2 := by
      intro p hp
      rw [Finset.sum_boole]
      have hc := two_mul_card_multiples_le (hP p hp).1.pos (hP p hp).2 hA hgood
      have hc' : (2 : ℝ) * ((A.filter (fun a => p ∣ a)).card : ℝ) ≤ ((N / p : ℕ) : ℝ) + 1 := by
        exact_mod_cast hc
      have hd : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
      have he : (N : ℝ) / 2 * ((1 : ℝ) / p) = (N : ℝ) / p / 2 := by ring
      rw [he]
      linarith
    have h' := Finset.sum_le_sum h
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h'
    exact h'
  -- (2) the deficiency `mu - w` is small on average
  have h2 : ∑ a ∈ A, (mu P - w P a) ≤
      ((N : ℝ) * mu P + 2 * mu P * P.card) / s + (N : ℝ) * (s / 4) := by
    have hpt : ∀ a ∈ A, mu P - w P a ≤ (w P a - mu P) ^ 2 / s + s / 4 := by
      intro a _
      have hid : (w P a - mu P) ^ 2 / s + s / 4 - (mu P - w P a) =
          (w P a - mu P + s / 2) ^ 2 / s := by
        field_simp
        ring
      have hnn : 0 ≤ (w P a - mu P + s / 2) ^ 2 / s := by positivity
      linarith
    have h3 := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul] at h3
    have h4 : ∑ a ∈ A, (w P a - mu P) ^ 2 ≤ ∑ n ∈ Ioc 0 N, (w P n - mu P) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => sq_nonneg _)
    have h5 := (h4.trans (variance_le N (fun p hp => (hP p hp).1)))
    have h6 : (∑ a ∈ A, (w P a - mu P) ^ 2) / s ≤ ((N : ℝ) * mu P + 2 * mu P * P.card) / s :=
      div_le_div_of_nonneg_right h5 hs.le
    have h7 : (A.card : ℝ) ≤ N := by
      have := Finset.card_le_card hA
      rw [Nat.card_Ioc, Nat.sub_zero] at this
      exact_mod_cast this
    have h8 : (A.card : ℝ) * (s / 4) ≤ (N : ℝ) * (s / 4) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  linarith

end E635

open Finset in
/-- **Erdős problem 635.** -/
theorem erdos_635 (t : ℕ) (ht : 1 ≤ t) :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) →
      (A.card : ℝ) ≤ (1 / 2 + ε) * N := by
  intro ε hε
  obtain ⟨P, hP, hμ0⟩ := E635.exists_primes t (4 / ε ^ 2 + 1)
  have hμ : 4 / ε ^ 2 + 1 ≤ E635.mu P := hμ0
  have hμpos : 0 < E635.mu P := lt_of_lt_of_le (by positivity) hμ
  rw [Filter.eventually_atTop]
  refine ⟨⌈(P.card : ℝ) / (ε * E635.mu P) + P.card⌉₊, fun N hN A hA hgood => ?_⟩
  have hN' : (P.card : ℝ) / (ε * E635.mu P) + P.card ≤ N := Nat.ceil_le.mp hN
  have hA' : A ⊆ Ioc 0 N := by
    intro x hx
    have := Finset.mem_Icc.mp (hA hx)
    exact Finset.mem_Ioc.mpr ⟨by omega, this.2⟩
  have key := E635.card_mul_mu_le hP hA' hgood (s := 4 / ε) (by positivity)
  have e1 : ((N : ℝ) * E635.mu P + 2 * E635.mu P * P.card) / (4 / ε) =
      ε * N * E635.mu P / 4 + ε * E635.mu P * P.card / 2 := by
    field_simp
    ring
  have e2 : (N : ℝ) * (4 / ε / 4) = ε * N * (4 / ε ^ 2) / 4 := by
    field_simp
  have h3 : ε * N * (4 / ε ^ 2) ≤ ε * N * E635.mu P :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : ((P.card : ℝ) / (ε * E635.mu P) + P.card) * (ε * E635.mu P) ≤
      (N : ℝ) * (ε * E635.mu P) :=
    mul_le_mul_of_nonneg_right hN' (by positivity)
  have e4 : ((P.card : ℝ) / (ε * E635.mu P) + P.card) * (ε * E635.mu P) =
      P.card + ε * E635.mu P * P.card := by
    field_simp
  rw [e1, e2] at key
  rw [e4] at h4
  have hfin : (A.card : ℝ) * E635.mu P ≤ (1 / 2 + ε) * N * E635.mu P := by
    nlinarith [key, h3, h4]
  exact le_of_mul_le_mul_right hfin hμpos
