import Mathlib

/-!
# Erdős 635 — first and second moment of the number of prime divisors from a fixed finite set

`P` is a fixed finite set of primes, `w P n = #{p ∈ P : p ∣ n}` (as a real number) and
`mu P = ∑_{p ∈ P} 1/p`.  We prove `∑_{n ≤ N} (w P n - mu P)^2 ≤ N * mu P + 2 * mu P * |P|`.
-/

namespace E635

open Finset

/-- Number of `p ∈ P` dividing `n`, as a real number. -/
noncomputable def w (P : Finset ℕ) (n : ℕ) : ℝ := ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0

/-- Sum of the reciprocals of the elements of `P`. -/
noncomputable def mu (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1 : ℝ) / p

theorem mu_nonneg (P : Finset ℕ) : 0 ≤ mu P :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem count_dvd (N p : ℕ) :
    (∑ n ∈ Ioc 0 N, if p ∣ n then (1 : ℝ) else 0) = ((N / p : ℕ) : ℝ) := by
  rw [Finset.sum_boole, Nat.Ioc_filter_dvd_card_eq_div]

theorem sum_w (P S : Finset ℕ) :
    ∑ n ∈ S, w P n = ∑ p ∈ P, ∑ n ∈ S, if p ∣ n then (1 : ℝ) else 0 := by
  unfold w
  exact Finset.sum_comm

/-- First moment, lower bound. -/
theorem first_moment_ge (N : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    (N : ℝ) * mu P - P.card ≤ ∑ n ∈ Ioc 0 N, w P n := by
  rw [sum_w]
  have h : ∀ p ∈ P,
      (N : ℝ) * ((1 : ℝ) / p) - 1 ≤ ∑ n ∈ Ioc 0 N, if p ∣ n then (1 : ℝ) else 0 := by
    intro p hp
    rw [count_dvd]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hP p hp
    have h1 : N < p * (N / p + 1) := Nat.lt_mul_div_succ N (hP p hp)
    have h2 : (N : ℝ) < (p : ℝ) * (((N / p : ℕ) : ℝ) + 1) := by exact_mod_cast h1
    have h3 : (N : ℝ) * ((1 : ℝ) / p) < ((N / p : ℕ) : ℝ) + 1 := by
      rw [mul_one_div, div_lt_iff₀ hp0, mul_comm]
      exact h2
    linarith
  have h' := Finset.sum_le_sum h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at h'
  exact h'

/-- Number of `n ≤ N` divisible by both `p` and `q`. -/
theorem pair_count_le (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∑ n ∈ Ioc 0 N, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)) ≤
      (N : ℝ) * (((1 : ℝ) / p) * ((1 : ℝ) / q)) +
        (if p = q then (N : ℝ) * ((1 : ℝ) / p) else 0) := by
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    have e : ∀ n ∈ Ioc 0 N, (if p ∣ n then (1 : ℝ) else 0) * (if p ∣ n then (1 : ℝ) else 0) =
        if p ∣ n then (1 : ℝ) else 0 := by
      intro n _
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl e, count_dvd]
    have h1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have h2 : (0 : ℝ) ≤ (N : ℝ) * (((1 : ℝ) / p) * ((1 : ℝ) / p)) := by positivity
    have h3 : (N : ℝ) * ((1 : ℝ) / p) = (N : ℝ) / p := mul_one_div _ _
    linarith
  · rw [if_neg hpq, add_zero]
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have e : ∀ n ∈ Ioc 0 N, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) =
        if p * q ∣ n then (1 : ℝ) else 0 := by
      intro n _
      by_cases h1 : p ∣ n
      · by_cases h2 : q ∣ n
        · rw [if_pos h1, if_pos h2, if_pos (hcop.mul_dvd_of_dvd_of_dvd h1 h2), mul_one]
        · rw [if_neg h2, if_neg (fun h => h2 (dvd_trans (dvd_mul_left q p) h)), mul_zero]
      · rw [if_neg h1, if_neg (fun h => h1 (dvd_trans (dvd_mul_right p q) h)), zero_mul]
    rw [Finset.sum_congr rfl e, count_dvd]
    have h1 : ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : (N : ℝ) / ((p * q : ℕ) : ℝ) = (N : ℝ) * (((1 : ℝ) / p) * ((1 : ℝ) / q)) := by
      rw [Nat.cast_mul, one_div, one_div, ← mul_inv, div_eq_mul_inv]
    linarith

/-- Second moment, upper bound. -/
theorem second_moment_le (N : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ Ioc 0 N, (w P n) ^ 2 ≤ (N : ℝ) * mu P ^ 2 + (N : ℝ) * mu P := by
  have e1 : ∀ n ∈ Ioc 0 N, (w P n) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n _
    rw [sq, w, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ p ∈ P, (∑ n ∈ Ioc 0 N, ∑ q ∈ P,
      (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)) ≤
      ∑ q ∈ P, ((N : ℝ) * (((1 : ℝ) / p) * ((1 : ℝ) / q)) +
        (if p = q then (N : ℝ) * ((1 : ℝ) / p) else 0)) := by
    intro p hp
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun q hq => pair_count_le N (hP p hp) (hP q hq))
  refine (Finset.sum_le_sum e2).trans (le_of_eq ?_)
  have e3 : ∀ p ∈ P, (∑ q ∈ P, ((N : ℝ) * (((1 : ℝ) / p) * ((1 : ℝ) / q)) +
        (if p = q then (N : ℝ) * ((1 : ℝ) / p) else 0))) =
      (N : ℝ) * ((1 : ℝ) / p) * mu P + (N : ℝ) * ((1 : ℝ) / p) := by
    intro p hp
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hp, mu, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl e3, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [show (∑ p ∈ P, (1 : ℝ) / p) = mu P from rfl]
  ring

/-- Turán–Kubilius type variance bound for a fixed finite set of primes. -/
theorem variance_le (N : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ Ioc 0 N, (w P n - mu P) ^ 2 ≤ (N : ℝ) * mu P + 2 * mu P * P.card := by
  have e : ∀ n ∈ Ioc 0 N,
      (w P n - mu P) ^ 2 = (w P n) ^ 2 - 2 * mu P * w P n + mu P ^ 2 := by
    intro n _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
  have h1 := first_moment_ge N (fun p hp => (hP p hp).pos)
  have h2 := second_moment_le N hP
  have h3 := mul_nonneg (mu_nonneg P) (sub_nonneg.mpr h1)
  nlinarith [h1, h2, h3]

end E635
