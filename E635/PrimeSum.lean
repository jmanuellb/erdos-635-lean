import Mathlib

/-!
# Erdős 635 — divergence of the sum of prime reciprocals, in finite form

For every `t` and `K` there is a finite set of primes `p ≥ t` with `∑ 1/p ≥ K`.
-/

namespace E635

open Finset

theorem exists_primes (t : ℕ) (K : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ t ≤ p) ∧ K ≤ ∑ p ∈ P, (1 : ℝ) / p := by
  have hns := not_summable_one_div_on_primes
  have hnn : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n :=
    fun n => Set.indicator_nonneg (fun _ _ => by positivity) n
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hnn] at hns
  obtain ⟨n, hn⟩ := (hns.eventually_ge_atTop (K + t)).exists
  refine ⟨(range n).filter (fun p => p.Prime ∧ t ≤ p), fun p hp => (mem_filter.mp hp).2, ?_⟩
  rw [Finset.sum_filter]
  have key : ∀ i ∈ range n,
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i ≤
        (if i.Prime ∧ t ≤ i then (1 : ℝ) / i else 0) + (if i < t then 1 else 0) := by
    intro i _
    by_cases hi : i.Prime
    · rw [Set.indicator_of_mem (show i ∈ {p : ℕ | p.Prime} from hi)]
      by_cases hti : t ≤ i
      · rw [if_pos ⟨hi, hti⟩, if_neg (not_lt.mpr hti), add_zero]
      · have h1 : (1 : ℝ) / i ≤ 1 := by
          have h0 : (1 : ℝ) ≤ i := by exact_mod_cast hi.one_le
          rw [div_le_one (by linarith)]
          exact h0
        rw [if_neg (fun h => hti h.2), if_pos (not_le.mp hti), zero_add]
        exact h1
    · rw [Set.indicator_of_notMem (show i ∉ {p : ℕ | p.Prime} from hi)]
      refine add_nonneg ?_ ?_
      · split_ifs
        · positivity
        · exact le_rfl
      · split_ifs <;> norm_num
  have h2 := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_boole] at h2
  have h3 : (((range n).filter (fun i => i < t)).card : ℝ) ≤ t := by
    have h4 : ((range n).filter (fun i => i < t)).card ≤ (range t).card :=
      Finset.card_le_card (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
    rw [Finset.card_range] at h4
    exact_mod_cast h4
  linarith

end E635
