import E635.Weights

/-!
# Erdős 635 — Theorem A of the note, finite form

`M(t, N) ≤ ⌈N/2⌉ + |B₁| + |B₂|` with `T = max(t, 3)` (any `T ≥ max(t, 3)` works),
`B₁ = {e ≤ N even : 2 · rad_{≥T}(e)² < 3e}` and
`B₂ = {p ⌊N/p⌋ : p prime, T ≤ p, 4p ≤ N, ⌊N/p⌋ even}`.
-/

namespace E635

open Finset

/-- `B₁ = {e ∈ [1, N] : e even, rad_{≥T}(e)² < (3/2) e}`. -/
def B1 (T N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun e => e % 2 = 0 ∧ 2 * radT T e ^ 2 < 3 * e)

/-- `B₂ = {p ⌊N/p⌋ : p prime, T ≤ p ≤ N/4, ⌊N/p⌋ even}`. -/
def B2 (T N : ℕ) : Finset ℕ :=
  ((Icc 1 N).filter (fun p => p.Prime ∧ T ≤ p ∧ 4 * p ≤ N ∧ (N / p) % 2 = 0)).image
    (fun p => p * (N / p))

theorem badSet_subset {T N : ℕ} (hT : 3 ≤ T) :
    badSet T N (logWeight T) ⊆ B1 T N ∪ B2 T N := by
  intro e he
  unfold badSet at he
  rw [mem_filter, mem_Icc] at he
  obtain ⟨⟨he1, heN⟩, he2, hcov⟩ := he
  rw [mem_union]
  by_contra hcon
  push_neg at hcon
  obtain ⟨hB1, hB2⟩ := hcon
  have hR : 3 * e ≤ 2 * radT T e ^ 2 := by
    by_contra h
    push_neg at h
    exact hB1 (mem_filter.mpr ⟨mem_Icc.mpr ⟨he1, heN⟩, he2, h⟩)
  apply absurd hcov
  push_neg
  have hfacts : ∀ p ∈ lines T e,
      p ∣ e ∧ 0 < p ∧ p % 2 = 1 ∧ 2 * p ≤ e ∧ p.Prime ∧ T ≤ p := by
    intro p hp
    obtain ⟨f1, -, f3, -, f5, f6, f7⟩ := line_facts (le_refl T) hT hp
    exact ⟨f1, f3, f5, two_mul_le he2 f5 f1 (by omega), f6, f7⟩
  have hterm_nonneg : ∀ p ∈ lines T e, 0 ≤ logWeight T (e - p) p +
      (if e + p ≤ N then logWeight T (e + p) p else 0) := by
    intro p _
    refine add_nonneg (logWeight_nonneg _ _ _) ?_
    split_ifs
    · exact logWeight_nonneg _ _ _
    · exact le_refl 0
  have hsub_lines : ∀ p ∈ lines T e, p ∈ lines T (e - p) := by
    intro p hp
    obtain ⟨hpe, hp0, _, h2p, hpr, hTp⟩ := hfacts p hp
    refine mem_lines.mpr ⟨⟨?_, by omega⟩, hpr, hTp⟩
    rw [show e = p + (e - p) by omega] at hpe
    exact (Nat.dvd_add_right (dvd_refl p)).mp hpe
  by_cases hc : ∃ p ∈ lines T e, N < e + p
  · -- Case 2 of the note
    obtain ⟨p, hp, hNp⟩ := hc
    obtain ⟨hpe, hp0, hp2, h2p, hpr, hTp⟩ := hfacts p hp
    obtain ⟨k, hk⟩ := hpe
    have hdiv : N / p = k := by
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]
        omega
      · rw [add_mul, one_mul, mul_comm k p]
        omega
    have hk2 : k % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exact h
      · exfalso
        rw [hk, Nat.mul_mod, hp2, h] at he2
        simp at he2
    by_cases h4 : 4 ≤ k
    · exfalso
      apply hB2
      have h4p : p * 4 ≤ p * k := Nat.mul_le_mul_left p h4
      rw [B2, mem_image]
      refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, by omega⟩, hpr, hTp, by omega, ?_⟩, ?_⟩
      · rw [hdiv]
        exact hk2
      · rw [hdiv, hk]
    · have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        omega
      have hk' : k = 2 := by omega
      rw [hk'] at hk
      have hep : e - p = p := by omega
      have hle : logWeight T (e - p) p + (if e + p ≤ N then logWeight T (e + p) p else 0) ≤
          cov T N (logWeight T) e := by
        unfold cov
        exact single_le_sum (f := fun q => logWeight T (e - q) q +
          (if e + q ≤ N then logWeight T (e + q) q else 0)) hterm_nonneg hp
      have hw1 : logWeight T (e - p) p = 1 := by
        rw [hep]
        exact logWeight_self hpr hTp
      have hnn : (0 : ℝ) ≤ (if e + p ≤ N then logWeight T (e + p) p else 0) := by
        split_ifs
        · exact logWeight_nonneg _ _ _
        · exact le_refl 0
      linarith
  · -- Case 1 of the note
    push_neg at hc
    have he2r : (2 : ℝ) ≤ e := by
      have : 2 ≤ e := by omega
      exact_mod_cast this
    have hL : 0 < Real.log (3 * e / 2) := Real.log_pos (by linarith)
    have hterm : ∀ p ∈ lines T e, 2 * (Real.log p / Real.log (3 * e / 2)) ≤
        logWeight T (e - p) p + (if e + p ≤ N then logWeight T (e + p) p else 0) := by
      intro p hp
      obtain ⟨_, _, _, h2p, _, _⟩ := hfacts p hp
      have h2pr : (2 * p : ℝ) ≤ e := by exact_mod_cast h2p
      rw [if_pos (hc p hp)]
      have a1 := logWeight_ge (hsub_lines p hp) (X := 3 * e / 2) (by
        rw [Nat.cast_sub (by omega)]
        have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        linarith)
      have hplus : p ∈ lines T (e + p) := by
        obtain ⟨hpe, hp0, _, _, hpr, hTp⟩ := hfacts p hp
        exact mem_lines.mpr ⟨⟨dvd_add hpe dvd_rfl, by omega⟩, hpr, hTp⟩
      have a2 := logWeight_ge hplus (X := 3 * e / 2) (by
        push_cast
        linarith)
      linarith
    have hsum : 2 * Real.log (radT T e) / Real.log (3 * e / 2) ≤ cov T N (logWeight T) e := by
      unfold cov
      rw [log_radT, mul_sum, sum_div]
      refine sum_le_sum (fun p hp => ?_)
      rw [mul_div_assoc]
      exact hterm p hp
    have hRr : (3 * e / 2 : ℝ) ≤ (radT T e : ℝ) ^ 2 := by
      have : ((3 * e : ℕ) : ℝ) ≤ ((2 * radT T e ^ 2 : ℕ) : ℝ) := by exact_mod_cast hR
      push_cast at this
      linarith
    have hlog : Real.log (3 * e / 2) ≤ 2 * Real.log (radT T e) := by
      have hp2 := Real.log_pow 2 (radT T e : ℝ)
      push_cast at hp2
      rw [← hp2]
      exact Real.log_le_log (by linarith) hRr
    have h1 : 1 ≤ 2 * Real.log (radT T e) / Real.log (3 * e / 2) := by
      rw [le_div_iff₀ hL]
      linarith
    linarith

/-- **Theorem A of the note, finite form.** For `T ≥ t`, `T ≥ 3` (e.g. `T = max t 3`):
`M(t, N) ≤ ⌈N/2⌉ + |B₁| + |B₂|`. -/
theorem maxAdmissible_le_B1_B2 {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) :
    maxAdmissible t N ≤ (N + 1) / 2 + (B1 T N).card + (B2 T N).card := by
  have h := maxAdmissible_le_of_weight htT hT (isWeight_logWeight T N)
  have h2 := card_le_card (badSet_subset (N := N) hT)
  have h3 := card_union_le (B1 T N) (B2 T N)
  omega

end E635
