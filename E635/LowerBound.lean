import E635.Main

/-!
# Erdős problem 635 — the matching lower bound and the asymptotic

* `erdos_635_lower`: for every `t ≥ 1` and every `N`, the odd numbers in `[1, N]` form an
  admissible set of size `⌈N/2⌉ = (N + 1) / 2 ≥ N/2`.
* `maxAdmissible t N`: the largest size of an admissible `A ⊆ [1, N]`, defined as a `sup` over
  the (finite) powerset of `[1, N]`, with its defining properties.
* `maxAdmissible_isEquivalent`: combined with `erdos_635`, `maxAdmissible t N ~ N/2`.
* `maxAdmissible_one`: for `t = 1` the maximum is exactly `⌈N/2⌉ = (N + 1) / 2`.
-/

namespace E635

open Finset

/-- The odd numbers in `[1, N]`, written as the image of `k ↦ 2k + 1` on `[0, (N+1)/2)`. -/
def odds (N : ℕ) : Finset ℕ := (range ((N + 1) / 2)).image (fun k => 2 * k + 1)

theorem odds_subset (N : ℕ) : odds N ⊆ Icc 1 N := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
  rw [mem_range] at hk
  rw [mem_Icc]
  omega

theorem card_odds (N : ℕ) : (odds N).card = (N + 1) / 2 := by
  rw [odds, card_image_of_injective _ (fun x y h => by simpa using h), card_range]

/-- If `a < b` are both odd then `b - a` is even and `b` is odd, so `b - a ∤ b`
(this holds for every threshold `t`). -/
theorem good_odds (t N : ℕ) : Good t (odds N) := by
  intro a ha b hb hab _ hdvd
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := mem_image.mp hb
  have h2 : 2 ∣ (2 * j + 1) - (2 * i + 1) := ⟨j - i, by omega⟩
  have h3 := h2.trans hdvd
  omega

end E635

/-- **Erdős problem 635, lower bound.** For every `t ≥ 1` and every `N` there is an admissible
`A ⊆ {1,…,N}` (the odd numbers) with `|A| = ⌈N/2⌉ = (N + 1) / 2`, in particular `|A| ≥ N/2`. -/
theorem erdos_635_lower (t : ℕ) (_ht : 1 ≤ t) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) ∧
      A.card = (N + 1) / 2 ∧ (N : ℝ) / 2 ≤ A.card := by
  refine ⟨E635.odds N, E635.odds_subset N, E635.good_odds t N, E635.card_odds N, ?_⟩
  rw [E635.card_odds]
  have h : N ≤ 2 * ((N + 1) / 2) := by omega
  have h' : (N : ℝ) ≤ 2 * (((N + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
  linarith

namespace E635

open Finset

open Classical in
/-- The largest size of an admissible `A ⊆ {1,…,N}`: the `sup` of `card` over the admissible
members of the (finite) powerset of `[1, N]`. -/
noncomputable def maxAdmissible (t N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun A => Good t A)).sup card

/-- Every admissible `A ⊆ [1, N]` has at most `maxAdmissible t N` elements. -/
theorem card_le_maxAdmissible {t N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    (hgood : ∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) :
    A.card ≤ maxAdmissible t N := by
  classical
  unfold maxAdmissible
  exact le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hA, hgood⟩)

/-- The maximum is attained by some admissible `A ⊆ [1, N]`. -/
theorem exists_card_eq_maxAdmissible (t N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) ∧
      A.card = maxAdmissible t N := by
  classical
  unfold maxAdmissible
  have hne : ((Icc 1 N).powerset.filter (fun A => Good t A)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, fun a ha => absurd ha (notMem_empty a)⟩⟩
  obtain ⟨A, hA, heq⟩ := exists_mem_eq_sup _ hne card
  obtain ⟨hA1, hA2⟩ := mem_filter.mp hA
  exact ⟨A, mem_powerset.mp hA1, hA2, heq.symm⟩

/-- `maxAdmissible t N` is characterised by the two properties above. -/
theorem maxAdmissible_eq_iff {t N m : ℕ} :
    maxAdmissible t N = m ↔
      (∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) ∧ A.card = m) ∧
      (∀ A : Finset ℕ, A ⊆ Icc 1 N →
        (∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)) → A.card ≤ m) := by
  constructor
  · rintro rfl
    exact ⟨exists_card_eq_maxAdmissible t N, fun A hA hg => card_le_maxAdmissible hA hg⟩
  · rintro ⟨⟨A, hA, hg, rfl⟩, hmax⟩
    obtain ⟨B, hB, hgB, hcB⟩ := exists_card_eq_maxAdmissible t N
    exact le_antisymm (hcB ▸ hmax B hB hgB) (card_le_maxAdmissible hA hg)

theorem le_maxAdmissible (t N : ℕ) (ht : 1 ≤ t) : (N + 1) / 2 ≤ maxAdmissible t N := by
  obtain ⟨A, hA, hg, hc, _⟩ := erdos_635_lower t ht N
  exact hc ▸ card_le_maxAdmissible hA hg

theorem half_le_maxAdmissible (t N : ℕ) (ht : 1 ≤ t) : (N : ℝ) / 2 ≤ maxAdmissible t N := by
  obtain ⟨A, hA, hg, _, hr⟩ := erdos_635_lower t ht N
  have h : (A.card : ℝ) ≤ maxAdmissible t N := by exact_mod_cast card_le_maxAdmissible hA hg
  linarith

/-- For `t = 1` no two consecutive integers `k, k + 1` lie in `A` (as `1 ∣ k + 1`), so
`a ↦ (a - 1) / 2` is injective on `A` with values in `[0, (N+1)/2)`. -/
theorem card_le_of_t_one {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    (hgood : ∀ a ∈ A, ∀ b ∈ A, a < b → 1 ≤ b - a → ¬ (b - a ∣ b)) :
    A.card ≤ (N + 1) / 2 := by
  have h := card_le_card_of_injOn (fun a => (a - 1) / 2) (t := range ((N + 1) / 2))
    (by
      intro a ha
      have := mem_Icc.mp (hA ha)
      simp only [coe_range, Set.mem_Iio]
      omega)
    (by
      intro a ha b hb hab
      have hab' : (a - 1) / 2 = (b - 1) / 2 := hab
      have ha1 := mem_Icc.mp (hA ha)
      have hb1 := mem_Icc.mp (hA hb)
      rcases lt_trichotomy a b with hlt | heq | hgt
      · have h1 : b - a = 1 := by omega
        exact absurd (by rw [h1]; exact one_dvd b) (hgood a ha b hb hlt (by omega))
      · exact heq
      · have h1 : a - b = 1 := by omega
        exact absurd (by rw [h1]; exact one_dvd a) (hgood b hb a ha hgt (by omega)))
  simpa using h

end E635

open Asymptotics in
/-- **Erdős problem 635, asymptotic form.** For every fixed `t ≥ 1`, the maximum size of an
admissible subset of `{1,…,N}` is asymptotically `N/2`. -/
theorem erdos_635_isEquivalent (t : ℕ) (ht : 1 ≤ t) :
    (fun N : ℕ => (E635.maxAdmissible t N : ℝ)) ~[Filter.atTop] (fun N : ℕ => (N : ℝ) / 2) := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [erdos_635 t ht (c / 2) (by positivity)] with N hN
  obtain ⟨A, hA, hg, hcard⟩ := E635.exists_card_eq_maxAdmissible t N
  have hup := hN A hA hg
  rw [hcard] at hup
  have hlow := E635.half_le_maxAdmissible t N ht
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
  linarith

/-- **Erdős problem 635, `t = 1`.** The maximum is exactly `⌈N/2⌉ = (N + 1) / 2`. -/
theorem erdos_635_t_one (N : ℕ) : E635.maxAdmissible 1 N = (N + 1) / 2 := by
  obtain ⟨A, hA, hg, hcard⟩ := E635.exists_card_eq_maxAdmissible 1 N
  exact le_antisymm (hcard ▸ E635.card_le_of_t_one hA hg) (E635.le_maxAdmissible 1 N le_rfl)
