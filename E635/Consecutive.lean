import Mathlib

/-!
# Erdős 635 — step 1: no two consecutive multiples

If `A ⊆ {1,…,N}` has no pair `a < b` with `b - a ≥ t` and `(b - a) ∣ b`, then for every
`p ≥ t` the set `A` contains at most `(⌊N/p⌋ + 1)/2` multiples of `p`.
-/

namespace E635

open Finset

/-- The hypothesis of the problem. -/
def Good (t : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a < b → t ≤ b - a → ¬ (b - a ∣ b)

/-- The multiples of `p` in `A` and their translates by `p` are disjoint sets of multiples of
`p` inside `(0, N + p]`. -/
theorem two_mul_card_multiples_le {t N p : ℕ} (hp : 0 < p) (htp : t ≤ p) {A : Finset ℕ}
    (hA : A ⊆ Ioc 0 N) (hgood : Good t A) :
    2 * (A.filter (fun a => p ∣ a)).card ≤ N / p + 1 := by
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B = A.filter (fun a => p ∣ a) := ⟨_, rfl⟩
  rw [← hB]
  have hmem : ∀ x, x ∈ B → x ∈ A ∧ p ∣ x := by
    intro x hx
    rw [hB] at hx
    exact Finset.mem_filter.mp hx
  have hdisj : Disjoint B (B.image (fun x => x + p)) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb'
    have h1 : a + p - a = p := by omega
    refine hgood a (hmem a ha).1 (a + p) (hmem _ hb).1 (by omega) (by omega) ?_
    rw [h1]
    exact (hmem _ hb).2
  have hcard : (B.image (fun x => x + p)).card = B.card :=
    Finset.card_image_of_injective _ (fun x y h => Nat.add_right_cancel h)
  have hsub : B ∪ B.image (fun x => x + p) ⊆ (Ioc 0 (N + p)).filter (fun x => p ∣ x) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_filter, Finset.mem_Ioc]
    rcases hx with hx | hx
    · have h := Finset.mem_Ioc.mp (hA (hmem x hx).1)
      exact ⟨⟨h.1, by omega⟩, (hmem x hx).2⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have h := Finset.mem_Ioc.mp (hA (hmem a ha).1)
      exact ⟨⟨by omega, by omega⟩, Dvd.dvd.add (hmem a ha).2 (dvd_refl p)⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcard, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.add_div_right _ hp] at h
  omega

end E635
