import E635.LowerBound

/-!
# Erdős 635 — the "one per line" lemma

For an odd `o`, a divisor `p ≥ t` of `o` with `p < o`: the numbers `o - p` and `o + p` are
consecutive multiples of `2p`, so an admissible set contains at most one of them.
Also: an element `e` of an admissible set excludes `e - p` and `e + p` whenever `p ≥ t`, `p ∣ e`.
-/

namespace E635

open Finset

/-- The primes `p ≥ T` dividing `n` (empty for `n = 0`). -/
def lines (T n : ℕ) : Finset ℕ := n.divisors.filter (fun p => p.Prime ∧ T ≤ p)

theorem mem_lines {T n p : ℕ} : p ∈ lines T n ↔ (p ∣ n ∧ n ≠ 0) ∧ p.Prime ∧ T ≤ p := by
  unfold lines
  rw [mem_filter, Nat.mem_divisors]

theorem mem_odds {N x : ℕ} : x ∈ odds N ↔ 1 ≤ x ∧ x ≤ N ∧ x % 2 = 1 := by
  unfold odds
  rw [mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_range] at hk
    omega
  · intro h
    exact ⟨x / 2, by rw [mem_range]; omega, by omega⟩

/-- **One per line.** -/
theorem one_per_line {t : ℕ} {A : Finset ℕ} (hgood : Good t A) {o p : ℕ}
    (ho : o % 2 = 1) (hp : 0 < p) (hpt : t ≤ p) (hpo : p ∣ o) (hlt : p < o) :
    ¬ (o - p ∈ A ∧ o + p ∈ A) := by
  rintro ⟨h1, h2⟩
  obtain ⟨q, hq⟩ := hpo
  have hq2 : q % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · exfalso
      have : 2 ∣ o := hq ▸ Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) p
      omega
    · exact h
  have hd : (o + p) - (o - p) = 2 * p := by omega
  refine hgood _ h1 _ h2 (by omega) (by omega) ?_
  rw [hd]
  refine ⟨q / 2 + 1, ?_⟩
  have hq' : q = 2 * (q / 2) + 1 := by omega
  rw [hq, hq']
  ring

theorem sub_not_mem {t : ℕ} {A : Finset ℕ} (hgood : Good t A) {e p : ℕ} (he : e ∈ A)
    (hp : 0 < p) (hpt : t ≤ p) (hpe : p ∣ e) (hle : p ≤ e) : e - p ∉ A := by
  intro h
  refine hgood _ h _ he (by omega) (by omega) ?_
  rw [show e - (e - p) = p by omega]
  exact hpe

theorem add_not_mem {t : ℕ} {A : Finset ℕ} (hgood : Good t A) {e p : ℕ} (he : e ∈ A)
    (hp : 0 < p) (hpt : t ≤ p) (hpe : p ∣ e) : e + p ∉ A := by
  intro h
  refine hgood _ he _ h (by omega) (by omega) ?_
  rw [show e + p - e = p by omega]
  exact dvd_add hpe dvd_rfl

/-- An even multiple `e > 0` of an odd `p` satisfies `2p ≤ e`. -/
theorem two_mul_le {e p : ℕ} (he : e % 2 = 0) (hp : p % 2 = 1) (hpe : p ∣ e) (he0 : 0 < e) :
    2 * p ≤ e := by
  obtain ⟨k, rfl⟩ := hpe
  have hk : k % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · exact h
    · exfalso
      rw [Nat.mul_mod, hp, h] at he
      simp at he
  have hk0 : k ≠ 0 := by rintro rfl; simp at he0
  have hk2 : 2 ≤ k := by omega
  calc 2 * p = p * 2 := mul_comm _ _
    _ ≤ p * k := Nat.mul_le_mul_left p hk2

/-- Primes `≥ 3` are odd. -/
theorem prime_mod_two {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : p % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h)
    omega
  · exact h

end E635
