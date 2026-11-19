import E635.DoubleCount

/-!
# Erdős 635 — the logarithmic weights of Theorem A

`w(o, p) = log p / log rad_{≥T}(o)` for primes `p ≥ T` dividing `o` (and `0` otherwise).
-/

namespace E635

open Finset

/-- `rad_{≥T}(n)`: the product of the primes `p ≥ T` dividing `n` (`1` if there are none). -/
def radT (T n : ℕ) : ℕ := ∏ p ∈ lines T n, p

theorem radT_pos (T n : ℕ) : 0 < radT T n :=
  prod_pos (fun p hp => (mem_lines.mp hp).2.1.pos)

theorem le_radT {T n p : ℕ} (hp : p ∈ lines T n) : p ≤ radT T n :=
  Nat.le_of_dvd (radT_pos T n) (dvd_prod_of_mem _ hp)

theorem radT_le {T n : ℕ} (hn : n ≠ 0) : radT T n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    (prod_primes_dvd n (fun p hp => (mem_lines.mp hp).2.1.prime)
      (fun p hp => (mem_lines.mp hp).1.1))

theorem log_radT (T n : ℕ) : Real.log (radT T n) = ∑ p ∈ lines T n, Real.log p := by
  unfold radT
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (mem_lines.mp hp).2.1.ne_zero

/-- The weights of Theorem A. -/
noncomputable def logWeight (T o p : ℕ) : ℝ :=
  if p ∈ lines T o then Real.log p / Real.log (radT T o) else 0

theorem logWeight_nonneg (T o p : ℕ) : 0 ≤ logWeight T o p := by
  unfold logWeight
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_lines.mp h).2.1.one_lt.le
    have h2 : (1 : ℝ) ≤ radT T o := by exact_mod_cast radT_pos T o
    exact div_nonneg (Real.log_nonneg h1) (Real.log_nonneg h2)
  · exact le_refl 0

theorem isWeight_logWeight (T N : ℕ) : IsWeight T N (logWeight T) := by
  refine ⟨logWeight_nonneg T, fun o _ => ?_⟩
  unfold logWeight
  rw [sum_congr rfl (fun p hp => if_pos hp), ← sum_div, ← log_radT]
  exact div_self_le_one _

theorem logWeight_self {T p : ℕ} (hp : p.Prime) (hTp : T ≤ p) : logWeight T p p = 1 := by
  have hl : p ∈ lines T p := mem_lines.mpr ⟨⟨dvd_rfl, hp.ne_zero⟩, hp, hTp⟩
  have hr : radT T p = p := le_antisymm (radT_le hp.ne_zero) (le_radT hl)
  unfold logWeight
  rw [if_pos hl, hr]
  have : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  exact div_self this.ne'

theorem logWeight_ge {T o p : ℕ} (hp : p ∈ lines T o) {X : ℝ} (hX : (o : ℝ) ≤ X) :
    Real.log p / Real.log X ≤ logWeight T o p := by
  unfold logWeight
  rw [if_pos hp]
  obtain ⟨⟨_, ho⟩, hpr, _⟩ := mem_lines.mp hp
  have h0 := le_radT hp
  have h00 := hpr.one_lt
  have h1 : (1 : ℝ) < radT T o := by exact_mod_cast (by omega : 1 < radT T o)
  have h2 : ((radT T o : ℕ) : ℝ) ≤ X := le_trans (by exact_mod_cast radT_le ho) hX
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
    (Real.log_pos h1) (Real.log_le_log (by linarith) h2)

end E635
