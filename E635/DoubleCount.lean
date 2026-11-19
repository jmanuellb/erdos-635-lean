import E635.Lines

/-!
# Erdős 635 — the fractional double count (Lemma 2.3 of the note)

A weight system `w` (nonnegative, total weight `≤ 1` on each odd `o ≤ N` over the primes
`p ≥ T` dividing `o`) gives every even `e` the coverage
`cov(e) = ∑_{p ∣ e, p ≥ T prime} (w(e - p, p) + [e + p ≤ N] w(e + p, p))`.
For admissible `A ⊆ [1, N]` (with `t ≤ T`, `3 ≤ T`):
`|A| ≤ ⌈N/2⌉ + #{e ∈ A : e even, cov(e) < 1}`.
-/

namespace E635

open Finset

/-- Coverage of `e` by the weight system `w`. -/
noncomputable def cov (T N : ℕ) (w : ℕ → ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ p ∈ lines T e, (w (e - p) p + if e + p ≤ N then w (e + p) p else 0)

/-- `w` is a weight system: nonnegative, total `≤ 1` on each odd `o ∈ [1, N]`. -/
def IsWeight (T N : ℕ) (w : ℕ → ℕ → ℝ) : Prop :=
  (∀ o p, 0 ≤ w o p) ∧ ∀ o ∈ odds N, ∑ p ∈ lines T o, w o p ≤ 1

/-- The pairs `(n, p)` with `n ∈ s` and `p ∈ lines T n`. -/
def pairs (T N : ℕ) (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ range (N + 1)).filter (fun x => x.2 ∈ lines T x.1)

theorem mem_pairs {T N : ℕ} {s : Finset ℕ} (hs : s ⊆ Icc 1 N) {x : ℕ × ℕ} :
    x ∈ pairs T N s ↔ x.1 ∈ s ∧ x.2 ∈ lines T x.1 := by
  unfold pairs
  rw [mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    have hN := (mem_Icc.mp (hs h1)).2
    have h := (mem_lines.mp h3).1
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) h.1
    omega

theorem sum_pairs {T N : ℕ} {s : Finset ℕ} (hs : s ⊆ Icc 1 N) (f : ℕ × ℕ → ℝ) :
    ∑ x ∈ pairs T N s, f x = ∑ n ∈ s, ∑ p ∈ lines T n, f (n, p) :=
  sum_finset_product _ _ _ (fun _ => mem_pairs hs)

theorem cov_nonneg {T N : ℕ} {w : ℕ → ℕ → ℝ} (hw : ∀ o p, 0 ≤ w o p) (e : ℕ) :
    0 ≤ cov T N w e := by
  unfold cov
  refine sum_nonneg (fun p _ => add_nonneg (hw _ _) ?_)
  split_ifs
  · exact hw _ _
  · exact le_refl 0

theorem line_facts {t T e p : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) (hp : p ∈ lines T e) :
    p ∣ e ∧ e ≠ 0 ∧ 0 < p ∧ t ≤ p ∧ p % 2 = 1 ∧ p.Prime ∧ T ≤ p := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_lines.mp hp
  exact ⟨h1, h2, h3.pos, le_trans htT h4, prime_mod_two h3 (le_trans hT h4), h3, h4⟩

theorem pair_facts {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) {e p : ℕ} (hx : (e, p) ∈ pairs T N (A.filter (fun x => x ∉ odds N))) :
    e ∈ A ∧ 1 ≤ e ∧ e ≤ N ∧ e % 2 = 0 ∧ p ∣ e ∧ 0 < p ∧ t ≤ p ∧ p % 2 = 1 ∧
      2 * p ≤ e ∧ p.Prime ∧ T ≤ p := by
  have hSI : A.filter (fun x => x ∉ odds N) ⊆ Icc 1 N := (filter_subset _ _).trans hA
  obtain ⟨he, hp⟩ := (mem_pairs hSI).mp hx
  rw [mem_filter] at he
  have h := mem_Icc.mp (hA he.1)
  have he2 : e % 2 = 0 := by
    by_contra hc
    exact he.2 (mem_odds.mpr ⟨h.1, h.2, by omega⟩)
  obtain ⟨f1, _, f3, f4, f5, f6, f7⟩ := line_facts htT hT hp
  exact ⟨he.1, h.1, h.2, he2, f1, f3, f4, f5, two_mul_le he2 f5 f1 (by omega), f6, f7⟩

/-- The double count: the coverage of the even elements of `A` is paid for by the odd numbers
of `[1, N]` outside `A`. -/
theorem sum_cov_le {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) {w : ℕ → ℕ → ℝ}
    (hw : IsWeight T N w) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hgood : Good t A) :
    ∑ e ∈ A.filter (fun x => x ∉ odds N), cov T N w e ≤ ((odds N \ A).card : ℝ) := by
  have hSI : A.filter (fun x => x ∉ odds N) ⊆ Icc 1 N := (filter_subset _ _).trans hA
  have hOI : odds N \ A ⊆ Icc 1 N := sdiff_subset.trans (odds_subset N)
  -- split the coverage into the `e - p` part and the `e + p` part
  have hsplit : ∑ e ∈ A.filter (fun x => x ∉ odds N), cov T N w e =
      ∑ x ∈ pairs T N (A.filter (fun x => x ∉ odds N)), w (x.1 - x.2) x.2 +
      ∑ x ∈ (pairs T N (A.filter (fun x => x ∉ odds N))).filter (fun x => x.1 + x.2 ≤ N),
        w (x.1 + x.2) x.2 := by
    rw [sum_filter, sum_pairs hSI, sum_pairs hSI, ← sum_add_distrib]
    refine sum_congr rfl (fun e _ => ?_)
    unfold cov
    rw [sum_add_distrib]
  have hinjX : Set.InjOn (fun x : ℕ × ℕ => (x.1 - x.2, x.2))
      ↑(pairs T N (A.filter (fun x => x ∉ odds N))) := by
    rintro ⟨e, p⟩ hx ⟨e', p'⟩ hy hxy
    have hx' := pair_facts htT hT hA (mem_coe.mp hx)
    have hy' := pair_facts htT hT hA (mem_coe.mp hy)
    simp only [Prod.mk.injEq] at hxy ⊢
    omega
  have hinjY : Set.InjOn (fun x : ℕ × ℕ => (x.1 + x.2, x.2))
      ↑((pairs T N (A.filter (fun x => x ∉ odds N))).filter (fun x => x.1 + x.2 ≤ N)) := by
    rintro ⟨e, p⟩ _ ⟨e', p'⟩ _ hxy
    simp only [Prod.mk.injEq] at hxy ⊢
    omega
  rw [hsplit, ← sum_image (f := fun y : ℕ × ℕ => w y.1 y.2) hinjX,
    ← sum_image (f := fun y : ℕ × ℕ => w y.1 y.2) hinjY, ← sum_union]
  · calc _ ≤ ∑ y ∈ pairs T N (odds N \ A), w y.1 y.2 := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => hw.1 _ _)
          intro y hy
          rw [mem_union] at hy
          rw [mem_pairs hOI, mem_sdiff, mem_odds]
          rcases hy with hy | hy
          · obtain ⟨⟨e, p⟩, hx, rfl⟩ := mem_image.mp hy
            obtain ⟨heA, he1, heN, he2, hpe, hp0, hpt, hp2, h2p, hpr, hTp⟩ :=
              pair_facts htT hT hA hx
            refine ⟨⟨⟨by omega, by omega, by omega⟩,
              sub_not_mem hgood heA hp0 hpt hpe (by omega)⟩, ?_⟩
            refine mem_lines.mpr ⟨⟨?_, by omega⟩, hpr, hTp⟩
            rw [show e = p + (e - p) by omega] at hpe
            exact (Nat.dvd_add_right (dvd_refl p)).mp hpe
          · obtain ⟨⟨e, p⟩, hx, rfl⟩ := mem_image.mp hy
            rw [mem_filter] at hx
            obtain ⟨heA, he1, heN, he2, hpe, hp0, hpt, hp2, h2p, hpr, hTp⟩ :=
              pair_facts htT hT hA hx.1
            have hle : e + p ≤ N := hx.2
            refine ⟨⟨⟨by omega, by omega, by omega⟩, add_not_mem hgood heA hp0 hpt hpe⟩, ?_⟩
            exact mem_lines.mpr ⟨⟨dvd_add hpe dvd_rfl, by omega⟩, hpr, hTp⟩
      _ = ∑ o ∈ odds N \ A, ∑ p ∈ lines T o, w o p := sum_pairs hOI _
      _ ≤ ∑ o ∈ odds N \ A, (1 : ℝ) :=
          sum_le_sum (fun o ho => hw.2 o (mem_sdiff.mp ho).1)
      _ = ((odds N \ A).card : ℝ) := by simp
  · -- the two images are disjoint: this is the "one per line" lemma
    rw [disjoint_left]
    intro y hy hy'
    obtain ⟨⟨e, p⟩, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨⟨e', p'⟩, hx', heq⟩ := mem_image.mp hy'
    rw [mem_filter] at hx'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨heq1, rfl⟩ := heq
    obtain ⟨heA, he1, heN, he2, hpe, hp0, hpt, hp2, h2p, hpr, hTp⟩ := pair_facts htT hT hA hx
    obtain ⟨heA', he1', heN', he2', hpe', -⟩ := pair_facts htT hT hA hx'.1
    refine one_per_line hgood (o := e' + p') (p := p') (by omega) hp0 hpt
      (dvd_add hpe' dvd_rfl) (by omega) ⟨?_, ?_⟩
    · rwa [show e' + p' - p' = e' by omega]
    · rwa [show e' + p' + p' = e by omega]

/-- **Lemma 2.3 of the note (finite form).** For every weight system `w`, every admissible
`A ⊆ [1, N]` has `|A| ≤ ⌈N/2⌉ + #{e ∈ A : e even, cov_w(e) < 1}`. -/
theorem card_le_of_weight {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) {w : ℕ → ℕ → ℝ}
    (hw : IsWeight T N w) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hgood : Good t A) :
    A.card ≤ (N + 1) / 2 + (A.filter (fun e => e % 2 = 0 ∧ cov T N w e < 1)).card := by
  have h1 := sum_cov_le htT hT hw hA hgood
  have h2 : ((A.filter (fun x => x ∉ odds N)).card : ℝ) ≤
      ∑ e ∈ A.filter (fun x => x ∉ odds N), cov T N w e +
        (((A.filter (fun x => x ∉ odds N)).filter (fun e => cov T N w e < 1)).card : ℝ) := by
    rw [card_filter, card_eq_sum_ones, Nat.cast_sum, Nat.cast_sum, ← sum_add_distrib]
    refine sum_le_sum (fun e _ => ?_)
    have := cov_nonneg hw.1 (T := T) (N := N) e
    split_ifs with h
    · push_cast
      linarith
    · push_cast
      push_neg at h
      linarith
  have e1 : A.card = (A.filter (fun x => x ∈ odds N)).card +
      (A.filter (fun x => x ∉ odds N)).card :=
    (card_filter_add_card_filter_not _).symm
  have e2 : (odds N \ A).card + (A.filter (fun x => x ∈ odds N)).card = (N + 1) / 2 := by
    rw [filter_mem_eq_inter, inter_comm, card_sdiff_add_card_inter, card_odds]
  have e3 : ((A.filter (fun x => x ∉ odds N)).filter (fun e => cov T N w e < 1)).card ≤
      (A.filter (fun e => e % 2 = 0 ∧ cov T N w e < 1)).card := by
    apply card_le_card
    intro e he
    rw [mem_filter, mem_filter] at he
    rw [mem_filter]
    refine ⟨he.1.1, ?_, he.2⟩
    have h := mem_Icc.mp (hA he.1.1)
    by_contra hc
    exact he.1.2 (mem_odds.mpr ⟨h.1, h.2, by omega⟩)
  have h4 : (A.filter (fun x => x ∉ odds N)).card ≤ (odds N \ A).card +
      ((A.filter (fun x => x ∉ odds N)).filter (fun e => cov T N w e < 1)).card := by
    have h3 : ((A.filter (fun x => x ∉ odds N)).card : ℝ) ≤ ((odds N \ A).card : ℝ) +
        (((A.filter (fun x => x ∉ odds N)).filter (fun e => cov T N w e < 1)).card : ℝ) := by
      linarith
    exact_mod_cast h3
  omega

/-- The set of "bad" even numbers: `{e ∈ [1, N] : e even, cov_w(e) < 1}`. -/
noncomputable def badSet (T N : ℕ) (w : ℕ → ℕ → ℝ) : Finset ℕ :=
  (Icc 1 N).filter (fun e => e % 2 = 0 ∧ cov T N w e < 1)

/-- `|A| ≤ ⌈N/2⌉ + |Bad_w|` for every admissible `A ⊆ [1, N]`. -/
theorem card_le_of_weight' {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T) {w : ℕ → ℕ → ℝ}
    (hw : IsWeight T N w) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hgood : Good t A) :
    A.card ≤ (N + 1) / 2 + (badSet T N w).card := by
  have h := card_le_of_weight htT hT hw hA hgood
  have : (A.filter (fun e => e % 2 = 0 ∧ cov T N w e < 1)).card ≤ (badSet T N w).card :=
    card_le_card (filter_subset_filter _ hA)
  omega

/-- The same bound for the extremal function `maxAdmissible`. -/
theorem maxAdmissible_le_of_weight {t T N : ℕ} (htT : t ≤ T) (hT : 3 ≤ T)
    {w : ℕ → ℕ → ℝ} (hw : IsWeight T N w) :
    maxAdmissible t N ≤ (N + 1) / 2 + (badSet T N w).card := by
  obtain ⟨A, hA, hgood, hcard⟩ := exists_card_eq_maxAdmissible t N
  rw [← hcard]
  exact card_le_of_weight' htT hT hw hA hgood

end E635
