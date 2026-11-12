/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ErdosWilson.Binomial

/-!
# Choice of the degree threshold

For every `ε > 0` and all large `N` there is a threshold `k ≥ 1` with `tl N k > 0` and
`1 / (n tl_k) + bp_{k-1}^2 / (4 tl_k^2) + n^2 ∑_{i ≥ k-1} bp_i^2 ≤ ε`, where `n = N + 2`.

The threshold is the least `k` with `n * tl N k ≤ A` for a large constant `A`. Then
`n * tl N (k - 1) > A`, so `k - 1` lies below `(1 + δ) N / 2` (`tail_small`), where the hazard
bound `bp_{k-1} ≤ η tl_k` holds (`hazard_eventually`). Hence `n tl_k ∈ (A / 2, A]`, and every
point probability beyond `k - 1` is at most `η A / n`.
-/

@[expose] public section

open Finset Filter

namespace ErdosWilson

theorem exists_good {ε : ℝ} (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∃ k : ℕ, 1 ≤ k ∧ 0 < tl N k ∧
    1 / (((N : ℝ) + 2) * tl N k) + bp N (k - 1) ^ 2 / (4 * tl N k ^ 2) +
      ((N : ℝ) + 2) ^ 2 * tl2 N (k - 1) ≤ ε := by
  set A : ℝ := max 1 (4 / ε) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA2 : 4 / ε ≤ A := le_max_right _ _
  have hA0 : 0 < A := by linarith
  have hεA : 4 ≤ ε * A := by
    have h1 := mul_le_mul_of_nonneg_left hA2 hε.le
    have h2 : ε * (4 / ε) = 4 := by field_simp
    linarith
  set η : ℝ := min 1 (ε / (8 * A ^ 2)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ ε / (8 * A ^ 2) := min_le_right _ _
  obtain ⟨δ, hδ0, hδ1, hhaz⟩ := hazard_eventually hη0
  have htail := tail_small hδ0 hδ1 hη0
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge A
  filter_upwards [hhaz, htail, eventually_ge_atTop N₀] with N hN1 hN2 hN3
  set n : ℝ := (N : ℝ) + 2 with hn
  have hn0 : 0 < n := by positivity
  have hnA : A < n := by
    have : A ≤ (N : ℝ) := hN₀.trans (by exact_mod_cast hN3)
    linarith
  have hex : ∃ j, n * tl N j ≤ A := ⟨N + 1, by rw [tl_eq_zero (by omega)]; linarith⟩
  classical
  set k := Nat.find hex with hk
  have hkA : n * tl N k ≤ A := Nat.find_spec hex
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [h0, tl_zero] at hkA
    linarith
  have hβ : A < n * tl N (k - 1) := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    push Not at this
    exact this
  have hrange : 2 * ((k - 1 : ℕ) : ℝ) < (1 + δ) * N := by
    by_contra h
    push Not at h
    have := hN2 (k - 1) h
    linarith
  have hkk : k - 1 + 1 = k := by omega
  have haz : bp N (k - 1) ≤ η * tl N k := by
    have := hN1 (k - 1) hrange
    rwa [hkk] at this
  have hrec : tl N (k - 1) = bp N (k - 1) + tl N k := by
    have := tl_succ N (k - 1)
    rwa [hkk] at this
  have htk0 := tl_nonneg N k
  have hβ2 : n * tl N (k - 1) ≤ 2 * (n * tl N k) := by
    rw [hrec]
    have : bp N (k - 1) ≤ tl N k := haz.trans (by nlinarith)
    nlinarith
  have hα : A / 2 < n * tl N k := by linarith
  have hαpos : 0 < n * tl N k := by linarith
  have htk : 0 < tl N k := by
    by_contra h
    push Not at h
    have : tl N k = 0 := le_antisymm h htk0
    rw [this, mul_zero] at hαpos
    exact lt_irrefl 0 hαpos
  refine ⟨k, hk1, htk, ?_⟩
  -- first term
  have t1 : 1 / (n * tl N k) ≤ ε / 2 := by
    rw [div_le_iff₀ hαpos]
    nlinarith [mul_lt_mul_of_pos_left hα hε]
  -- second term
  have t2 : bp N (k - 1) ^ 2 / (4 * tl N k ^ 2) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hb0 := bp_nonneg N (k - 1)
    have h1 : bp N (k - 1) ^ 2 ≤ (η * tl N k) ^ 2 := pow_le_pow_left₀ hb0 haz 2
    have hη3 : η ^ 2 ≤ ε := by
      have h2 : η ^ 2 ≤ η := by nlinarith
      have h3 : ε / (8 * A ^ 2) ≤ ε := div_le_self hε.le (by nlinarith)
      linarith
    have h4 : (η * tl N k) ^ 2 = η ^ 2 * tl N k ^ 2 := by ring
    rw [h4] at h1
    have h5 : η ^ 2 * tl N k ^ 2 ≤ ε * tl N k ^ 2 :=
      mul_le_mul_of_nonneg_right hη3 (sq_nonneg _)
    linarith
  -- third term
  have hpt : ∀ i ∈ range (N + 1), k - 1 ≤ i → n * bp N i ≤ η * A := by
    intro i _ hi
    by_cases hr : 2 * (i : ℝ) < (1 + δ) * N
    · have h1 := hN1 i hr
      have h2 : tl N (i + 1) ≤ tl N k := tl_antitone N (by omega)
      calc n * bp N i ≤ n * (η * tl N k) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hη0.le)) hn0.le
        _ = η * (n * tl N k) := by ring
        _ ≤ η * A := mul_le_mul_of_nonneg_left hkA hη0.le
    · push Not at hr
      have h3 := hN2 i hr
      calc n * bp N i ≤ n * tl N i := mul_le_mul_of_nonneg_left (bp_le_tl N i) hn0.le
        _ ≤ η := h3
        _ ≤ η * A := le_mul_of_one_le_right hη0.le hA1
  have t3 : n ^ 2 * tl2 N (k - 1) ≤ ε / 4 := by
    have h1 : n ^ 2 * tl2 N (k - 1) ≤ (η * A) * (n * tl N (k - 1)) := by
      unfold tl2 tl
      simp only [Finset.mul_sum]
      apply sum_le_sum
      intro i hi
      split_ifs with h
      · have := hpt i hi h
        have hb := bp_nonneg N i
        calc n ^ 2 * bp N i ^ 2 = (n * bp N i) * (n * bp N i) := by ring
          _ ≤ (η * A) * (n * bp N i) := mul_le_mul_of_nonneg_right this (by positivity)
      · simp
    have h2 : (η * A) * (n * tl N (k - 1)) ≤ (η * A) * (2 * A) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h3 : (η * A) * (2 * A) ≤ ε / 4 := by
      have h4 : η * (2 * A ^ 2) ≤ ε / (8 * A ^ 2) * (2 * A ^ 2) :=
        mul_le_mul_of_nonneg_right hη2 (by positivity)
      have e : ε / (8 * A ^ 2) * (2 * A ^ 2) = ε / 4 := by field_simp; ring
      nlinarith
    linarith
  linarith

end ErdosWilson
