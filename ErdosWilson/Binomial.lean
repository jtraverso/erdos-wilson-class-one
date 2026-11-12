/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Estimates for the binomial distribution `Bin(N, 1/2)`

`bp N i = C(N, i) / 2 ^ N` is the point probability, `tl N k = P(Bin(N, 1/2) ≥ k)` the upper tail
and `tl2 N k = ∑_{i ≥ k} bp N i ^ 2`.

* `hazard`: near the mean, the point probability is small compared to the tail beyond it:
  `L * bp N j ≤ 2 * tl N (j + 1)` as long as `j + L` stays below `(1 + x / 2) N / 2` with
  `2 L x ≤ 1`.
* `tail_small`: beyond `(1 + δ) N / 2` the tail is `o(1 / N)`.
* `exists_good`: for every `ε > 0` and all large `N` there is a threshold `k` at which the bound
  of the second-moment argument (see `ErdosWilson.Count`) is at most `ε`.
-/

@[expose] public section

open Finset Filter

namespace ErdosWilson

/-- The point probability `P(Bin(N, 1/2) = i) = C(N, i) / 2 ^ N`. -/
noncomputable def bp (N i : ℕ) : ℝ := (N.choose i : ℝ) / 2 ^ N

/-- The upper tail `P(Bin(N, 1/2) ≥ k)`. -/
noncomputable def tl (N k : ℕ) : ℝ := ∑ i ∈ range (N + 1), if k ≤ i then bp N i else 0

/-- `∑_{i ≥ k} P(Bin(N, 1/2) = i) ^ 2`. -/
noncomputable def tl2 (N k : ℕ) : ℝ := ∑ i ∈ range (N + 1), if k ≤ i then bp N i ^ 2 else 0

theorem bp_nonneg (N i : ℕ) : 0 ≤ bp N i := by unfold bp; positivity

theorem bp_eq_zero {N i : ℕ} (h : N < i) : bp N i = 0 := by
  simp [bp, Nat.choose_eq_zero_of_lt h]

theorem bp_le_one (N i : ℕ) : bp N i ≤ 1 := by
  unfold bp
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.choose_le_two_pow N i

theorem sum_bp (N : ℕ) : ∑ i ∈ range (N + 1), bp N i = 1 := by
  unfold bp
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

theorem tl_nonneg (N k : ℕ) : 0 ≤ tl N k :=
  sum_nonneg fun i _ => by split_ifs <;> simp [bp_nonneg]

theorem tl2_nonneg (N k : ℕ) : 0 ≤ tl2 N k :=
  sum_nonneg fun i _ => by split_ifs <;> positivity

theorem tl_zero (N : ℕ) : tl N 0 = 1 := by simp [tl, sum_bp]

theorem tl_eq_zero {N k : ℕ} (h : N < k) : tl N k = 0 :=
  sum_eq_zero fun i hi => by
    have : ¬ k ≤ i := by simp at hi; omega
    simp [this]

theorem tl_succ (N k : ℕ) : tl N k = bp N k + tl N (k + 1) := by
  have h : ∀ i, (if k ≤ i then bp N i else 0) =
      (if k = i then bp N i else 0) + (if k + 1 ≤ i then bp N i else 0) := by
    intro i
    by_cases h1 : k = i
    · subst h1; simp
    · by_cases h2 : k ≤ i
      · have : k + 1 ≤ i := by omega
        simp [h1, h2, this]
      · have : ¬ k + 1 ≤ i := by omega
        simp [h1, h2, this]
  unfold tl
  rw [sum_congr rfl (fun i _ => h i), sum_add_distrib, sum_ite_eq]
  congr 1
  split_ifs with hk
  · rfl
  · exact (bp_eq_zero (by simp at hk; omega)).symm

theorem bp_le_tl (N k : ℕ) : bp N k ≤ tl N k := by
  rw [tl_succ N k]; linarith [tl_nonneg N (k + 1)]

theorem tl_antitone (N : ℕ) : Antitone (tl N) :=
  antitone_nat_of_succ_le fun k => by rw [tl_succ N k]; linarith [bp_nonneg N k]

theorem tl_iter (N a L : ℕ) : tl N a = ∑ l ∈ range L, bp N (a + l) + tl N (a + L) := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, ih, tl_succ N (a + L), ← add_assoc a L 1]; ring

theorem bp_succ_mul (N m : ℕ) : bp N (m + 1) * (m + 1) = bp N m * ((N : ℝ) - m) := by
  by_cases h : m ≤ N
  · have h' : ((N.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((N.choose m * (N - m) : ℕ) : ℝ) := by
      rw [Nat.choose_succ_right_eq]
    push_cast [Nat.cast_sub h] at h'
    unfold bp
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, h']
  · rw [bp_eq_zero (by omega), bp_eq_zero (by omega)]; ring

/-- **Hazard bound.** Near (and below) the mean the point probability at `j` is at most
`2 / L` times the tail beyond `j`. -/
theorem hazard {N L j : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hL : 2 * L * x ≤ 1)
    (hj : 2 * ((j : ℝ) + L + 1) ≤ (1 + x / 2) * N) : (L : ℝ) * bp N j ≤ 2 * tl N (j + 1) := by
  have step : ∀ m : ℕ, m ≤ j + L → (1 - x) * bp N m ≤ bp N (m + 1) := by
    intro m hm
    have hm' : 2 * ((m : ℝ) + 1) ≤ (1 + x / 2) * N := by
      have : (m : ℝ) ≤ j + L := by exact_mod_cast hm
      linarith
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : (1 - x) * ((m : ℝ) + 1) ≤ (N : ℝ) - m := by
      have h1 : (2 - x) * (2 * ((m : ℝ) + 1)) ≤ (2 - x) * ((1 + x / 2) * N) :=
        mul_le_mul_of_nonneg_left hm' (by linarith)
      nlinarith [mul_nonneg (mul_nonneg hx0 hx0) hN]
    have hb := bp_succ_mul N m
    have hpos : (0 : ℝ) < m + 1 := by positivity
    have : (1 - x) * bp N m * (m + 1) ≤ bp N (m + 1) * (m + 1) := by
      calc (1 - x) * bp N m * (m + 1) = bp N m * ((1 - x) * (m + 1)) := by ring
        _ ≤ bp N m * (N - m) := mul_le_mul_of_nonneg_left key (bp_nonneg N m)
        _ = bp N (m + 1) * (m + 1) := hb.symm
    exact le_of_mul_le_mul_right this hpos
  have grow : ∀ l : ℕ, l ≤ L → (1 - x) ^ l * bp N j ≤ bp N (j + l) := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have h1 := step (j + l) (by omega)
      calc (1 - x) ^ (l + 1) * bp N j = (1 - x) * ((1 - x) ^ l * bp N j) := by ring
        _ ≤ (1 - x) * bp N (j + l) := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ ≤ bp N (j + l + 1) := h1
        _ = bp N (j + (l + 1)) := by rw [add_assoc]
  have hsum : (L : ℝ) * ((1 - x) ^ L * bp N j) ≤ tl N (j + 1) := by
    rw [tl_iter N (j + 1) L]
    have h2 : ∑ l ∈ range L, (1 - x) ^ L * bp N j ≤ ∑ l ∈ range L, bp N (j + 1 + l) := by
      apply sum_le_sum
      intro l hl
      have hl' : l + 1 ≤ L := by simp at hl; omega
      calc (1 - x) ^ L * bp N j ≤ (1 - x) ^ (l + 1) * bp N j :=
            mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) hl')
              (bp_nonneg N j)
        _ ≤ bp N (j + (l + 1)) := grow (l + 1) hl'
        _ = bp N (j + 1 + l) := by rw [add_comm l 1, add_assoc]
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    linarith [tl_nonneg N (j + 1 + L)]
  have hbern : 1 + (L : ℝ) * (-x) ≤ (1 + -x) ^ L := one_add_mul_le_pow (by linarith) L
  have hhalf : (1 : ℝ) / 2 ≤ (1 - x) ^ L := by
    rw [← sub_eq_add_neg] at hbern; linarith
  have hLb : (0 : ℝ) ≤ L * bp N j := mul_nonneg (Nat.cast_nonneg L) (bp_nonneg N j)
  calc (L : ℝ) * bp N j = 2 * ((L * bp N j) * (1 / 2)) := by ring
    _ ≤ 2 * ((L * bp N j) * (1 - x) ^ L) := by
      have := mul_le_mul_of_nonneg_left hhalf hLb
      linarith
    _ = 2 * (L * ((1 - x) ^ L * bp N j)) := by ring
    _ ≤ 2 * tl N (j + 1) := by linarith

/-- The hazard bound in the form used later: for every `η > 0` there is `δ > 0` such that, for
all large `N`, `bp N i ≤ η * tl N (i + 1)` whenever `2 i < (1 + δ) N`. -/
theorem hazard_eventually {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 2 * (i : ℝ) < (1 + δ) * N →
      bp N i ≤ η * tl N (i + 1) := by
  obtain ⟨L, hL⟩ := exists_nat_ge (2 / η + 1)
  have h2η : 0 < 2 / η := by positivity
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  refine ⟨1 / (8 * L), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((2 * (L : ℝ) + 2) * (8 * L))
    refine eventually_atTop.2 ⟨N₀, fun N hN i hi => ?_⟩
    have hN' : ((2 * L + 2) * (8 * L) : ℝ) ≤ N := hN₀.trans (by exact_mod_cast hN)
    have hx0 : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
    have hx1 : 1 / (2 * (L : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hLx : 2 * (L : ℝ) * (1 / (2 * L)) ≤ 1 := by
      rw [mul_one_div, div_self (by positivity)]
    have hj : 2 * ((i : ℝ) + L + 1) ≤ (1 + 1 / (2 * L) / 2) * N := by
      have e1 : (1 + 1 / (2 * (L : ℝ)) / 2) * N = (1 + 1 / (8 * L)) * N + N / (8 * L) := by
        field_simp; ring
      have e2 : (2 * L + 2 : ℝ) ≤ N / (8 * L) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [e1]; linarith
    have h := hazard hx0 hx1 hLx hj
    have hle : 2 / (L : ℝ) ≤ η := by
      rw [div_le_iff₀ hLpos]
      have : 2 / η ≤ L := by linarith
      rw [div_le_iff₀ hη] at this; linarith
    have htl := tl_nonneg N (i + 1)
    calc bp N i = (L * bp N i) / L := by field_simp
      _ ≤ (2 * tl N (i + 1)) / L := div_le_div_of_nonneg_right h hLpos.le
      _ = (2 / L) * tl N (i + 1) := by ring
      _ ≤ η * tl N (i + 1) := mul_le_mul_of_nonneg_right hle htl

theorem bp_succ_le {N m : ℕ} {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hm : (1 + d) * N ≤ 2 * m) :
    bp N (m + 1) ≤ (1 - d) * bp N m := by
  have hb := bp_succ_mul N m
  have hpos : (0 : ℝ) < m + 1 := by positivity
  have key : (N : ℝ) - m ≤ (1 - d) * (m + 1) := by
    rcases le_or_gt ((N : ℝ) - m) 0 with h | h
    · have : 0 ≤ (1 - d) * ((m : ℝ) + 1) := mul_nonneg (by linarith) (by positivity)
      linarith
    · have h2 : d * (m : ℝ) ≤ d * N := mul_le_mul_of_nonneg_left (by linarith) hd0
      nlinarith
  have : bp N (m + 1) * (m + 1) ≤ (1 - d) * bp N m * (m + 1) := by
    rw [hb]
    calc bp N m * (N - m) ≤ bp N m * ((1 - d) * (m + 1)) :=
          mul_le_mul_of_nonneg_left key (bp_nonneg N m)
      _ = (1 - d) * bp N m * (m + 1) := by ring
  exact le_of_mul_le_mul_right this hpos

theorem bp_geom {N m₀ : ℕ} {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hm : (1 + d) * N ≤ 2 * m₀) :
    ∀ l : ℕ, bp N (m₀ + l) ≤ (1 - d) ^ l
  | 0 => by simpa using bp_le_one N m₀
  | l + 1 => by
    have h1 : (1 + d) * N ≤ 2 * ((m₀ + l : ℕ) : ℝ) := by
      push_cast; have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      linarith
    calc bp N (m₀ + (l + 1)) = bp N (m₀ + l + 1) := by rw [add_assoc]
      _ ≤ (1 - d) * bp N (m₀ + l) := bp_succ_le hd0 hd1 h1
      _ ≤ (1 - d) * (1 - d) ^ l :=
          mul_le_mul_of_nonneg_left (bp_geom hd0 hd1 hm l) (by linarith)
      _ = (1 - d) ^ (l + 1) := by ring

theorem tl_le_geom {N m₀ i : ℕ} {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hm : (1 + d) * N ≤ 2 * m₀) (hi : m₀ ≤ i) :
    tl N i ≤ (N + 1) * (1 - d) ^ (i - m₀) := by
  unfold tl
  calc ∑ m ∈ range (N + 1), (if i ≤ m then bp N m else 0)
      ≤ ∑ m ∈ range (N + 1), (1 - d) ^ (i - m₀) := by
        apply sum_le_sum
        intro m _
        split_ifs with h
        · have h1 := bp_geom hd0 hd1 hm (m - m₀)
          rw [Nat.add_sub_cancel' (by omega)] at h1
          exact h1.trans (pow_le_pow_of_le_one (by linarith) (by linarith) (by omega))
        · exact pow_nonneg (by linarith) _
    _ = (N + 1) * (1 - d) ^ (i - m₀) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- **Tail bound.** Beyond `(1 + δ) N / 2` the tail of `Bin(N, 1/2)` is `o(1 / N)`. -/
theorem tail_small {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, (1 + δ) * N ≤ 2 * i → ((N : ℝ) + 2) * tl N i ≤ c := by
  set d := δ / 2 with hd
  have hd0 : 0 < d := by positivity
  have hd1 : d ≤ 1 := by linarith
  set a := d ^ 2 / 2 with ha
  have ha0 : 0 < a := by positivity
  set K := 36 * Real.exp d / a ^ 3 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (K / c + 1)
  refine eventually_atTop.2 ⟨N₀, fun N hN i hi => ?_⟩
  have hNr : K / c + 1 ≤ (N : ℝ) := hN₀.trans (by exact_mod_cast hN)
  have hKc : 0 < K / c := by positivity
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  -- the starting index of the geometric decay
  set m₀ := ⌈(1 + d) * N / 2⌉₊ with hm₀
  have hm₀a : (1 + d) * N ≤ 2 * (m₀ : ℝ) := by
    have := Nat.le_ceil ((1 + d) * N / 2); linarith
  have hm₀b : (m₀ : ℝ) < (1 + d) * N / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm₀i : m₀ ≤ i := by
    have : (m₀ : ℝ) < (i : ℝ) + 1 := by
      have : (1 + d) * (N : ℝ) ≤ (1 + δ) * N := by
        apply mul_le_mul_of_nonneg_right _ hNpos.le; linarith
      linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hgeo := tl_le_geom hd0.le hd1 hm₀a hm₀i
  -- exponent bookkeeping
  have hk : d * N / 2 - 1 ≤ ((i - m₀ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm₀i]
    have : (1 + 2 * d) * (N : ℝ) ≤ 2 * i := by rw [hd]; linarith
    linarith
  have hpow : (1 - d) ^ (i - m₀) ≤ Real.exp d * Real.exp (-(a * N)) := by
    calc (1 - d) ^ (i - m₀) ≤ Real.exp (-d) ^ (i - m₀) :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-d)]) _
      _ = Real.exp (-d * ((i - m₀ : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-d * (d * N / 2 - 1)) := by
          apply Real.exp_le_exp.2; nlinarith
      _ = Real.exp d * Real.exp (-(a * N)) := by rw [← Real.exp_add]; congr 1; rw [ha]; ring
  have hexp : Real.exp (-(a * N)) ≤ 6 / (a * N) ^ 3 := by
    have hpos : 0 < a * N := by positivity
    have h3 := Real.pow_div_factorial_le_exp (x := a * N) hpos.le 3
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have : (3 : ℕ).factorial = 6 := rfl
    rw [this] at h3
    push_cast at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hfin : ((N : ℝ) + 2) * tl N i ≤ K / N := by
    have h1 : ((N : ℝ) + 2) * tl N i ≤ ((N : ℝ) + 2) * ((N + 1) * (Real.exp d * (6 / (a * N) ^ 3))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine hgeo.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hpow.trans (mul_le_mul_of_nonneg_left hexp (Real.exp_pos d).le)
    refine h1.trans ?_
    rw [hK]
    have hN2 : ((N : ℝ) + 2) * (N + 1) ≤ 6 * N ^ 2 := by nlinarith
    have e : ((N : ℝ) + 2) * ((N + 1) * (Real.exp d * (6 / (a * N) ^ 3))) =
        (((N : ℝ) + 2) * (N + 1)) * (6 * Real.exp d / (a ^ 3 * N ^ 3)) := by
      field_simp
    rw [e]
    calc (((N : ℝ) + 2) * (N + 1)) * (6 * Real.exp d / (a ^ 3 * N ^ 3))
        ≤ (6 * N ^ 2) * (6 * Real.exp d / (a ^ 3 * N ^ 3)) :=
          mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = 36 * Real.exp d / a ^ 3 / N := by field_simp; ring
  refine hfin.trans ?_
  rw [div_le_iff₀ hNpos]
  have : K / c ≤ N := by linarith
  rw [div_le_iff₀ hc] at this; linarith

end ErdosWilson
