/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ErdosWilson.Count
public import ErdosWilson.Asymp
public import Fournier.Basic

/-!
# Almost every graph has a unique vertex of maximum degree, hence is of class one

Graphs on `Fin (N + 2)`, all `2 ^ C(N + 2, 2)` equally likely, `n = N + 2`. Fix a threshold
`k ≥ 1` and let `X(G)` be the number of vertices of degree at least `k`.

* Second moment (`card_none_ge_le`): `P(X = 0) ≤ 1 / (n tl_k) + bp_{k-1}^2 / (4 tl_k^2)`, from
  `E X = n P₁`, `E X^2 = n P₁ + n (n - 1) P₂` with `P₁ = (tl_k + tl_{k-1}) / 2` and
  `P₂ = (tl_k^2 + tl_{k-1}^2) / 2` (`sum_degrees`).
* If two vertices share the maximum degree and `X ≠ 0`, then two distinct vertices have the same
  degree, at least `k`; for a fixed pair this has probability at most `tl2 (k - 1)`.

So `P(two vertices of maximum degree) ≤ 1/(n tl_k) + bp_{k-1}^2/(4 tl_k^2) + n^2 tl2 (k-1)`
(`tie_le`), which tends to `0` for a suitable `k` (`exists_good`). A graph whose maximum degree
is attained only once is of class one by Fournier's theorem (`FournierLib.fournier`, PALOMAR-
2026-11-08-000009): its vertices of maximum degree induce a graph on at most one vertex.
-/

@[expose] public section

open Finset SimpleGraph Filter Topology

namespace ErdosWilson

/-- **Fournier's theorem, special case.** A graph with at most one vertex of maximum degree is
of class one. -/
theorem colorable_of_subsingleton {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : {v | G.degree v = G.maxDegree}.Subsingleton) :
    G.lineGraph.Colorable G.maxDegree := by
  apply FournierLib.fournier G
  have e : G.induce {v | G.degree v = G.maxDegree} = ⊥ := by
    ext a b
    simp only [comap_adj, Function.Embedding.coe_subtype, bot_adj, iff_false]
    intro hadj
    exact G.ne_of_adj hadj (h a.2 b.2)
  rw [e]
  exact isAcyclic_bot

open Classical

/-- `[k ≤ i]` as a real number. -/
noncomputable def ind (k i : ℕ) : ℝ := if k ≤ i then 1 else 0

theorem ind_nonneg (k i : ℕ) : 0 ≤ ind k i := by unfold ind; split_ifs <;> norm_num

theorem ind_le_one (k i : ℕ) : ind k i ≤ 1 := by unfold ind; split_ifs <;> norm_num

theorem ind_succ {k : ℕ} (hk : 1 ≤ k) (i : ℕ) : ind k (i + 1) = ind (k - 1) i := by
  unfold ind
  by_cases h : k - 1 ≤ i
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem ind_mono {k : ℕ} (i : ℕ) : ind k i ≤ ind (k - 1) i := by
  unfold ind
  by_cases h : k ≤ i
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h]; split_ifs <;> norm_num

theorem sum_bp_ind (N k : ℕ) : ∑ i ∈ range (N + 1), bp N i * ind k i = tl N k := by
  unfold tl ind
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem sum_sum_bp_left (N : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), bp N i * bp N j * g i =
      ∑ i ∈ range (N + 1), bp N i * g i := by
  apply sum_congr rfl
  intro i _
  have : ∑ j ∈ range (N + 1), bp N i * bp N j * g i =
      (bp N i * g i) * ∑ j ∈ range (N + 1), bp N j := by
    rw [mul_sum]; apply sum_congr rfl; intro j _; ring
  rw [this, sum_bp, mul_one]

theorem sum_sum_bp_prod (N : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), bp N i * bp N j * (g i * g j) =
      (∑ i ∈ range (N + 1), bp N i * g i) ^ 2 := by
  rw [sq, sum_mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  ring

variable {N : ℕ}

/-- **Joint law of two degrees**, in terms of the degrees. -/
theorem sum_degrees {u v : Fin (N + 2)} (h : u ≠ v) (f : ℕ → ℕ → ℝ) :
    ∑ G : SimpleGraph (Fin (N + 2)), f (G.degree u) (G.degree v) =
      2 ^ (N + 2).choose 2 * ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        bp N i * bp N j * ((f i j + f (i + 1) (j + 1)) / 2) := by
  have e : ∀ G : SimpleGraph (Fin (N + 2)), f (G.degree u) (G.degree v) =
      (fun i j (c : Bool) => f (i + if c then 1 else 0) (j + if c then 1 else 0))
        (part G u v u).card (part G u v v).card (decide (G.Adj u v)) := by
    intro G
    rw [degree_left G h, degree_right G h]
    by_cases hG : G.Adj u v <;> simp [hG]
  rw [sum_congr rfl (fun G _ => e G),
    sum_graphs h (fun i j (c : Bool) => f (i + if c then 1 else 0) (j + if c then 1 else 0))]
  simp

theorem sum_ind_degree (w : Fin (N + 2)) {k : ℕ} (hk : 1 ≤ k) :
    ∑ G : SimpleGraph (Fin (N + 2)), ind k (G.degree w) =
      2 ^ (N + 2).choose 2 * ((tl N k + tl N (k - 1)) / 2) := by
  obtain ⟨w', hw'⟩ := exists_ne w
  rw [sum_degrees (Ne.symm hw') (fun i _ => ind k i)]
  rw [sum_sum_bp_left N (fun i => (ind k i + ind k (i + 1)) / 2)]
  congr 1
  rw [← sum_bp_ind N k, ← sum_bp_ind N (k - 1), ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro i _
  rw [ind_succ hk]
  ring

theorem sum_ind_pair {u v : Fin (N + 2)} (h : u ≠ v) {k : ℕ} (hk : 1 ≤ k) :
    ∑ G : SimpleGraph (Fin (N + 2)), ind k (G.degree u) * ind k (G.degree v) =
      2 ^ (N + 2).choose 2 * ((tl N k ^ 2 + tl N (k - 1) ^ 2) / 2) := by
  rw [sum_degrees h (fun i j => ind k i * ind k j)]
  congr 1
  rw [← sum_bp_ind N k, ← sum_bp_ind N (k - 1), ← sum_sum_bp_prod, ← sum_sum_bp_prod,
    ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro i _
  rw [← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro j _
  rw [ind_succ hk, ind_succ hk]
  ring

theorem sum_eq_pair_le {u v : Fin (N + 2)} (h : u ≠ v) (k : ℕ) :
    ∑ G : SimpleGraph (Fin (N + 2)),
        (if G.degree u = G.degree v then ind k (G.degree u) else 0) ≤
      2 ^ (N + 2).choose 2 * tl2 N (k - 1) := by
  rw [sum_degrees h (fun i j => if i = j then ind k i else 0)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), bp N i * bp N j *
        (((if i = j then ind k i else 0) + (if i + 1 = j + 1 then ind k (i + 1) else 0)) / 2)
      ≤ ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
          bp N i * bp N j * (if i = j then ind (k - 1) i else 0) := by
        apply sum_le_sum; intro i _
        apply sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (bp_nonneg N i) (bp_nonneg N j))
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, if_pos rfl, if_pos rfl]
          have h1 := ind_mono (k := k) i
          have h2 := ind_mono (k := k) (i + 1)
          have h3 : ind (k - 1) (i + 1) ≤ 1 := ind_le_one _ _
          by_cases hk : 1 ≤ k
          · rw [ind_succ hk]; linarith
          · have : k = 0 := by omega
            subst this
            simp [ind]
        · simp [hij]
    _ = tl2 N (k - 1) := by
        unfold tl2
        apply sum_congr rfl
        intro i hi
        simp only [mul_ite, mul_zero]
        rw [sum_ite_eq, if_pos hi]
        unfold ind
        split_ifs <;> ring

/-- `P₂ - P₁²` and the second moment, as an algebraic inequality. -/
theorem cheb_alg {n a b z : ℝ} (hn : 1 ≤ n) (ha : 0 < a) (hab : a ≤ b)
    (h : z * (n * ((a + b) / 2)) ^ 2 ≤
      n * ((a + b) / 2) + n * (n - 1) * ((a ^ 2 + b ^ 2) / 2) - n ^ 2 * ((a + b) / 2) ^ 2) :
    z ≤ 1 / (n * a) + (b - a) ^ 2 / (4 * a ^ 2) := by
  set p := (a + b) / 2 with hp
  have hpa : a ≤ p := by rw [hp]; linarith
  have hp0 : 0 < p := by linarith
  have hn0 : 0 < n := by linarith
  have hvar : (a ^ 2 + b ^ 2) / 2 - p ^ 2 = (b - a) ^ 2 / 4 := by rw [hp]; ring
  have h1 : n * (n - 1) * ((a ^ 2 + b ^ 2) / 2) ≤ n ^ 2 * ((a ^ 2 + b ^ 2) / 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  have h2 : z * (n * p) ^ 2 ≤ n * p + n ^ 2 * ((b - a) ^ 2 / 4) := by
    have : n ^ 2 * ((a ^ 2 + b ^ 2) / 2) - n ^ 2 * p ^ 2 = n ^ 2 * ((b - a) ^ 2 / 4) := by
      rw [← hvar]; ring
    linarith
  have hnp : 0 < (n * p) ^ 2 := by positivity
  have h3 : z ≤ (n * p + n ^ 2 * ((b - a) ^ 2 / 4)) / (n * p) ^ 2 := by
    rw [le_div_iff₀ hnp]; exact h2
  have e : (n * p + n ^ 2 * ((b - a) ^ 2 / 4)) / (n * p) ^ 2 =
      1 / (n * p) + (b - a) ^ 2 / (4 * p ^ 2) := by
    field_simp
  rw [e] at h3
  have h4 : 1 / (n * p) ≤ 1 / (n * a) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hpa hn0.le)
  have h5 : (b - a) ^ 2 / (4 * p ^ 2) ≤ (b - a) ^ 2 / (4 * a ^ 2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have : a ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ ha.le hpa 2
    linarith
  linarith

theorem ind_mul_self (k i : ℕ) : ind k i * ind k i = ind k i := by
  unfold ind; split_ifs <;> norm_num

/-- Chebyshev's inequality for the event `X = 0`, in counting form. -/
theorem cheb_count {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) (P : Ω → Prop) [DecidablePred P]
    (hP : ∀ ω, P ω → X ω = 0) (μ : ℝ) :
    ((univ.filter P).card : ℝ) * μ ^ 2 ≤
      ∑ ω, X ω ^ 2 - 2 * μ * ∑ ω, X ω + (Fintype.card Ω : ℝ) * μ ^ 2 := by
  have e : ∑ ω, (X ω - μ) ^ 2 =
      ∑ ω, X ω ^ 2 - 2 * μ * ∑ ω, X ω + (Fintype.card Ω : ℝ) * μ ^ 2 := by
    have h : ∀ ω, (X ω - μ) ^ 2 = X ω ^ 2 - 2 * μ * X ω + μ ^ 2 := fun ω => by ring
    simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
      nsmul_eq_mul]
  rw [← e, natCast_card_filter, sum_mul]
  apply sum_le_sum
  intro ω _
  split_ifs with h
  · rw [hP ω h]; ring_nf; exact le_refl _
  · rw [zero_mul]; positivity

theorem sum_X {k : ℕ} (hk : 1 ≤ k) :
    ∑ G : SimpleGraph (Fin (N + 2)), ∑ w, ind k (G.degree w) =
      2 ^ (N + 2).choose 2 * (((N : ℝ) + 2) * ((tl N k + tl N (k - 1)) / 2)) := by
  rw [sum_comm]
  simp only [sum_ind_degree _ hk, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem sum_X_sq {k : ℕ} (hk : 1 ≤ k) :
    ∑ G : SimpleGraph (Fin (N + 2)), (∑ w, ind k (G.degree w)) ^ 2 =
      2 ^ (N + 2).choose 2 * (((N : ℝ) + 2) * ((tl N k + tl N (k - 1)) / 2) +
        ((N : ℝ) + 2) * (((N : ℝ) + 2) - 1) * ((tl N k ^ 2 + tl N (k - 1) ^ 2) / 2)) := by
  calc ∑ G : SimpleGraph (Fin (N + 2)), (∑ w, ind k (G.degree w)) ^ 2
      = ∑ u : Fin (N + 2), ∑ v : Fin (N + 2), ∑ G : SimpleGraph (Fin (N + 2)),
          ind k (G.degree u) * ind k (G.degree v) := by
        simp only [sq, sum_mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro u _
        rw [sum_comm]
    _ = ∑ u : Fin (N + 2), (2 ^ (N + 2).choose 2 * ((tl N k + tl N (k - 1)) / 2) +
          ((N : ℝ) + 1) * (2 ^ (N + 2).choose 2 * ((tl N k ^ 2 + tl N (k - 1) ^ 2) / 2))) := by
        apply sum_congr rfl
        intro u _
        rw [← add_sum_erase _ _ (mem_univ u)]
        have hdiag : ∑ G : SimpleGraph (Fin (N + 2)), ind k (G.degree u) * ind k (G.degree u) =
            2 ^ (N + 2).choose 2 * ((tl N k + tl N (k - 1)) / 2) := by
          simp only [ind_mul_self]
          exact sum_ind_degree u hk
        rw [hdiag, sum_congr rfl (fun v hv => sum_ind_pair (Ne.symm (ne_of_mem_erase hv)) hk),
          sum_const, card_erase_of_mem (mem_univ u), card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Second moment.** The probability that no vertex has degree at least `k`. -/
theorem card_none_ge_le {k : ℕ} (hk : 1 ≤ k) (htk : 0 < tl N k) :
    ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => ∀ w, G.degree w < k).card : ℝ) /
        2 ^ (N + 2).choose 2 ≤
      1 / (((N : ℝ) + 2) * tl N k) + bp N (k - 1) ^ 2 / (4 * tl N k ^ 2) := by
  have hba : bp N (k - 1) = tl N (k - 1) - tl N k := by
    have := tl_succ N (k - 1)
    rw [Nat.sub_add_cancel hk] at this
    linarith
  have hab : tl N k ≤ tl N (k - 1) := tl_antitone N (by omega)
  have hcheb := cheb_count (fun G : SimpleGraph (Fin (N + 2)) => ∑ w, ind k (G.degree w))
    (fun G => ∀ w, G.degree w < k)
    (by
      intro G hG
      apply sum_eq_zero
      intro w _
      unfold ind
      rw [if_neg (by have := hG w; omega)])
    (((N : ℝ) + 2) * ((tl N k + tl N (k - 1)) / 2))
  rw [sum_X hk, sum_X_sq hk, card_graphs] at hcheb
  push_cast at hcheb
  have hM0 : (0 : ℝ) < 2 ^ (N + 2).choose 2 := by positivity
  have hn : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [hba]
  apply cheb_alg hn htk hab
  rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
  linarith

/-- Two distinct vertices of maximum degree. -/
def Tie {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ u v, u ≠ v ∧ G.degree u = G.maxDegree ∧ G.degree v = G.maxDegree

/-- **The main estimate.** -/
theorem tie_le {k : ℕ} (hk : 1 ≤ k) (htk : 0 < tl N k) :
    ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => Tie G).card : ℝ) / 2 ^ (N + 2).choose 2 ≤
      1 / (((N : ℝ) + 2) * tl N k) + bp N (k - 1) ^ 2 / (4 * tl N k ^ 2) +
        ((N : ℝ) + 2) ^ 2 * tl2 N (k - 1) := by
  have hM0 : (0 : ℝ) < 2 ^ (N + 2).choose 2 := by positivity
  set Q : SimpleGraph (Fin (N + 2)) → Fin (N + 2) → Fin (N + 2) → ℝ :=
    fun G u v => if G.degree u = G.degree v then ind k (G.degree u) else 0 with hQ
  have hQ0 : ∀ G u v, 0 ≤ Q G u v := fun G u v => by
    simp only [hQ]; split_ifs
    · exact ind_nonneg _ _
    · exact le_refl _
  -- pointwise
  have hpt : ∀ G : SimpleGraph (Fin (N + 2)), (if Tie G then (1 : ℝ) else 0) ≤
      (if ∀ w, G.degree w < k then 1 else 0) + ∑ u, ∑ v ∈ univ.erase u, Q G u v := by
    intro G
    have hsum0 : 0 ≤ ∑ u, ∑ v ∈ univ.erase u, Q G u v :=
      sum_nonneg fun u _ => sum_nonneg fun v _ => hQ0 G u v
    by_cases hT : Tie G
    · rw [if_pos hT]
      by_cases hE : ∀ w, G.degree w < k
      · rw [if_pos hE]; linarith
      · rw [if_neg hE, zero_add]
        push Not at hE
        obtain ⟨w, hw⟩ := hE
        obtain ⟨u, v, huv, hu, hv⟩ := hT
        have hkΔ : k ≤ G.maxDegree := hw.trans (G.degree_le_maxDegree w)
        have hQ1 : Q G u v = 1 := by
          simp only [hQ]
          rw [if_pos (hu.trans hv.symm)]
          unfold ind
          rw [if_pos (by rw [hu]; exact hkΔ)]
        calc (1 : ℝ) = Q G u v := hQ1.symm
          _ ≤ ∑ v ∈ univ.erase u, Q G u v :=
              single_le_sum (fun v _ => hQ0 G u v) (mem_erase.2 ⟨Ne.symm huv, mem_univ v⟩)
          _ ≤ ∑ u, ∑ v ∈ univ.erase u, Q G u v :=
              single_le_sum (f := fun u => ∑ v ∈ univ.erase u, Q G u v)
                (fun u _ => sum_nonneg fun v _ => hQ0 G u v) (mem_univ u)
    · rw [if_neg hT]
      have : (0 : ℝ) ≤ if ∀ w, G.degree w < k then 1 else 0 := by split_ifs <;> norm_num
      linarith
  have hsum := sum_le_sum fun G (_ : G ∈ univ) => hpt G
  rw [sum_add_distrib, ← natCast_card_filter, ← natCast_card_filter, sum_comm] at hsum
  have hpair : ∑ u : Fin (N + 2), ∑ G : SimpleGraph (Fin (N + 2)), ∑ v ∈ univ.erase u, Q G u v ≤
      ((N : ℝ) + 2) ^ 2 * ((2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1)) := by
    have h1 : ∀ u : Fin (N + 2), ∑ G : SimpleGraph (Fin (N + 2)), ∑ v ∈ univ.erase u, Q G u v ≤
        ((N : ℝ) + 2) * ((2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1)) := by
      intro u
      rw [sum_comm]
      calc ∑ v ∈ univ.erase u, ∑ G : SimpleGraph (Fin (N + 2)), Q G u v
          ≤ ∑ v ∈ univ.erase u, (2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1) :=
            sum_le_sum fun v hv => sum_eq_pair_le (Ne.symm (ne_of_mem_erase hv)) k
        _ = ((N : ℝ) + 1) * ((2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1)) := by
            rw [sum_const, card_erase_of_mem (mem_univ u), card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast; ring
        _ ≤ ((N : ℝ) + 2) * ((2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1)) := by
            exact mul_le_mul_of_nonneg_right (by linarith)
              (mul_nonneg hM0.le (tl2_nonneg _ _))
    calc ∑ u : Fin (N + 2), ∑ G : SimpleGraph (Fin (N + 2)), ∑ v ∈ univ.erase u, Q G u v
        ≤ ∑ u : Fin (N + 2), ((N : ℝ) + 2) * ((2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1)) := sum_le_sum fun u _ => h1 u
      _ = ((N : ℝ) + 2) ^ 2 * ((2 : ℝ) ^ (N + 2).choose 2 * tl2 N (k - 1)) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hE := card_none_ge_le hk htk
  rw [div_le_iff₀ hM0] at hE
  rw [div_le_iff₀ hM0]
  linarith

theorem tendsto_tie : Tendsto (fun N : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => Tie G).card : ℝ) / 2 ^ (N + 2).choose 2)
    atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall fun N => lt_of_lt_of_le ha (by positivity)
  · intro ε hε
    filter_upwards [exists_good (half_pos hε)] with N hN
    obtain ⟨k, hk, htk, hb⟩ := hN
    exact (tie_le hk htk).trans_lt (hb.trans_lt (half_lt_self hε))

theorem not_tie_iff {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) :
    ¬ Tie G ↔ ∃! v, G.degree v = G.maxDegree := by
  constructor
  · intro hT
    obtain ⟨v, hv⟩ := exists_maximal_degree_vertex G
    refine ⟨v, hv.symm, fun w hw => ?_⟩
    by_contra hne
    exact hT ⟨w, v, hne, hw, hv.symm⟩
  · rintro ⟨v, -, hv⟩ ⟨a, b, hab, ha, hb⟩
    exact hab ((hv a ha).trans (hv b hb).symm)

theorem subsingleton_of_not_tie {n : ℕ} (G : SimpleGraph (Fin n)) (hT : ¬ Tie G) :
    {v | G.degree v = G.maxDegree}.Subsingleton := by
  intro a ha b hb
  by_contra hne
  exact hT ⟨a, b, hne, ha, hb⟩

theorem card_tie_add (N : ℕ) :
    ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => ¬ Tie G).card : ℝ) =
      2 ^ (N + 2).choose 2 -
        ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => Tie G).card : ℝ) := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (SimpleGraph (Fin (N + 2)))))
    (fun G => Tie G)
  rw [card_univ, card_graphs] at h
  have h' : ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => Tie G).card : ℝ) +
      ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => ¬ Tie G).card : ℝ) =
        2 ^ (N + 2).choose 2 := by exact_mod_cast h
  linarith

/-- **Almost every graph has a unique vertex of maximum degree.** -/
theorem tendsto_unique_maxDegree' : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => ∃! v, G.degree v = G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 2]
  have e : (fun N : ℕ => ((univ.filter fun G : SimpleGraph (Fin (N + 2)) =>
      ∃! v, G.degree v = G.maxDegree).card : ℝ) / 2 ^ (N + 2).choose 2) =
      fun N => 1 - ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => Tie G).card : ℝ) /
        2 ^ (N + 2).choose 2 := by
    funext N
    have hf : (univ.filter fun G : SimpleGraph (Fin (N + 2)) => ∃! v, G.degree v = G.maxDegree) =
        univ.filter fun G => ¬ Tie G :=
      filter_congr fun G _ => (not_tie_iff G).symm
    rw [hf, card_tie_add, sub_div, div_self (by positivity)]
  rw [e]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_tie

/-- **Erdős–Wilson 1977.** Almost every graph is of class one. -/
theorem tendsto_classOne : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => G.lineGraph.Colorable G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1) := by
  rw [← tendsto_add_atTop_iff_nat 2]
  have hlow : Tendsto (fun N : ℕ => 1 - ((univ.filter fun G : SimpleGraph (Fin (N + 2)) =>
      Tie G).card : ℝ) / 2 ^ (N + 2).choose 2) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_tie
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_) (fun N => ?_)
  · have hsub : (univ.filter fun G : SimpleGraph (Fin (N + 2)) => ¬ Tie G) ⊆
        univ.filter fun G => G.lineGraph.Colorable G.maxDegree := by
      intro G hG
      simp only [mem_filter, mem_univ, true_and] at hG ⊢
      exact colorable_of_subsingleton G (subsingleton_of_not_tie G hG)
    have h1 := card_le_card hsub
    have h2 : ((univ.filter fun G : SimpleGraph (Fin (N + 2)) => ¬ Tie G).card : ℝ) ≤
        ((univ.filter fun G : SimpleGraph (Fin (N + 2)) =>
          G.lineGraph.Colorable G.maxDegree).card : ℝ) := by exact_mod_cast h1
    rw [card_tie_add] at h2
    have hM : (0 : ℝ) < 2 ^ (N + 2).choose 2 := by positivity
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hM, one_mul]
    linarith
  · have hM : (0 : ℝ) < 2 ^ (N + 2).choose 2 := by positivity
    rw [div_le_one hM]
    have h1 := card_le_univ (univ.filter fun G : SimpleGraph (Fin (N + 2)) =>
      G.lineGraph.Colorable G.maxDegree)
    rw [card_graphs] at h1
    exact_mod_cast h1

end ErdosWilson
