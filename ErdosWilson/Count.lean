/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ErdosWilson.Binomial
public import RandomGraphLib.Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The joint law of two degrees in a uniformly random graph

For distinct vertices `u, v` of `Fin n` write `rest u v` for the other `n - 2` vertices and
`data u v G = (N(u) ∩ rest, N(v) ∩ rest, [uv ∈ E(G)])`. Adding (symmetric difference) a fixed graph
supported on the edges at `u` and `v` permutes the graphs and translates `data`, so all fibres of
`data` over its range `𝒫(rest) × 𝒫(rest) × Bool` have the same size (`card_fiber`). Hence
(`sum_graphs`), for every `f`,

`∑_G f(|N(u) ∩ rest|, |N(v) ∩ rest|, [uv]) = 2^C(n,2) ∑_{i,j} bp_i bp_j (f(i,j,0) + f(i,j,1)) / 2`

with `bp = bp (n - 2)`: the two degrees are `Bin(n - 2, 1/2)` variables plus a shared fair coin.
The number of graphs on `Fin n` is `2 ^ C(n, 2)` (`card_graphs`, from `RandomGraphLib.graphEquiv`).
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosWilson

theorem card_graphs (n : ℕ) : Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  rw [← Fintype.card_congr (RandomGraphLib.graphEquiv n)]
  classical
  rw [Fintype.card_fun, Fintype.card_bool, RandomGraphLib.card_pairs]

open Classical

variable {n : ℕ}

/-- The vertices other than `u` and `v`. -/
def rest (u v : Fin n) : Finset (Fin n) := (univ.erase u).erase v

theorem mem_rest {u v w : Fin n} : w ∈ rest u v ↔ w ≠ u ∧ w ≠ v := by
  simp [rest, and_comm]

theorem rest_comm (u v : Fin n) : rest u v = rest v u := by
  ext w; simp [mem_rest, and_comm]

theorem card_rest {u v : Fin n} (h : u ≠ v) : (rest u v).card = n - 2 := by
  rw [rest, card_erase_of_mem (by simp [Ne.symm h]), card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]
  omega

/-- The neighbours of `x` among the vertices other than `u` and `v`. -/
noncomputable def part (G : SimpleGraph (Fin n)) (u v x : Fin n) : Finset (Fin n) :=
  G.neighborFinset x ∩ rest u v

theorem mem_part {G : SimpleGraph (Fin n)} {u v x w : Fin n} :
    w ∈ part G u v x ↔ G.Adj x w ∧ w ≠ u ∧ w ≠ v := by
  simp [part, mem_rest]

theorem part_subset (G : SimpleGraph (Fin n)) (u v x : Fin n) : part G u v x ⊆ rest u v :=
  inter_subset_right

theorem part_comm (G : SimpleGraph (Fin n)) (u v x : Fin n) : part G v u x = part G u v x := by
  simp [part, rest_comm]

theorem degree_left (G : SimpleGraph (Fin n)) {u v : Fin n} (h : u ≠ v) :
    G.degree u = (part G u v u).card + if G.Adj u v then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree]
  have e : G.neighborFinset u = part G u v u ∪ (if G.Adj u v then {v} else ∅) := by
    ext w
    constructor
    · intro hw
      rw [mem_neighborFinset] at hw
      by_cases hwv : w = v
      · subst hwv; simp [hw]
      · exact mem_union_left _ (mem_part.2 ⟨hw, (G.ne_of_adj hw).symm, hwv⟩)
    · intro hw
      rcases mem_union.1 hw with h1 | h1
      · exact mem_of_mem_inter_left h1
      · split_ifs at h1 with hadj
        · rw [mem_singleton.1 h1]; simpa using hadj
        · simp at h1
  rw [e, card_union_of_disjoint]
  · split_ifs <;> simp
  · split_ifs
    · rw [disjoint_singleton_right]
      intro hv
      exact (mem_part.1 hv).2.2 rfl
    · exact disjoint_empty_right _

theorem degree_right (G : SimpleGraph (Fin n)) {u v : Fin n} (h : u ≠ v) :
    G.degree v = (part G u v v).card + if G.Adj u v then 1 else 0 := by
  rw [degree_left G h.symm, part_comm, G.adj_comm]

/-- The graph with edges `u w` (`w ∈ S`), `v w` (`w ∈ T`) and, if `c`, the edge `u v`. -/
def star (u v : Fin n) (S T : Finset (Fin n)) (c : Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x z => (x = u ∧ z ∈ S) ∨ (x = v ∧ z ∈ T) ∨ (c = true ∧ x = u ∧ z = v)

theorem part_star_left {u v : Fin n} (h : u ≠ v) {S T : Finset (Fin n)} (hS : S ⊆ rest u v)
    (c : Bool) : part (star u v S T c) u v u = S := by
  ext w
  rw [mem_part]
  constructor
  · rintro ⟨hadj, hwu, hwv⟩
    simp only [star, fromRel_adj] at hadj
    obtain ⟨-, hr | hr⟩ := hadj
    · rcases hr with ⟨-, hw⟩ | ⟨huv, -⟩ | ⟨-, -, hw⟩
      · exact hw
      · exact absurd huv h
      · exact absurd hw hwv
    · rcases hr with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨-, hw, -⟩
      · exact absurd hw hwu
      · exact absurd hw hwv
      · exact absurd hw hwu
  · intro hw
    have hw' := mem_rest.1 (hS hw)
    refine ⟨?_, hw'.1, hw'.2⟩
    simp only [star, fromRel_adj]
    exact ⟨Ne.symm hw'.1, by simp [hw]⟩

theorem part_star_right {u v : Fin n} (h : u ≠ v) {S T : Finset (Fin n)} (hT : T ⊆ rest u v)
    (c : Bool) : part (star u v S T c) u v v = T := by
  ext w
  rw [mem_part]
  constructor
  · rintro ⟨hadj, hwu, hwv⟩
    simp only [star, fromRel_adj] at hadj
    obtain ⟨-, hr | hr⟩ := hadj
    · rcases hr with ⟨hvu, -⟩ | ⟨-, hw⟩ | ⟨-, hvu, -⟩
      · exact absurd hvu (Ne.symm h)
      · exact hw
      · exact absurd hvu (Ne.symm h)
    · rcases hr with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨-, hw, -⟩
      · exact absurd hw hwu
      · exact absurd hw hwv
      · exact absurd hw hwu
  · intro hw
    have hw' := mem_rest.1 (hT hw)
    refine ⟨?_, hw'.1, hw'.2⟩
    simp only [star, fromRel_adj]
    exact ⟨Ne.symm hw'.2, by simp [hw]⟩

theorem star_adj {u v : Fin n} (h : u ≠ v) {S T : Finset (Fin n)} (hS : S ⊆ rest u v)
    (hT : T ⊆ rest u v) (c : Bool) : (star u v S T c).Adj u v ↔ c = true := by
  simp only [star, fromRel_adj]
  constructor
  · rintro ⟨-, hr | hr⟩
    · rcases hr with ⟨-, hv⟩ | ⟨huv, -⟩ | ⟨hc, -, -⟩
      · exact absurd rfl (mem_rest.1 (hS hv)).2
      · exact absurd huv h
      · exact hc
    · rcases hr with ⟨hvu, -⟩ | ⟨-, hu⟩ | ⟨-, hvu, -⟩
      · exact absurd hvu (Ne.symm h)
      · exact absurd rfl (mem_rest.1 (hT hu)).1
      · exact absurd hvu (Ne.symm h)
  · intro hc
    exact ⟨h, by simp [hc]⟩

theorem symmDiff_adj' (G H : SimpleGraph (Fin n)) (x y : Fin n) :
    (symmDiff G H).Adj x y ↔ (G.Adj x y ∧ ¬ H.Adj x y) ∨ (H.Adj x y ∧ ¬ G.Adj x y) := by
  simp [symmDiff_def]

theorem part_symmDiff (G H : SimpleGraph (Fin n)) (u v x : Fin n) :
    part (symmDiff G H) u v x = symmDiff (part G u v x) (part H u v x) := by
  ext w
  simp only [mem_part, mem_symmDiff, symmDiff_adj']
  tauto

/-- The data `(N(u) ∩ rest, N(v) ∩ rest, [uv ∈ E])` of a graph. -/
noncomputable def data (u v : Fin n) (G : SimpleGraph (Fin n)) :
    Finset (Fin n) × Finset (Fin n) × Bool :=
  (part G u v u, part G u v v, decide (G.Adj u v))

/-- The range of `data`. -/
def box (u v : Fin n) : Finset (Finset (Fin n) × Finset (Fin n) × Bool) :=
  (rest u v).powerset ×ˢ (rest u v).powerset ×ˢ univ

theorem data_mem_box (u v : Fin n) (G : SimpleGraph (Fin n)) : data u v G ∈ box u v := by
  simp only [data, box, mem_product, mem_powerset, mem_univ, and_true]
  exact ⟨part_subset G u v u, part_subset G u v v⟩

theorem data_symmDiff_star {u v : Fin n} (h : u ≠ v) {S T : Finset (Fin n)} (hS : S ⊆ rest u v)
    (hT : T ⊆ rest u v) (c : Bool) (G : SimpleGraph (Fin n)) :
    data u v (symmDiff G (star u v S T c)) =
      (symmDiff (part G u v u) S, symmDiff (part G u v v) T, xor (decide (G.Adj u v)) c) := by
  simp only [data, part_symmDiff, part_star_left h hS, part_star_right h hT, Prod.mk.injEq,
    true_and]
  have := star_adj h hS hT c
  cases c <;> by_cases hG : G.Adj u v <;> simp_all [symmDiff_adj']

theorem empty_symmDiff' (S : Finset (Fin n)) : symmDiff ∅ S = S := by
  ext; simp [mem_symmDiff]

theorem card_fiber {u v : Fin n} (h : u ≠ v) {y : Finset (Fin n) × Finset (Fin n) × Bool}
    (hy : y ∈ box u v) :
    (univ.filter fun G => data u v G = y).card =
      (univ.filter fun G => data u v G = (∅, ∅, false)).card := by
  obtain ⟨S, T, c⟩ := y
  have hST : S ⊆ rest u v ∧ T ⊆ rest u v := by simpa [box] using hy
  set H := star u v S T c
  have hinv : ∀ G : SimpleGraph (Fin n), symmDiff (symmDiff G H) H = G := fun G =>
    symmDiff_symmDiff_cancel_right H G
  apply card_nbij' (fun G => symmDiff G H) (fun G => symmDiff G H)
  · intro G hG
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hG ⊢
    rw [data_symmDiff_star h hST.1 hST.2]
    simp only [data, Prod.mk.injEq] at hG
    obtain ⟨h1, h2, h3⟩ := hG
    rw [h1, h2, h3]
    simp
  · intro G hG
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hG ⊢
    rw [data_symmDiff_star h hST.1 hST.2]
    simp only [data, Prod.mk.injEq] at hG
    obtain ⟨h1, h2, h3⟩ := hG
    rw [h1, h2, h3]
    simp [empty_symmDiff']
  · intro G _; exact hinv G
  · intro G _; exact hinv G

theorem card_box {u v : Fin n} (h : u ≠ v) : (box u v).card = 2 ^ (n - 2) * (2 ^ (n - 2) * 2) := by
  simp [box, card_product, card_powerset, card_rest h]

theorem sum_box (u v : Fin n) (f : ℕ → ℕ → Bool → ℝ) :
    ∑ y ∈ box u v, f y.1.card y.2.1.card y.2.2 =
      ∑ i ∈ range ((rest u v).card + 1), ∑ j ∈ range ((rest u v).card + 1),
        ((rest u v).card.choose i : ℝ) * (rest u v).card.choose j * (f i j false + f i j true) := by
  rw [box, sum_product]
  simp only [sum_product, Fintype.sum_bool]
  rw [sum_powerset_apply_card (fun i => ∑ T ∈ (rest u v).powerset, (f i T.card true + f i T.card false))]
  apply sum_congr rfl
  intro i _
  rw [sum_powerset_apply_card (fun j => f i j true + f i j false), nsmul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [nsmul_eq_mul]
  ring

/-- **Joint law of two degrees.** -/
theorem sum_graphs {u v : Fin n} (h : u ≠ v) (f : ℕ → ℕ → Bool → ℝ) :
    ∑ G : SimpleGraph (Fin n), f (part G u v u).card (part G u v v).card (decide (G.Adj u v)) =
      2 ^ n.choose 2 * ∑ i ∈ range (n - 2 + 1), ∑ j ∈ range (n - 2 + 1),
        bp (n - 2) i * bp (n - 2) j * ((f i j false + f i j true) / 2) := by
  set F : ℝ := ((univ.filter fun G : SimpleGraph (Fin n) => data u v G = (∅, ∅, false)).card : ℝ)
  have key : ∀ g : Finset (Fin n) × Finset (Fin n) × Bool → ℝ,
      ∑ G : SimpleGraph (Fin n), g (data u v G) = F * ∑ y ∈ box u v, g y := by
    intro g
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := box u v) (g := data u v)
      (fun G _ => data_mem_box u v G), mul_sum]
    apply sum_congr rfl
    intro y hy
    rw [sum_congr rfl (fun G hG => by rw [(mem_filter.1 hG).2]), sum_const, card_fiber h hy,
      nsmul_eq_mul]
  have htot : (2 : ℝ) ^ n.choose 2 = F * (2 ^ (n - 2) * (2 ^ (n - 2) * 2)) := by
    have := key (fun _ => 1)
    simp only [sum_const, card_univ, card_graphs, nsmul_eq_mul, mul_one, card_box h] at this
    exact_mod_cast this
  have e1 := key (fun y => f y.1.card y.2.1.card y.2.2)
  simp only [data] at e1
  rw [e1, sum_box, card_rest h, htot, mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  unfold bp
  field_simp

end ErdosWilson
