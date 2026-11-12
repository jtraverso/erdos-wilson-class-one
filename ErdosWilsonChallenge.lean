/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Erdős–Wilson (1977): almost every graph is of class one

P. Erdős and R. J. Wilson, *Note on the chromatic index of almost all graphs*, J. Combin. Theory
Ser. B 23 (1977) 255–257. Among the `2 ^ C(n, 2)` labelled graphs on `n` vertices, the proportion
with chromatic index equal to the maximum degree (`χ'(G) = Δ(G)`, class one) tends to `1`.

The proof: almost every graph has a unique vertex of maximum degree, and such a graph is of class
one (a special case of Fournier's theorem).
-/

@[expose] public section

open Finset Filter Topology

namespace ErdosWilson

open SimpleGraph

/-- A graph with at most one vertex of maximum degree is of class one. -/
theorem colorable_of_subsingleton_maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : {v | G.degree v = G.maxDegree}.Subsingleton) :
    G.lineGraph.Colorable G.maxDegree := by
  sorry

open Classical in
/-- **Almost every graph has a unique vertex of maximum degree.** -/
theorem tendsto_unique_maxDegree : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => ∃! v, G.degree v = G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1) := by
  sorry

open Classical in
/-- **Erdős–Wilson 1977.** Almost every graph is of class one: the proportion of the graphs on
`Fin n` whose line graph is `Δ(G)`-colourable tends to `1`. -/
theorem erdos_wilson : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => G.lineGraph.Colorable G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1) := by
  sorry

end ErdosWilson
