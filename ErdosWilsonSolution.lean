/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ErdosWilson.Main

/-!
# Proof of the statements in `ErdosWilsonChallenge.lean`

* `colorable_of_subsingleton_maxDegree`: Fournier's theorem (`FournierLib.fournier`,
  jtraverso/fournier-class-one, PALOMAR-2026-11-08-000009) applied to an induced graph on at most
  one vertex.
* `tendsto_unique_maxDegree`, `erdos_wilson`: second-moment argument for the number of vertices
  of degree at least a threshold `k`, together with the joint law of two degrees
  (`ErdosWilson/Count.lean`) and binomial estimates (`ErdosWilson/Binomial.lean`,
  `ErdosWilson/Asymp.lean`); `ErdosWilson/Main.lean` assembles them.
-/

@[expose] public section

open Finset Filter Topology

namespace ErdosWilson

open SimpleGraph

/-- A graph with at most one vertex of maximum degree is of class one. -/
theorem colorable_of_subsingleton_maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : {v | G.degree v = G.maxDegree}.Subsingleton) :
    G.lineGraph.Colorable G.maxDegree :=
  colorable_of_subsingleton G h

open Classical in
/-- **Almost every graph has a unique vertex of maximum degree.** -/
theorem tendsto_unique_maxDegree : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => ∃! v, G.degree v = G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1) :=
  ErdosWilson.tendsto_unique_maxDegree'

open Classical in
/-- **Erdős–Wilson 1977.** Almost every graph is of class one: the proportion of the graphs on
`Fin n` whose line graph is `Δ(G)`-colourable tends to `1`. -/
theorem erdos_wilson : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => G.lineGraph.Colorable G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1) :=
  tendsto_classOne

end ErdosWilson
