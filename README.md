# Erdős–Wilson in Lean 4: almost every graph is of class one

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

P. Erdős and R. J. Wilson, *On the chromatic index of almost all graphs*, J. Combin. Theory Ser. B
23 (1977) 255–257, doi:10.1016/0095-8956(77)90039-9: almost every graph `G` has chromatic index
`χ'(G) = Δ(G)`.

## Statements (`ErdosWilsonChallenge.lean`, namespace `ErdosWilson`)

```lean
theorem colorable_of_subsingleton_maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : {v | G.degree v = G.maxDegree}.Subsingleton) :
    G.lineGraph.Colorable G.maxDegree

open Classical in
theorem tendsto_unique_maxDegree : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => ∃! v, G.degree v = G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1)

open Classical in
theorem erdos_wilson : Tendsto (fun n : ℕ =>
    ((univ.filter fun G : SimpleGraph (Fin n) => G.lineGraph.Colorable G.maxDegree).card : ℝ) /
      2 ^ n.choose 2) atTop (𝓝 1)
```

## Proof

* `ErdosWilson/Count.lean`: for distinct `u, v`, symmetric difference with graphs supported on the
  edges at `u` and `v` shows that `(N(u) \ {v}, N(v) \ {u}, [uv ∈ E])` is uniformly distributed;
  hence `deg u = A + c`, `deg v = B + c` with `A, B ~ Bin(n - 2, 1/2)` and a fair coin `c`, all
  independent (`sum_graphs`). The number of graphs on `Fin n` is `2 ^ C(n, 2)`, from
  `RandomGraphLib.graphEquiv` (jtraverso/random-graph-lib @ 86e5575).
* `ErdosWilson/Binomial.lean`: hazard bound `L · bp_j ≤ 2 · tl_{j+1}` near the mean, and the tail
  bound `n · tl_i → 0` beyond `(1 + δ) N / 2`.
* `ErdosWilson/Asymp.lean`: for every `ε` and large `N`, the least `k` with `n · tl_k ≤ A` makes
  `1/(n tl_k) + bp_{k-1}^2 / (4 tl_k^2) + n^2 Σ_{i ≥ k-1} bp_i^2 ≤ ε`.
* `ErdosWilson/Main.lean`: second moment for the number of vertices of degree `≥ k`; if the
  maximum degree is attained twice and some vertex has degree `≥ k`, two distinct vertices have
  equal degree `≥ k`. So `P(tie at the top) → 0`. A graph whose maximum degree is attained once is
  of class one by Fournier's theorem (`FournierLib.fournier`, jtraverso/fournier-class-one,
  PALOMAR-2026-11-08-000009), since its vertices of maximum degree induce a graph on at most one
  vertex.

## Building

```
lake build
```
Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.
