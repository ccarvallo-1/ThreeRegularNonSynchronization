# Random 3-regular graphs are not globally synchronizing — Lean formalization

A Lean 4 / Mathlib formalization of the main result of

> Ciro Carvallo, Pablo Groisman, Dieter Mitsche,
> *Random 3-regular graphs are not globally synchronizing*,
> [arXiv:2610.09135](https://arxiv.org/abs/2610.09135).

**Theorem 1.2.** Let `G_{2n,3}` be a uniformly random simple 3-regular graph on `2n` vertices.
Then `P(G_{2n,3} is not globally synchronizing) → 1` as `n → ∞`.

In Lean (`Kuramoto/Main.lean`):

```lean
theorem main_theorem :
    Filter.Tendsto (fun n => Random.prob (2 * n) {G | ¬ GloballySynchronizing G})
      Filter.atTop (nhds 1)
```

The development has no `sorry`. It builds with no errors or warnings.

`import Kuramoto` exposes the main results:

- `Kuramoto.main_theorem`: Theorem 1.2.
- `Kuramoto.Random.gadgetcount`: Lemma 2.2, `Q_{ℓ,R(ℓ)}` is an induced subgraph of `G_{n,3}` for
  some `ℓ = 4k`, with probability tending to 1.
- `Kuramoto.glue`, `Kuramoto.glue_consequently`: Proposition 3.3, correcting the gadget
  configuration to a stable non-synchronized equilibrium.
- `Kuramoto.Gadget.grad_eq_zero_of_nonleaf`, `Kuramoto.Gadget.etabounds`: Proposition 2.1.
- `Kuramoto.prop_cert`: Proposition 1.3.

## Companion documents

- `Kuramoto_Lean_to_Tex.tex`: a guide to the formalization in mathematical prose, one section per
  Lean file. Every definition and result is labelled with its Lean name. It is a reading aid; the
  Lean source is authoritative.
- `manifest.json`: for each part of the paper, the Lean file and the declarations that formalize
  it, together with the list of assumed results. `scripts/check_manifest.py` (run in CI) checks
  that every listed declaration exists and that `Kuramoto.main_theorem` depends on exactly the
  listed axioms.

## What is assumed

Apart from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), the proof
depends on four published results that are not in Mathlib. Each one is stated as an `axiom`, so
`#print axioms` lists them by name:

| Axiom | Result | Reference |
|---|---|---|
| `Kuramoto.NK.newton_kantorovich` | Kantorovich's theorem (paper, Theorem 3.1), on a real Banach space | Kantorovich–Akilov, *Functional Analysis*, Ch. XVIII, Thm. 6 |
| `Kuramoto.Random.friedman` | w.h.p. `λ₂(A) ≤ 2√2 + ε` for the adjacency matrix of `G_{n,3}` | J. Friedman, *A proof of Alon's second eigenvalue conjecture*, Mem. AMS (2008) |
| `Kuramoto.Random.cycles_poisson` | the number of `ℓ`-cycles of `G_{n,3}` is asymptotically Poisson with mean `2^{ℓ−1}/ℓ` (used as `limsup P(no ℓ-cycle) ≤ e^{−2^{ℓ−1}/ℓ}`) | B. Bollobás (1980); N. Wormald (1981) |
| `Kuramoto.Random.simple_prob_pos` | a uniformly random pairing of `3n` half-edges is simple with probability bounded away from `0` | E. Bender, R. Canfield (1978); B. Bollobás (1980) |

To check:

```sh
lake env lean scripts/print_axioms.lean   # print the axioms of the main results
python3 scripts/check_manifest.py         # check them against manifest.json
```

Everything else is proved. That includes:
- the construction of the gadget `Q_{ℓ,R}` and its equilibrium (Proposition 2.1);
- the Newton–Kantorovich correction step (Proposition 3.3);
- the step from `λ₂(A)` to `λ₂(L)`;
- Lemma 2.2. Its probabilistic input is reduced to the two cited facts about random regular
  graphs; the configuration model and the first-moment count are formalized.

## Modelling choices

- **Global synchronization** (`GloballySynchronizing`, `Kuramoto/Basic.lean`) is the landscape
  version: every stable equilibrium is synchronized. Definition 1.1 of the paper is dynamical
  (almost every trajectory of the gradient flow synchronizes). The formal proof exhibits, with
  probability tending to 1, a stable equilibrium that is not synchronized. That this rules out
  global synchronization in the dynamical sense is the remark after Definition 1.1 (Lyapunov
  stability of a strict local minimum); that step is not formalized.
- **Stable equilibrium** means `∇𝓔(θ) = 0` and `⟨H(θ)x, x⟩ > 0` for every nonzero `x ⊥ 𝟏`, that
  is, `λ₂(H(θ)) > 0`.
- **The random graph.** `Random.Gnt n` is the uniform distribution on the simple 3-regular
  graphs with vertex set `Fin n`, defined with `PMF.uniformOfFinset`. Statements about it are
  restricted to even `n`.
- **Phase differences.** `phaseDiff θ u v` is the paper's `Δ_{uv}`: the representative of
  `θ_v − θ_u` modulo `2π` in `(−π, π]`, via `Real.Angle.toReal`.
- **Eigenvalues.** `Random.lambda2 G` is the second largest eigenvalue of the adjacency matrix,
  taken from Mathlib's eigenvalues of a Hermitian matrix sorted in decreasing order. Elsewhere,
  spectral gaps are expressed through the quadratic form on `𝟏ᗮ`.

## Correspondence with the paper

| Paper | Lean | File |
|---|---|---|
| eq. (2), (3): energy, gradient, Hessian | `energy`, `grad`, `hess` | `Basic.lean` |
| Definition 1.1 | `GloballySynchronizing` | `Basic.lean` |
| §1.3: `Δ_e` | `phaseDiff` | `Basic.lean` |
| Proposition 1.3 | `prop_cert` | `Certificate.lean` |
| §2: the gadget `Q_{ℓ,R}` and `θ^η` | `Gadget.Q`, `Gadget.phase` | `Gadget.lean` |
| Proposition 2.1 (i) | `Gadget.grad_eq_zero_of_nonleaf` | `Gadget.lean` |
| Proposition 2.1 (ii) | `Gadget.phaseCohesive_phase`, `Gadget.abs_phaseDiff_phase_le`, `Gadget.absDelta_branch` | `Gadget.lean` |
| Proposition 2.1 (iii) | `Gadget.exists_unique_root`, `Gadget.root`, `Gadget.δ₀`, `Gadget.etabounds` | `Gadget.lean` |
| Lemma 2.2 | `Random.gadgetcount` | `GadgetCount.lean` |
| Theorem 3.1 (Kantorovich) | `NK.newton_kantorovich` (axiom) | `Kantorovich.lean` |
| Lemma 3.2 | `lipschitz_hess`, operator-norm form `norm_hessL_sub_le` | `Kantorovich.lean`, `Correction.lean` |
| Proposition 3.3 | `glue`, `glue_consequently` | `Correction.lean` |
| Theorem 1.2 | `main_theorem` | `Main.lean` |

## Layout

| File | Contents |
|---|---|
| `Kuramoto/Basic.lean` | energy, gradient, Hessian, `Δ_e`, equilibria, stability, global synchronization |
| `Kuramoto/Certificate.lean` | Proposition 1.3: phase-cohesive equilibria are stable |
| `Kuramoto/Gadget.lean` | `Q_{ℓ,R}`, the configuration `θ^η`, the function `G_R` and its root `η*(R)`, Proposition 2.1 |
| `Kuramoto/Kantorovich.lean` | Theorem 3.1 (assumed), Lemma 3.2 |
| `Kuramoto/Transplant.lean` | the configuration `θ̂` in `G`, its gradient `ε_ℓ(R)`, the threshold `R₀` |
| `Kuramoto/Correction.lean` | Proposition 3.3: Kantorovich on `𝟏ᗮ` |
| `Kuramoto/RandomGraph.lean` | `G_{n,3}`, `λ₂(A)`, Friedman's theorem, `λ₂(L) ≥ 3 − λ₂(A)` |
| `Kuramoto/Extension.lean` | an `ℓ`-cycle in a 3-regular graph with no small dense sets extends to an induced `Q_{ℓ,R}` |
| `Kuramoto/ConfigModel.lean` | the configuration model; `G_{n,3}` is the configuration model conditioned on being simple; the first-moment bound |
| `Kuramoto/GadgetCount.lean` | Lemma 2.2 |
| `Kuramoto/Main.lean` | Theorem 1.2 |

## Building

Install Lean with [elan](https://github.com/leanprover/elan). Then:

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

The Lean version is pinned in `lean-toolchain` and the Mathlib commit in `lakefile.toml`.

## How this formalization was produced

The Lean code was written with extensive use of Claude (Anthropic), working from the paper and
under the authors' supervision. The authors chose the statements to be formalized and checked
that they match the paper; correctness of the proofs is checked by Lean's kernel.

## Citation

Please cite the paper; see `CITATION.cff`.

## License

Apache License 2.0, see `LICENSE`.
