/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# The random `3`-regular graph and Friedman's theorem

* `Gnt n`: the uniformly random simple `3`-regular graph on `Fin n`, as a definition, and
  `prob n s = P(G_{n,3} ∈ s)`. Every statement about it is restricted to even `n`.
* `lambda2 G`: the second largest eigenvalue `λ₂(A)` of the adjacency matrix.
* `friedman`: Friedman's theorem, `λ₂(A) ≤ 2√2 + ε` w.h.p. (assumed).
* `spectralGap_of_lambda2`: `L = 3I − A`, so `λ₂(A) ≤ c` gives `⟨Lx, x⟩ ≥ (3 − c)‖x‖²` on
  `1ᗮ` (proved).
-/

@[expose] public section

namespace Kuramoto.Random

open Finset Real

-- `G.degree` and `hess G` need decidable adjacency; on an abstract graph it comes from choice.
open scoped Classical

/-! ## The random graph -/

/-- The simple `3`-regular graphs on `Fin n`. Nonempty exactly when `n` is even and `n ≥ 4`. -/
noncomputable def regularGraphs (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G => ∀ v, G.degree v = 3

/-- **`G_{n,3}`**: the uniform distribution on the simple `3`-regular graphs on `Fin n`, when
there is one. For the remaining `n` (odd, or `n < 4`) it is the empty graph; every statement
about `G_{n,3}` is restricted to even `n` (the paper's `G_{2n,3}`). -/
noncomputable def Gnt (n : ℕ) : PMF (SimpleGraph (Fin n)) :=
  if h : (regularGraphs n).Nonempty then PMF.uniformOfFinset (regularGraphs n) h
  else PMF.pure ⊥

/-- `P(G_{n,3} ∈ s)`. -/
noncomputable def prob (n : ℕ) (s : Set (SimpleGraph (Fin n))) : ENNReal :=
  (Gnt n).toOuterMeasure s

/-- `P(A) + P(Aᶜ) = 1`. -/
theorem prob_add_compl (n : ℕ) (s : Set (SimpleGraph (Fin n))) :
    prob n s + prob n sᶜ = 1 := by
  simp only [prob, PMF.toOuterMeasure_apply_fintype, ← Finset.sum_add_distrib,
    Set.indicator_self_add_compl_apply]
  have h := (Gnt n).tsum_coe
  rwa [tsum_fintype] at h

theorem prob_compl (n : ℕ) (s : Set (SimpleGraph (Fin n))) : prob n sᶜ = 1 - prob n s := by
  have h := prob_add_compl n s
  have hs : prob n s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_self_add)
  rw [← h, ENNReal.add_sub_cancel_left hs]

/-! ## Friedman's theorem -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped InnerProductSpace RealInnerProductSpace

/-- `L` has spectral gap `λ` on `1ᗮ`: `⟨L x, x⟩ ≥ λ ‖x‖²` for `x ⊥ 1`, i.e. `λ₂(L) ≥ λ`. Here
`⟨L x, x⟩` is the quadratic form of `hess G 0`, since at a synchronized state every edge weight
is `cos 0 = 1`. -/
def SpectralGap (G : SimpleGraph V) [DecidableRel G.Adj] (gap : ℝ) : Prop :=
  ∀ x : V → ℝ, OnePerp x → gap * (∑ v, x v ^ 2) ≤ quadForm (hess G (fun _ => 0)) x

omit [Fintype V] [DecidableEq V] in
theorem adjMatrix_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix

/-- **`λ₂(A)`, the second largest eigenvalue of the adjacency matrix.** Mathlib's `eigenvalues₀`
lists the eigenvalues of a symmetric matrix with multiplicity, in decreasing order; `λ₂` is
entry number `1` (counting from `0`). Junk value `0` on graphs with fewer than two vertices. -/
noncomputable def lambda2 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if h : 1 < Fintype.card V then (adjMatrix_isHermitian G).eigenvalues₀ ⟨1, h⟩ else 0

/-- **Friedman's theorem, ASSUMED**, as stated in the paper: for every `ε > 0`, with high
probability the second largest eigenvalue of the adjacency matrix of `G_{n,3}` satisfies
`λ₂(A) ≤ 2√2 + ε`.

Friedman, *A proof of Alon's second eigenvalue conjecture* (Mem. AMS 2008), which gives the
stronger `|λ| ≤ 2√2 + ε` for every eigenvalue but the trivial one. This is the only fact about
eigenvalues that is assumed; the consequence `λ₂(L) ≥ 3 − λ₂(A)` used by the paper is proved
(`spectralGap_of_lambda2`).
Restricted to even `n`, where `Gnt n` is the uniform measure. -/
axiom friedman (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, Even n →
      prob n {G | lambda2 G ≤ 2 * Real.sqrt 2 + ε}ᶜ ≤ ENNReal.ofReal η

/-! ### From `λ₂(A)` to `λ₂(L)`

"Since `L = 3I − A`, we have `λ₂(L) = 3 − λ₂(A)`." The direction used: if `λ₂(A) ≤ c`, then
`⟨L x, x⟩ ≥ (3 − c) ‖x‖²` for every `x ⊥ 1`. Proof: expand `x` in an orthonormal eigenbasis of
`A`; the top eigenvector is `∝ 1` (when `c < 3`), so `x ⊥ 1` has no component along it, and
every other eigenvalue is `≤ c`. -/

section Spectral

variable (A : Matrix V V ℝ) (hA : A.IsHermitian)

theorem toEuclideanLin_eigenvectorBasis (j : V) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis j) = hA.eigenvalues j • hA.eigenvectorBasis j := by
  have := hA.mulVec_eigenvectorBasis j
  ext v
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, this]

/-- `⟨Ay, y⟩ = ∑ λ_j ⟨b_j, y⟩²`, so if `y` has no component along `b_{i₀}` and every other
eigenvalue is `≤ c`, then `⟨Ay, y⟩ ≤ c ‖y‖²`. -/
theorem inner_toEuclideanLin_le {c : ℝ} {i₀ : V} (hc : ∀ i, i ≠ i₀ → hA.eigenvalues i ≤ c)
    (y : EuclideanSpace ℝ V) (hy : ⟪hA.eigenvectorBasis i₀, y⟫ = 0) :
    ⟪y, Matrix.toEuclideanLin A y⟫ ≤ c * ⟪y, y⟫ := by
  set B := hA.eigenvectorBasis
  have hT : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hj : ∀ j, ⟪B j, Matrix.toEuclideanLin A y⟫ = hA.eigenvalues j * ⟪B j, y⟫ := fun j => by
    rw [← hT (B j) y, toEuclideanLin_eigenvectorBasis A hA j, real_inner_smul_left]
  rw [← B.sum_inner_mul_inner y (Matrix.toEuclideanLin A y), ← B.sum_inner_mul_inner y y,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [hj, real_inner_comm (B j) y]
  by_cases h : j = i₀
  · subst h; rw [hy]; simp
  · have := hc j h
    nlinarith [mul_nonneg (sub_nonneg.mpr this) (mul_self_nonneg ⟪B j, y⟫)]

end Spectral

section Graph

open Matrix

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The eigenvalues are `λ₁ ≥ λ₂ ≥ …`: all but one of them (the top one, at index `i₀`) are
`≤ λ₂`. -/
theorem exists_top_index (h : 1 < Fintype.card V) :
    ∃ i₀ : V, ∀ i, i ≠ i₀ → (adjMatrix_isHermitian G).eigenvalues i ≤ lambda2 G := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)) with he
  refine ⟨e ⟨0, by omega⟩, fun i hi => ?_⟩
  have h1 : (⟨1, h⟩ : Fin (Fintype.card V)) ≤ e.symm i := by
    show 1 ≤ (e.symm i : ℕ)
    by_contra h0
    exact hi (by rw [← e.apply_symm_apply i]; congr 1; ext; simp only []; omega)
  rw [lambda2, dite_eq_left h]
  exact (adjMatrix_isHermitian G).eigenvalues₀_antitone h1

/-- `⟨L x, x⟩ = 3 ‖x‖² − ⟨A x, x⟩` on a `3`-regular graph (`L = 3I − A`). -/
theorem quadForm_hess_zero (hreg : ∀ v, G.degree v = 3) (x : V → ℝ) :
    quadForm (hess G (fun _ => 0)) x = 3 * ∑ u, x u ^ 2 - ∑ u, x u * (G.adjMatrix ℝ *ᵥ x) u := by
  rw [quadForm_hess]
  have h1 : ∀ u, ∑ _v ∈ G.neighborFinset u, x u ^ 2 = 3 * x u ^ 2 := fun u => by
    rw [Finset.sum_const, G.card_neighborFinset_eq_degree, hreg, nsmul_eq_mul]; norm_num
  have h2 : ∑ u, ∑ v ∈ G.neighborFinset u, x v ^ 2 = ∑ u, ∑ _v ∈ G.neighborFinset u, x u ^ 2 :=
    (sum_neighbor_comm G (fun u _ => x u ^ 2)).symm
  have h3 : ∀ u, ∑ v ∈ G.neighborFinset u, x u * x v = x u * (G.adjMatrix ℝ *ᵥ x) u := fun u => by
    rw [SimpleGraph.adjMatrix_mulVec_apply, Finset.mul_sum]
  have hexp : ∀ u, ∑ v ∈ G.neighborFinset u,
      Real.cos ((fun _ => (0 : ℝ)) u - (fun _ => (0 : ℝ)) v) * (x u - x v) ^ 2
      = ∑ _v ∈ G.neighborFinset u, x u ^ 2 - 2 * ∑ v ∈ G.neighborFinset u, x u * x v
        + ∑ v ∈ G.neighborFinset u, x v ^ 2 := fun u => by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [sub_self, Real.cos_zero]; ring
  rw [Finset.sum_congr rfl fun u _ => hexp u, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2,
    ← Finset.mul_sum, Finset.sum_congr rfl fun u _ => h1 u, Finset.sum_congr rfl fun u _ => h3 u,
    ← Finset.mul_sum]
  ring

/-- **`λ₂(L) ≥ 3 − λ₂(A)`.** On a `3`-regular graph with at least two vertices, `λ₂(A) ≤ c`
gives `⟨L x, x⟩ ≥ (3 − c) ‖x‖²` for every `x ⊥ 1`. -/
theorem spectralGap_of_lambda2 (hreg : ∀ v, G.degree v = 3) (h2 : 1 < Fintype.card V)
    {c : ℝ} (hc : lambda2 G ≤ c) : SpectralGap G (3 - c) := by
  intro x hx
  rw [quadForm_hess_zero G hreg x]
  by_cases hc3 : 3 ≤ c
  · -- then the bound is trivial: `⟨L x, x⟩ ≥ 0`
    have hnn : 0 ≤ quadForm (hess G (fun _ => 0)) x := by
      rw [quadForm_hess]
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_)
      simp only [sub_self, Real.cos_zero, one_mul]; positivity
    rw [quadForm_hess_zero G hreg x] at hnn
    nlinarith [Finset.sum_nonneg fun u (_ : u ∈ Finset.univ) => sq_nonneg (x u)]
  push Not at hc3
  set hA := adjMatrix_isHermitian G
  set B := hA.eigenvectorBasis
  set T := Matrix.toEuclideanLin (G.adjMatrix ℝ)
  obtain ⟨i₀, hi₀⟩ := exists_top_index G h2
  have hci : ∀ i, i ≠ i₀ → hA.eigenvalues i ≤ c := fun i hi => (hi₀ i hi).trans hc
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  set one : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => (1 : ℝ))
  set Y : EuclideanSpace ℝ V := WithLp.toLp 2 x
  -- `A 1 = 3 · 1`
  have hone : T one = (3 : ℝ) • one := by
    ext v
    simp [T, one, Matrix.toEuclideanLin, Matrix.toLpLin_apply, hreg v]
  -- every eigenvector other than the top one is orthogonal to `1`
  have horth : ∀ j, j ≠ i₀ → ⟪B j, one⟫ = 0 := fun j hj => by
    have e1 : ⟪B j, T one⟫ = hA.eigenvalues j * ⟪B j, one⟫ := by
      rw [← hT (B j) one, toEuclideanLin_eigenvectorBasis _ hA j, real_inner_smul_left]
    rw [hone, real_inner_smul_right] at e1
    have := hci j hj
    have hne : hA.eigenvalues j - 3 ≠ 0 := by linarith
    have : (hA.eigenvalues j - 3) * ⟪B j, one⟫ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hne
  -- so `⟨1, z⟩ = ⟨1, b_{i₀}⟩ ⟨b_{i₀}, z⟩`
  have hproj : ∀ z, ⟪one, z⟫ = ⟪one, B i₀⟫ * ⟪B i₀, z⟫ := fun z => by
    rw [← B.sum_inner_mul_inner one z, Finset.sum_eq_single i₀]
    · intro j _ hj; rw [real_inner_comm, horth j hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  have hcard : ⟪one, one⟫ = Fintype.card V := by
    rw [PiLp.inner_apply]; simp [one]
  have htop : ⟪one, B i₀⟫ ≠ 0 := by
    intro h0
    have := hproj one
    rw [h0, zero_mul, hcard] at this
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
    linarith
  -- `x ⊥ 1` has no component along the top eigenvector
  have hY : ⟪B i₀, Y⟫ = 0 := by
    have h1 : ⟪one, Y⟫ = 0 := by rw [PiLp.inner_apply]; simpa [one, Y, OnePerp] using hx
    rw [hproj] at h1
    exact (mul_eq_zero.mp h1).resolve_left htop
  have hle := inner_toEuclideanLin_le (G.adjMatrix ℝ) hA hci Y hY
  have e1 : ⟪Y, T Y⟫ = ∑ u, x u * (G.adjMatrix ℝ *ᵥ x) u := by
    simp [Y, T, PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mul_comm]
  have e2 : ⟪Y, Y⟫ = ∑ u, x u ^ 2 := by rw [PiLp.inner_apply]; simp [Y, sq]
  rw [e1, e2] at hle
  linarith

end Graph

end Kuramoto.Random
