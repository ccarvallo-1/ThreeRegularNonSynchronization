/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Theorem 3.1 (Kantorovich) and Lemma 3.2 (the Hessian is Lipschitz)

Paper cross-reference:
  * Theorem 3.1 -> `Kuramoto.NK.newton_kantorovich` (assumed)
  * Lemma 3.2   -> `Kuramoto.lipschitz_hess` (quadratic-form version, as in the paper); the
                   operator-norm version used with Kantorovich is `Kuramoto.norm_hessL_sub_le`
                   in `Correction.lean`
-/

@[expose] public section

namespace Kuramoto

open Finset Real

/-! ## Newton–Kantorovich -/

namespace NK

/-- **Theorem 3.1 (Kantorovich), ASSUMED.**

Let `E` be a real Banach space and `F : E → E` differentiable with `F'` `K`-Lipschitz. If
`F'(θ₀)` is invertible and `α₀ = K ‖F'(θ₀)⁻¹‖ h₀ ≤ ½` with `h₀ = ‖F'(θ₀)⁻¹ F(θ₀)‖`, then `F`
has a zero within `2 h₀` of `θ₀`.

The paper states it on an open `X ⊆ ℝ^m` with `B̄(θ°, 2h₀) ⊆ X`, and with uniqueness. It is
applied with `X = 1ᗮ`, the whole space, which is the case stated here; uniqueness is never
used, so it is left out.

It is stated for an arbitrary real Banach space, the generality of Kantorovich–Akilov
(Ch. XVIII, Thm. 6), and with a global Lipschitz hypothesis on `F'`, so it is a special case of
the classical theorem. It is an `axiom` (a published theorem not in Mathlib), so that
`#print axioms` lists it for every result that depends on it. -/
axiom newton_kantorovich {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : E → E) (F' : E → (E →L[ℝ] E)) (hF : ∀ x, HasFDerivAt F (F' x) x)
    (K : ℝ) (hK : LipschitzWith (Real.toNNReal K) F')
    (θ₀ : E) (A : E ≃L[ℝ] E) (hA : (A : E →L[ℝ] E) = F' θ₀)
    (h₀ : ℝ) (hh₀ : h₀ = ‖A.symm (F θ₀)‖)
    (hα : K * ‖(A.symm : E →L[ℝ] E)‖ * h₀ ≤ 1 / 2) :
    ∃ θ, F θ = 0 ∧ ‖θ - θ₀‖ ≤ 2 * h₀

end NK

/-! ## The Hessian is Lipschitz -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For two distinct vertices, `|w u - w v| ≤ √2 ‖w‖₂`. This is the `‖B w‖_∞ ≤ √2 ‖w‖₂` step
of the paper's proof. -/
theorem abs_sub_le_sqrt_two_mul {w : V → ℝ} {u v : V} (huv : u ≠ v) :
    |w u - w v| ≤ Real.sqrt 2 * Real.sqrt (∑ z, w z ^ 2) := by
  have hpair : w u ^ 2 + w v ^ 2 ≤ ∑ z, w z ^ 2 := by
    have hsub : ({u, v} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
    have hsum : ∑ z ∈ ({u, v} : Finset V), w z ^ 2 = w u ^ 2 + w v ^ 2 := by
      rw [Finset.sum_insert (by simpa using huv), Finset.sum_singleton]
    calc w u ^ 2 + w v ^ 2 = ∑ z ∈ ({u, v} : Finset V), w z ^ 2 := hsum.symm
      _ ≤ ∑ z, w z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => sq_nonneg _
  have hsq : (w u - w v) ^ 2 ≤ 2 * ∑ z, w z ^ 2 := by nlinarith [sq_nonneg (w u + w v)]
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  calc |w u - w v| = Real.sqrt ((w u - w v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * ∑ z, w z ^ 2) := Real.sqrt_le_sqrt hsq

omit [DecidableEq V] in
/-- On a `3`-regular graph, `∑_u ∑_{v ∼ u} (x u - x v)^2 ≤ 12 ∑ x²`. This is the
`‖B x‖² = ⟨x, L x⟩ ≤ 2d` step, with `d = 3`. -/
theorem sum_sq_diff_le (hreg : ∀ v, G.degree v = 3) (x : V → ℝ) :
    ∑ u, ∑ v ∈ G.neighborFinset u, (x u - x v) ^ 2 ≤ 12 * ∑ v, x v ^ 2 := by
  have hconst : ∀ u : V, ∑ _v ∈ G.neighborFinset u, x u ^ 2 = 3 * x u ^ 2 := by
    intro u
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hreg u, nsmul_eq_mul]
    norm_num
  -- `∑_u ∑_{v ∼ u} x v ² = ∑_u ∑_{v ∼ u} x u ²` by swapping endpoints
  have hswap : ∑ u, ∑ v ∈ G.neighborFinset u, x v ^ 2
      = ∑ u, ∑ v ∈ G.neighborFinset u, x u ^ 2 :=
    (sum_neighbor_comm G (fun u _ => x u ^ 2)).symm
  have hbound : ∑ u, ∑ v ∈ G.neighborFinset u, (x u - x v) ^ 2
      ≤ ∑ u, ∑ v ∈ G.neighborFinset u, (2 * x u ^ 2 + 2 * x v ^ 2) := by
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    nlinarith [sq_nonneg (x u + x v)]
  have hsplit : ∑ u, ∑ v ∈ G.neighborFinset u, (2 * x u ^ 2 + 2 * x v ^ 2)
      = 12 * ∑ v, x v ^ 2 := by
    have e : ∀ u : V, ∑ v ∈ G.neighborFinset u, (2 * x u ^ 2 + 2 * x v ^ 2)
        = 2 * (∑ _v ∈ G.neighborFinset u, x u ^ 2) + 2 * ∑ v ∈ G.neighborFinset u, x v ^ 2 := by
      intro u
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
    simp only [hconst, ← Finset.mul_sum]
    ring
  linarith [hbound, hsplit.le, hsplit.ge]

/-- **Lemma 3.2.** On a `3`-regular graph, `‖H(θ) - H(θ')‖ ≤ 6√2 ‖θ - θ'‖`, with a constant
independent of `n`.

The proof in the paper is elementary: `|cos Δ_e(θ) - cos Δ_e(θ')| ≤ |B_e w|` by `1`-Lipschitz
continuity of `cos`, then `‖B x‖² = ⟨x, L x⟩ ≤ 2d = 6` and `‖B w‖_∞ ≤ √2 ‖w‖`. -/
theorem lipschitz_hess (hreg : ∀ v, G.degree v = 3) (θ θ' : Config V) (x : V → ℝ) :
    |quadForm (hess G θ) x - quadForm (hess G θ') x|
      ≤ 6 * Real.sqrt 2 * Real.sqrt (∑ v, (θ v - θ' v) ^ 2) * (∑ v, x v ^ 2) := by
  set w : V → ℝ := fun v => θ v - θ' v with hw
  set N : ℝ := Real.sqrt 2 * Real.sqrt (∑ z, w z ^ 2) with hN
  have hN0 : 0 ≤ N := by positivity
  -- write the difference as a single sum over ordered adjacent pairs
  have hdiff : quadForm (hess G θ) x - quadForm (hess G θ') x
      = (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u,
          (Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (x u - x v) ^ 2 := by
    rw [quadForm_hess, quadForm_hess, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  -- bound each term: `|cos a - cos b| ≤ |a - b| = |w u - w v| ≤ √2 ‖w‖`
  have hterm : ∀ u : V, ∀ v ∈ G.neighborFinset u,
      |(Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (x u - x v) ^ 2|
        ≤ N * (x u - x v) ^ 2 := by
    intro u v hv
    have huv : u ≠ v := (G.ne_of_adj ((G.mem_neighborFinset u v).mp hv))
    have hcos : |Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)| ≤ N := by
      refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
      have : (θ u - θ v) - (θ' u - θ' v) = w u - w v := by simp [hw]; ring
      rw [this]
      exact abs_sub_le_sqrt_two_mul (w := w) huv
    rw [abs_mul, abs_of_nonneg (sq_nonneg (x u - x v))]
    exact mul_le_mul_of_nonneg_right hcos (sq_nonneg _)
  calc |quadForm (hess G θ) x - quadForm (hess G θ') x|
      = (1 / 2) * |∑ u, ∑ v ∈ G.neighborFinset u,
          (Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (x u - x v) ^ 2| := by
        rw [hdiff, abs_mul]; norm_num
    _ ≤ (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u, N * (x u - x v) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun u _ => ?_
        exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (hterm u))
    _ = (1 / 2) * N * ∑ u, ∑ v ∈ G.neighborFinset u, (x u - x v) ^ 2 := by
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
    _ ≤ (1 / 2) * N * (12 * ∑ v, x v ^ 2) := by
        refine mul_le_mul_of_nonneg_left (sum_sq_diff_le G hreg x) (by positivity)
    _ = 6 * Real.sqrt 2 * Real.sqrt (∑ v, (θ v - θ' v) ^ 2) * (∑ v, x v ^ 2) := by
        rw [hN, hw]; ring

end Kuramoto
