/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Proposition 1.3: the stability criterion

Paper cross-reference:
  * Proposition 1.3 -> `Kuramoto.prop_cert`; with the remark after Definition 1.1,
                       `Kuramoto.not_globallySynchronizing_of_certificate`
-/

@[expose] public section

namespace Kuramoto

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A phase-cohesive configuration has positive semidefinite Hessian: all the edge weights
`cos Δ_e` in `quadForm_hess` are positive. -/
theorem quadForm_hess_nonneg {θ : Config V} (hpc : PhaseCohesive G θ) (x : V → ℝ) :
    0 ≤ quadForm (hess G θ) x := by
  rw [quadForm_hess]
  have : (0 : ℝ) ≤ ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u - x v) ^ 2 := by
    refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v hv => ?_
    exact mul_nonneg (le_of_lt (hpc u v ((G.mem_neighborFinset u v).mp hv))) (sq_nonneg _)
  linarith

/-- On a connected graph the quadratic form vanishes only on the constants: if every edge weight
is positive and `∑_{uv ∈ E} cos Δ_e (x u - x v)^2 = 0` then `x` is constant. -/
theorem quadForm_hess_eq_zero_iff_const (hG : G.Connected) {θ : Config V}
    (hpc : PhaseCohesive G θ) {x : V → ℝ} (hx : quadForm (hess G θ) x = 0) :
    ∃ c, ∀ v, x v = c := by
  rw [quadForm_hess] at hx
  have hnn : ∀ u ∈ Finset.univ, (0 : ℝ) ≤
      ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u - x v) ^ 2 := fun u _ =>
    Finset.sum_nonneg fun v hv =>
      mul_nonneg (le_of_lt (hpc u v ((G.mem_neighborFinset u v).mp hv))) (sq_nonneg _)
  have hS : ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u - x v) ^ 2 = 0 := by
    linarith
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS
  -- every edge has equal endpoints, since its weight is strictly positive
  have key : ∀ u v, G.Adj u v → x u = x v := by
    intro u v huv
    have hnn2 : ∀ w ∈ G.neighborFinset u, (0 : ℝ) ≤ Real.cos (θ u - θ w) * (x u - x w) ^ 2 :=
      fun w hw => mul_nonneg (le_of_lt (hpc u w ((G.mem_neighborFinset u w).mp hw))) (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp (hrow u (Finset.mem_univ u)) v
      ((G.mem_neighborFinset u v).mpr huv)
    have hsq : (x u - x v) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h (ne_of_gt (hpc u v huv))
      · exact h
    have : x u - x v = 0 := by
      have := sq_eq_zero_iff.mp hsq
      exact this
    linarith
  -- connectedness propagates equality along walks
  have hconst : ∀ u v : V, G.Reachable u v → x u = x v := by
    intro u v huv
    obtain ⟨w⟩ := huv
    induction w with
    | nil => rfl
    | cons h _ ih => exact (key _ _ h).trans ih
  obtain ⟨u₀⟩ := hG.nonempty
  exact ⟨x u₀, fun v => hconst v u₀ (hG.preconnected v u₀)⟩

/-- Phase cohesion implies nondegenerate stability, for an equilibrium on a connected graph.
This is the standard Dörfler–Bullo criterion; the paper gives the two-line proof in §1.3. -/
theorem stableEquilibrium_of_phaseCohesive (hG : G.Connected) {θ : Config V}
    (heq : IsEquilibrium G θ) (hpc : PhaseCohesive G θ) :
    StableEquilibrium G θ := by
  refine ⟨heq, fun x hperp hx0 => ?_⟩
  rcases lt_or_eq_of_le (quadForm_hess_nonneg G hpc x) with h | h
  · exact h
  -- if the form vanished, `x` would be constant, and a constant in `1ᗮ` is `0`
  exfalso
  obtain ⟨c, hc⟩ := quadForm_hess_eq_zero_iff_const G hG hpc h.symm
  obtain ⟨u₀⟩ := hG.nonempty
  have : Nonempty V := ⟨u₀⟩
  have hsum : (0 : ℝ) = (Fintype.card V : ℝ) * c := by
    rw [← hperp, Finset.sum_congr rfl (fun v _ => hc v), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hcard : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc0 : c = 0 := (mul_eq_zero.mp hsum.symm).resolve_left hcard
  exact hx0 (funext fun v => by rw [hc v, hc0]; rfl)

/-- **Proposition 1.3.** Let `G` be connected and let `θ` satisfy `∇𝓔(θ) = 0`,
`max_e |Δ_e| < π/2` and `Δ_{e₀} ≠ 0` for some edge `e₀`. Then `θ` is a stable equilibrium that is
not synchronized. -/
theorem prop_cert (hG : G.Connected) {θ : Config V} (heq : IsEquilibrium G θ)
    (hmax : ∀ u v, G.Adj u v → |phaseDiff θ u v| < π / 2)
    (he₀ : ∃ u₀ v₀, G.Adj u₀ v₀ ∧ phaseDiff θ u₀ v₀ ≠ 0) :
    StableEquilibrium G θ ∧ ¬ Synchronized θ := by
  have hpc := (phaseCohesive_iff G θ).mpr hmax
  refine ⟨stableEquilibrium_of_phaseCohesive G hG heq hpc, fun hs => ?_⟩
  obtain ⟨u₀, v₀, _, hne⟩ := he₀
  have h1 := hs u₀ v₀
  rw [cos_eq_cos_phaseDiff] at h1
  have hpi := Real.pi_pos
  have hlo : -π < phaseDiff θ u₀ v₀ := Real.Angle.neg_pi_lt_toReal _
  have hhi : phaseDiff θ u₀ v₀ ≤ π := Real.Angle.toReal_le_pi _
  exact hne ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp h1)

/-- Proposition 1.3 together with the remark after Definition 1.1: a stable non-synchronized
equilibrium means `G` is not globally synchronizing. Here nontriviality is phrased as
`cos (θ u₀ − θ v₀) ≠ 1`, which is `Δ_{u₀v₀} ≠ 0`. -/
theorem not_globallySynchronizing_of_certificate (hG : G.Connected) {θ : Config V}
    (heq : IsEquilibrium G θ) (hpc : PhaseCohesive G θ)
    {u₀ v₀ : V} (_hadj : G.Adj u₀ v₀) (hne : Real.cos (θ u₀ - θ v₀) ≠ 1) :
    ¬ GloballySynchronizing G := by
  intro hsync
  exact hne (hsync θ (stableEquilibrium_of_phaseCohesive G hG heq hpc) u₀ v₀)

end Kuramoto
