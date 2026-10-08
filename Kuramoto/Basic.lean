/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Section 1: the Kuramoto model on a finite graph

Paper cross-reference:
  * eq. (2)           -> `Kuramoto.energy`
  * eq. (3)           -> `Kuramoto.grad`, `Kuramoto.hess`
  * Definition 1.1    -> `Kuramoto.GloballySynchronizing` (landscape version; see its docstring)
  * §1.3, stability   -> `Kuramoto.IsEquilibrium`, `Kuramoto.StableEquilibrium`
  * §1.3, `Δ_e`       -> `Kuramoto.phaseDiff`; `max_e |Δ_e| < π/2` -> `Kuramoto.PhaseCohesive`
-/

@[expose] public section

namespace Kuramoto

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A phase configuration, i.e. a real lift `θ ∈ ℝ^V` of a point of the torus `(ℝ/2πℤ)^V`.
Every quantity below depends on `θ` only through the differences `θ u - θ v`, hence only on
the class of `θ` modulo `2π`. -/
abbrev Config (V : Type*) := V → ℝ

/-- The energy `𝓔(θ) = ∑_{uv ∈ E} (1 - cos (θ u - θ v))`, paper eq. (2).

Each edge is counted twice by the double sum, hence the factor `1/2`. The summand is symmetric
in `u, v` because `cos` is even, so this really is a sum over unoriented edges. -/
noncomputable def energy (θ : Config V) : ℝ :=
  (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u, (1 - Real.cos (θ u - θ v))

/-- `∂𝓔/∂θ x = ∑_{y ∼ x} sin (θ x - θ y)`, paper eq. (3).

In the notation of the paper this is `-∑_{y ∼ x} sin Δ_{x y}`, since `Δ_{x y} ≡ θ y - θ x`. -/
noncomputable def grad (θ : Config V) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, Real.sin (θ x - θ y)

/-- `θ` is an equilibrium of the gradient flow: the current is divergence free. -/
def IsEquilibrium (θ : Config V) : Prop := ∀ x, grad G θ x = 0

/-- The Hessian `H(θ) = ∑_e cos (Δ_e) L_e`, paper eq. (3).

It is the Laplacian of `G` with edge weights `cos (θ u - θ v)`; note that this is *not* a second
name for the unweighted Laplacian `L`, which is the case `θ` synchronized. -/
noncomputable def hess (θ : Config V) : Matrix V V ℝ := fun u v =>
  if u = v then ∑ y ∈ G.neighborFinset u, Real.cos (θ u - θ y)
  else if G.Adj u v then -Real.cos (θ u - θ v) else 0

/-- The quadratic form of a matrix, written out so that the weighted-Laplacian identity below
can be stated without extra coercions. -/
noncomputable def quadForm (M : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  ∑ u, ∑ v, M u v * x u * x v

omit [DecidableEq V] in
/-- Summing a function over all ordered adjacent pairs is invariant under swapping the two
endpoints: both sides enumerate the darts of `G`. -/
theorem sum_neighbor_comm (f : V → V → ℝ) :
    ∑ u, ∑ v ∈ G.neighborFinset u, f u v = ∑ u, ∑ v ∈ G.neighborFinset u, f v u := by
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases h : G.Adj u v
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right fun hc => h hc.symm]

/-- Splits the Hessian into its diagonal (the row sum) and its off-diagonal `-cos Δ_e` part.
The two cases glue because `¬ G.Adj u u`. -/
theorem hess_eq_add (θ : Config V) (u v : V) :
    hess G θ u v
      = (if u = v then (∑ y ∈ G.neighborFinset u, Real.cos (θ u - θ y)) else 0)
        + (if G.Adj u v then -Real.cos (θ u - θ v) else 0) := by
  unfold hess
  by_cases h : u = v
  · subst h; simp []
  · simp [h]

/-- The identity that drives every stability argument in the paper:
`⟨x, H(θ) x⟩ = ∑_{uv ∈ E} cos (Δ_e) (x u - x v)^2`.

This is what makes `H(θ)` positive semidefinite as soon as all the weights are positive. -/
theorem quadForm_hess (θ : Config V) (x : V → ℝ) :
    quadForm (hess G θ) x
      = (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u - x v) ^ 2 := by
  have hcos : ∀ u v : V, Real.cos (θ v - θ u) = Real.cos (θ u - θ v) := fun u v => by
    rw [← Real.cos_neg, neg_sub]
  -- Step 1: expand the quadratic form into a sum over ordered adjacent pairs.
  have step1 : quadForm (hess G θ) x
      = ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u ^ 2 - x u * x v) := by
    unfold quadForm
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hess_eq_add, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ u
      (fun v => (∑ y ∈ G.neighborFinset u, Real.cos (θ u - θ y)) * x u * x v)]
    simp only [Finset.mem_univ, ite_true]
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : G.Adj u v
    · simp only [ite_eq_left h]; ring
    · simp only [ite_eq_right h]; ring
  rw [step1]
  -- Step 2: expand the square on the right and fold the two endpoint terms together.
  have expand : ∀ u v : V, Real.cos (θ u - θ v) * (x u - x v) ^ 2
      = (Real.cos (θ u - θ v) * x u ^ 2 - Real.cos (θ u - θ v) * (x u * x v))
        + (Real.cos (θ u - θ v) * x v ^ 2 - Real.cos (θ u - θ v) * (x u * x v)) := by
    intro u v; ring
  have hswap : ∑ u, ∑ v ∈ G.neighborFinset u,
        (Real.cos (θ u - θ v) * x v ^ 2 - Real.cos (θ u - θ v) * (x u * x v))
      = ∑ u, ∑ v ∈ G.neighborFinset u,
        (Real.cos (θ u - θ v) * x u ^ 2 - Real.cos (θ u - θ v) * (x u * x v)) := by
    rw [sum_neighbor_comm G (fun u v =>
      Real.cos (θ u - θ v) * x v ^ 2 - Real.cos (θ u - θ v) * (x u * x v))]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hcos, mul_comm (x v) (x u)]
  symm
  calc (1 / 2 : ℝ) * ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u - x v) ^ 2
      = (1 / 2 : ℝ) * ((∑ u, ∑ v ∈ G.neighborFinset u,
            (Real.cos (θ u - θ v) * x u ^ 2 - Real.cos (θ u - θ v) * (x u * x v)))
          + ∑ u, ∑ v ∈ G.neighborFinset u,
            (Real.cos (θ u - θ v) * x v ^ 2 - Real.cos (θ u - θ v) * (x u * x v))) := by
        simp only [expand, Finset.sum_add_distrib]
    _ = ∑ u, ∑ v ∈ G.neighborFinset u,
            (Real.cos (θ u - θ v) * x u ^ 2 - Real.cos (θ u - θ v) * (x u * x v)) := by
        rw [hswap]; ring
    _ = ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (x u ^ 2 - x u * x v) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        ring

/-- `θ` is *phase-cohesive*: every edge has `|Δ_e| < π/2`, the hypothesis `max_e |Δ_e| < π/2` of Proposition 1.3.

We phrase it as `0 < cos (θ u - θ v)`, which is equivalent and, unlike a bound on a chosen
representative `Δ_e ∈ (-π, π]`, is manifestly independent of the lift. -/
def PhaseCohesive (θ : Config V) : Prop := ∀ u v, G.Adj u v → 0 < Real.cos (θ u - θ v)

/-! ### The paper's `Δ_e`, literally

§1.3: `Δ_{uv} ∈ (−π, π]` is the representative of `θ_v − θ_u` modulo `2π`. Mathlib's
`Real.Angle.toReal` is exactly that representative, so `phaseDiff` *is* the paper's `Δ_{uv}`.
The development mostly works with branch-free reformulations (`cos (θ u − θ v) > 0`, "within
`a` of `2πℤ`"); the lemmas below prove that these say the same thing as the paper. -/

/-- **`Δ_{uv}` of §1.3**: the representative of `θ_v − θ_u` modulo `2π` in
`(−π, π]`. -/
noncomputable def phaseDiff (θ : Config V) (u v : V) : ℝ :=
  ((θ v - θ u : ℝ) : Real.Angle).toReal

omit [Fintype V] [DecidableEq V] in
/-- If `θ_v − θ_u − 2πk` already lies in `(−π, π]`, it *is* the representative `Δ_{uv}`. -/
theorem phaseDiff_eq (θ : Config V) (u v : V) (k : ℤ)
    (h1 : -π < θ v - θ u - 2 * π * k) (h2 : θ v - θ u - 2 * π * k ≤ π) :
    phaseDiff θ u v = θ v - θ u - 2 * π * k := by
  have hx : ((θ v - θ u : ℝ) : Real.Angle) = ((θ v - θ u - 2 * π * k : ℝ) : Real.Angle) := by
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]; exact ⟨k, by ring⟩
  rw [phaseDiff, hx]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨h1, h2⟩

omit [Fintype V] [DecidableEq V] in
/-- **The paper's `|Δ_{uv}| ≤ a` is the development's "within `a` of `2πℤ`"**, for `a < π`.
Every hypothesis of the form `∃ k : ℤ, |θ u − θ v − 2πk| ≤ a` is therefore literally the
paper's bound on `Δ_e`. -/
theorem abs_phaseDiff_le_iff (θ : Config V) (u v : V) {a : ℝ} (ha : a < π) :
    |phaseDiff θ u v| ≤ a ↔ ∃ k : ℤ, |θ u - θ v - 2 * π * k| ≤ a := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.coe_toReal ((θ v - θ u : ℝ) : Real.Angle))
    refine ⟨k, ?_⟩
    have e : θ u - θ v - 2 * π * k = -phaseDiff θ u v := by unfold phaseDiff; linarith
    rw [e, abs_neg]; exact h
  · rintro ⟨k, hk⟩
    obtain ⟨h1, h2⟩ := abs_le.mp hk
    rw [phaseDiff_eq θ u v (-k) (by push_cast; linarith) (by push_cast; linarith)]
    rw [show θ v - θ u - 2 * π * ((-k : ℤ) : ℝ) = -(θ u - θ v - 2 * π * k) by push_cast; ring,
      abs_neg]
    exact hk

omit [Fintype V] [DecidableEq V] in
/-- `cos (θ u − θ v) = cos Δ_{uv}`: the cosine does not see the choice of representative. -/
theorem cos_eq_cos_phaseDiff (θ : Config V) (u v : V) :
    Real.cos (θ u - θ v) = Real.cos (phaseDiff θ u v) := by
  rw [phaseDiff, Real.Angle.cos_toReal, Real.Angle.cos_coe, ← Real.cos_neg, neg_sub]

omit [DecidableRel G.Adj] [Fintype V] [DecidableEq V] in
/-- **Phase cohesion is the paper's `max_e |Δ_e| < π/2`.** The development's `PhaseCohesive` (`cos Δ_e > 0` on
every edge) is exactly the paper's `max_e |Δ_e| < π/2`. -/
theorem phaseCohesive_iff (θ : Config V) :
    PhaseCohesive G θ ↔ ∀ u v, G.Adj u v → |phaseDiff θ u v| < π / 2 := by
  have hpi := Real.pi_pos
  constructor
  · intro h u v huv
    have hc := h u v huv
    rw [cos_eq_cos_phaseDiff] at hc
    have h1 := Real.Angle.neg_pi_lt_toReal ((θ v - θ u : ℝ) : Real.Angle)
    have h2 := Real.Angle.toReal_le_pi ((θ v - θ u : ℝ) : Real.Angle)
    change -π < phaseDiff θ u v at h1
    change phaseDiff θ u v ≤ π at h2
    rw [abs_lt]
    constructor
    · by_contra hlo
      push Not at hlo
      have : Real.cos (-phaseDiff θ u v) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
    · by_contra hhi
      push Not at hhi
      have : Real.cos (phaseDiff θ u v) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hhi (by linarith)
      linarith
  · intro h u v huv
    rw [cos_eq_cos_phaseDiff]
    obtain ⟨h1, h2⟩ := abs_lt.mp (h u v huv)
    exact Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩

/-- `θ` is fully synchronized: all phases agree modulo `2π`. -/
def Synchronized (θ : Config V) : Prop := ∀ u v, Real.cos (θ u - θ v) = 1

/-- The tangent directions transverse to the global rotation `θ ↦ θ + c • 1`. -/
def OnePerp (x : V → ℝ) : Prop := ∑ v, x v = 0

/-- A *nondegenerate stable equilibrium*: a critical point whose Hessian is positive definite on
`1ᗮ`. Since `𝓔` is invariant under the global rotation we always have `H(θ) 1 = 0`, so this is
the strongest nondegeneracy a critical point of `𝓔` can have. -/
def StableEquilibrium (θ : Config V) : Prop :=
  IsEquilibrium G θ ∧ ∀ x : V → ℝ, OnePerp x → x ≠ 0 → 0 < quadForm (hess G θ) x

/-- Global rotation invariance: `H(θ) 1 = 0`, so the Hessian is never positive definite on all
of `ℝ^V`. This is the reason for working on `1ᗮ` throughout Section 3. -/
theorem quadForm_hess_one (θ : Config V) : quadForm (hess G θ) (fun _ => (1 : ℝ)) = 0 := by
  rw [quadForm_hess]
  simp

/-- **`G` is globally synchronizing.**

Definition 1.1 of the paper is dynamical: from a uniformly random initial state the gradient
flow converges to a synchronized state with probability one. This is the landscape version:
every stable equilibrium (`∇𝓔 = 0`, `λ₂(H) > 0`) is synchronized. The proof of Theorem 1.2
exhibits a stable non-synchronized equilibrium, which by the remark after Definition 1.1
(Lyapunov stability of a strict local minimum of a gradient flow) rules out global
synchronization in the dynamical sense; that last step is not formalized. -/
def GloballySynchronizing : Prop :=
  ∀ θ : Config V, StableEquilibrium G θ → Synchronized θ

end Kuramoto
