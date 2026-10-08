/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Transplant
public import Kuramoto.Certificate
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Proposition 3.3: correcting `θ̂` to a stable equilibrium

Paper cross-reference:
  * Proposition 3.3 -> `Kuramoto.glue`, and its closing sentence `Kuramoto.glue_consequently`

The transplanted configuration `θ̂` is turned into a genuine equilibrium by Kantorovich's
theorem, following the paper's proof:

> we replace `θ̂` by `θ̂ − mean(θ̂)·1` and work on `1ᗮ`. Set `F = ∇𝓔|_{1ᗮ}`. Since
> `⟨∇𝓔(θ), 1⟩ = 0`, `F` maps `1ᗮ` to itself and `F' = H|_{1ᗮ}`. Since `F'(θ̂)` is invertible
> with `‖F'(θ̂)⁻¹‖ ≤ 1/μ`, we have `h₀ = ‖F'(θ̂)⁻¹ F(θ̂)‖ ≤ ε(R)/μ`. By Lemma 3.2, `F'` is
> `L`-Lipschitz with `L = 6√2`. The condition `α₀ ≤ ½` of Theorem 3.1 holds since
> `R ≥ R₀`. That is, there exists `θ*` with `F(θ*) = 0` and `‖θ* − θ̂‖₂ ≤ 2h₀ ≤ 2ε(R)/μ`.

| paper                                    | here                                   |
|------------------------------------------|----------------------------------------|
| `θ̂ − mean(θ̂)·1`                         | `center`                               |
| `1ᗮ`                                     | `onePerp V`                            |
| `⟨∇𝓔(θ), 1⟩ = 0`                         | `sum_grad`                             |
| `F = ∇𝓔|_{1ᗮ}`, `F' = H|_{1ᗮ}`           | `gradP`, `hessP`                       |
| `F'` is the derivative of `F`            | `hasFDerivAt_gradP`                    |
| `‖F'(θ̂)⁻¹‖ ≤ 1/μ`                        | `exists_hessPEquiv`                    |
| `F'` is `6√2`-Lipschitz                  | `lipschitz_hessP`                      |
| `α₀ ≤ ½`                                 | `kantorovich_condition`                |
| the conclusion                           | `kantorovich_step`                     |

Norms are `ℓ²`. `Config V = V → ℝ` carries the sup norm in Mathlib, which would make the
Kantorovich constants depend on `n`, so everything analytic lives on `EuclideanSpace ℝ V` and
its subspace `1ᗮ`.
-/

@[expose] public section

namespace Kuramoto

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## The gradient lies in `1ᗮ` -/

omit [DecidableEq V] in
/-- `∑_u ∂𝓔/∂θ_u = 0`: the current is antisymmetric, so it sums to zero. This is the
rotation invariance of `𝓔` at the level of the gradient. -/
theorem sum_grad (θ : Config V) : ∑ u, grad G θ u = 0 := by
  have hswap := sum_neighbor_comm G (fun u v => Real.sin (θ u - θ v))
  have hneg : ∑ u, ∑ v ∈ G.neighborFinset u, Real.sin (θ v - θ u)
      = -∑ u, ∑ v ∈ G.neighborFinset u, Real.sin (θ u - θ v) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [← Real.sin_neg, neg_sub]
  simp only [grad]
  linarith

/-! ## The Hessian as an operator on `ℓ²` -/

/-- `(H(θ) y)_u = ∑_{v ∼ u} cos (θ u - θ v) (y u - y v)`. -/
noncomputable def hessApply (θ : Config V) (y : V → ℝ) : V → ℝ :=
  fun u => ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (y u - y v)

/-- The Hessian `H(θ)` as a continuous linear map on `EuclideanSpace ℝ V`. -/
noncomputable def hessL (θ : Config V) : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (hessApply G θ y.ofLp)
      map_add' := fun y z => by
        ext u
        simp only [hessApply, PiLp.add_apply,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      map_smul' := fun c y => by
        ext u
        simp only [hessApply, PiLp.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring }

omit [DecidableEq V] in
theorem hessL_apply (θ : Config V) (y : EuclideanSpace ℝ V) (u : V) :
    hessL G θ y u = ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (y u - y v) := rfl

omit [DecidableEq V] in
/-- `H` maps into `1ᗮ`: `∑_u (H y)_u = 0`, by the same antisymmetry as `sum_grad`. -/
theorem sum_hessL (θ : Config V) (y : EuclideanSpace ℝ V) : ∑ u, hessL G θ y u = 0 := by
  have hcos : ∀ u v : V, Real.cos (θ v - θ u) = Real.cos (θ u - θ v) := fun u v => by
    rw [← Real.cos_neg, neg_sub]
  have hswap := sum_neighbor_comm G (fun u v => Real.cos (θ u - θ v) * (y u - y v))
  have hneg : ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ v - θ u) * (y v - y u)
      = -∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (y u - y v) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hcos]; ring
  simp only [hessL_apply]
  linarith

/-! ## The subspace `1ᗮ` and the centering -/

variable (V) in
/-- `1ᗮ`: the configurations orthogonal to the rotation mode, `∑_v θ_v = 0`. -/
def onePerp : Submodule ℝ (EuclideanSpace ℝ V) where
  carrier := {z | ∑ v, z v = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, PiLp.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c z hz => by
    simp only [Set.mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum] at *
    rw [hz, mul_zero]

omit [DecidableEq V] in
theorem mem_onePerp {z : EuclideanSpace ℝ V} : z ∈ onePerp V ↔ ∑ v, z v = 0 := Iff.rfl

instance : CompleteSpace (onePerp V) := FiniteDimensional.complete ℝ _

/-- `θ − mean(θ)·1`: the paper's "we replace `θ̂` by `θ̂ − mean(θ̂)·1`". -/
noncomputable def center (θ : Config V) : Config V :=
  fun v => θ v - (∑ w, θ w) / Fintype.card V

omit [DecidableEq V] in
theorem sum_center (hn : 0 < Fintype.card V) (θ : Config V) : ∑ v, center θ v = 0 := by
  have hn' : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [center, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [DecidableEq V] in
/-- Centering does not change a single phase difference. -/
theorem center_sub (θ : Config V) (u v : V) : center θ u - center θ v = θ u - θ v := by
  simp only [center]; ring

omit [DecidableEq V] in
/-- …so it changes neither the gradient… -/
theorem grad_center (θ : Config V) : grad G (center θ) = grad G θ := by
  funext x
  simp only [grad, center_sub]

omit [DecidableEq V] in
/-- …nor the Hessian. -/
theorem hessL_center (θ : Config V) : hessL G (center θ) = hessL G θ := by
  ext y u
  simp only [hessL_apply, center_sub]

/-! ## `F = ∇𝓔|_{1ᗮ}` and `F' = H|_{1ᗮ}` -/

/-- The gradient as a map on `EuclideanSpace ℝ V`. -/
noncomputable def gradFull (θ : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (grad G (fun v => θ v))

omit [DecidableEq V] in
/-- **`D(∇𝓔) = H`.** Componentwise, the derivative of `∑_{v ∼ u} sin (θ_u − θ_v)` in the
direction `y` is `∑_{v ∼ u} cos (θ_u − θ_v) (y_u − y_v) = (H y)_u`. -/
theorem hasFDerivAt_gradFull (θ : EuclideanSpace ℝ V) :
    HasFDerivAt (gradFull G) (hessL G (fun v => θ v)) θ := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro u
  rw [hasFDerivWithinAt_univ]
  have hinner : ∀ v, HasFDerivAt (fun z : EuclideanSpace ℝ V => z u - z v)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : V => ℝ) u - PiLp.proj (𝕜 := ℝ) 2 (fun _ : V => ℝ) v) θ :=
    fun v => (PiLp.hasFDerivAt_apply 2 θ u).sub (PiLp.hasFDerivAt_apply 2 θ v)
  have hsum := HasFDerivAt.fun_sum (u := G.neighborFinset u) (fun v _ => (hinner v).sin)
  refine hsum.congr_fderiv ?_
  ext y
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, sub_apply, PiLp.proj_apply, smul_eq_mul,
    ContinuousLinearMap.coe_comp, Function.comp_apply, hessL_apply]

/-- `F = ∇𝓔|_{1ᗮ}`. It maps `1ᗮ` to itself because `⟨∇𝓔(θ), 1⟩ = 0`. -/
noncomputable def gradP (θ : onePerp V) : onePerp V :=
  ⟨gradFull G θ, (mem_onePerp).mpr (sum_grad G _)⟩

/-- `F' = H|_{1ᗮ}`. It maps `1ᗮ` to itself because `H` does. -/
noncomputable def hessP (θ : Config V) : onePerp V →L[ℝ] onePerp V :=
  ((hessL G θ).comp (onePerp V).subtypeL).codRestrict (onePerp V)
    (fun _ => (mem_onePerp).mpr (sum_hessL G θ _))

omit [DecidableEq V] in
theorem coe_hessP_apply (θ : Config V) (y : onePerp V) :
    ((hessP G θ y : onePerp V) : EuclideanSpace ℝ V) = hessL G θ y := rfl

omit [DecidableEq V] in
theorem hessP_center (θ : Config V) : hessP G (center θ) = hessP G θ := by
  simp only [hessP, hessL_center]

omit [DecidableEq V] in
/-- A map into a subspace has a derivative as soon as its composite with the inclusion does:
the inclusion is an isometry, so the `o(‖h‖)` remainder is the same inside and outside.
Mathlib has this for isomorphisms (`comp_hasFDerivAt_iff`) but not for inclusions. -/
theorem hasFDerivAt_of_comp_subtype {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S : Submodule ℝ (EuclideanSpace ℝ V)} {f : W → S} {f' : W →L[ℝ] S} {x : W}
    (h : HasFDerivAt (fun y => (f y : EuclideanSpace ℝ V)) (S.subtypeL.comp f') x) :
    HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  refine h.congr_left fun y => ?_
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [← Submodule.coe_sub, ← Submodule.coe_sub, Submodule.norm_coe]

omit [DecidableEq V] in
/-- **`F'` is the derivative of `F`.** -/
theorem hasFDerivAt_gradP (θ : onePerp V) :
    HasFDerivAt (gradP G) (hessP G (fun v => (θ : EuclideanSpace ℝ V) v)) θ := by
  apply hasFDerivAt_of_comp_subtype
  have h := (hasFDerivAt_gradFull G (θ : EuclideanSpace ℝ V)).comp θ
    (onePerp V).subtypeL.hasFDerivAt
  exact h.congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)

/-! ## The Hessian is Lipschitz, in operator norm

Lemma 3.2 bounds the *quadratic form* `⟨x, (H - H') x⟩`. Kantorovich needs the *operator norm*
`‖H - H'‖`, which for a symmetric operator is the same number but is a different statement.
Rather than go through the self-adjoint characterization of the norm, we bound it directly;
the constant comes out the same, `6√2`. -/

omit [DecidableEq V] in
/-- The `ℓ²` norm on `EuclideanSpace ℝ V`, spelled out. -/
theorem norm_eucl (x : EuclideanSpace ℝ V) : ‖x‖ = Real.sqrt (∑ v, x v ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]

theorem norm_hessL_sub_le (hreg : ∀ v, G.degree v = 3) (θ θ' : Config V) :
    ‖hessL G θ - hessL G θ'‖ ≤ 6 * Real.sqrt 2 * Real.sqrt (∑ v, (θ v - θ' v) ^ 2) := by
  set N : ℝ := Real.sqrt 2 * Real.sqrt (∑ v, (θ v - θ' v) ^ 2) with hN
  have hN0 : 0 ≤ N := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have hcomp : ∀ u, (hessL G θ - hessL G θ') y u
      = ∑ v ∈ G.neighborFinset u,
          (Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (y u - y v) := by
    intro u
    rw [sub_apply, PiLp.sub_apply, hessL_apply, hessL_apply,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  -- each weight moves by at most `√2 ‖θ - θ'‖`
  have hc : ∀ u, ∀ v ∈ G.neighborFinset u,
      |Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)| ≤ N := by
    intro u v hv
    have huv : u ≠ v := G.ne_of_adj ((G.mem_neighborFinset u v).mp hv)
    refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
    have e : (θ u - θ v) - (θ' u - θ' v)
        = (fun z => θ z - θ' z) u - (fun z => θ z - θ' z) v := by ring
    rw [e]
    exact abs_sub_le_sqrt_two_mul (w := fun z => θ z - θ' z) huv
  -- per component: `((H - H')y)_u² ≤ 3 N² ∑_{v ∼ u} (y_u - y_v)²`, by Cauchy–Schwarz on 3 terms
  have hu : ∀ u, ((hessL G θ - hessL G θ') y u) ^ 2
      ≤ 3 * N ^ 2 * ∑ v ∈ G.neighborFinset u, (y u - y v) ^ 2 := by
    intro u
    rw [hcomp u]
    have h1 : |∑ v ∈ G.neighborFinset u,
          (Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (y u - y v)|
        ≤ N * ∑ v ∈ G.neighborFinset u, |y u - y v| := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun v hv => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc u v hv) (abs_nonneg _)
    have h2 : (∑ v ∈ G.neighborFinset u, |y u - y v|) ^ 2
        ≤ 3 * ∑ v ∈ G.neighborFinset u, (y u - y v) ^ 2 := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := G.neighborFinset u) (f := fun v => |y u - y v|)
      rw [SimpleGraph.card_neighborFinset_eq_degree, hreg u] at hcs
      simpa only [sq_abs, Nat.cast_ofNat] using hcs
    have hS : 0 ≤ ∑ v ∈ G.neighborFinset u, |y u - y v| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc (∑ v ∈ G.neighborFinset u,
            (Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (y u - y v)) ^ 2
        = |∑ v ∈ G.neighborFinset u,
            (Real.cos (θ u - θ v) - Real.cos (θ' u - θ' v)) * (y u - y v)| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (N * ∑ v ∈ G.neighborFinset u, |y u - y v|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = N ^ 2 * (∑ v ∈ G.neighborFinset u, |y u - y v|) ^ 2 := by ring
      _ ≤ N ^ 2 * (3 * ∑ v ∈ G.neighborFinset u, (y u - y v) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg N)
      _ = 3 * N ^ 2 * ∑ v ∈ G.neighborFinset u, (y u - y v) ^ 2 := by ring
  -- sum over `u`, and use `‖B y‖² ≤ 12 ‖y‖²`
  have htot : ∑ u, ((hessL G θ - hessL G θ') y u) ^ 2 ≤ 36 * N ^ 2 * ∑ u, y u ^ 2 := by
    calc ∑ u, ((hessL G θ - hessL G θ') y u) ^ 2
        ≤ ∑ u, 3 * N ^ 2 * ∑ v ∈ G.neighborFinset u, (y u - y v) ^ 2 :=
          Finset.sum_le_sum fun u _ => hu u
      _ = 3 * N ^ 2 * ∑ u, ∑ v ∈ G.neighborFinset u, (y u - y v) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ 3 * N ^ 2 * (12 * ∑ u, y u ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_sq_diff_le G hreg (fun u => y u)) (by positivity)
      _ = 36 * N ^ 2 * ∑ u, y u ^ 2 := by ring
  rw [norm_eucl, norm_eucl]
  have e : 6 * Real.sqrt 2 * Real.sqrt (∑ v, (θ v - θ' v) ^ 2) * Real.sqrt (∑ u, y u ^ 2)
      = Real.sqrt (36 * N ^ 2 * ∑ u, y u ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hN0,
      show Real.sqrt 36 = 6 by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num), hN]
    ring
  rw [e]
  exact Real.sqrt_le_sqrt htot

/-- **`F'` is `6√2`-Lipschitz** (Lemma 3.2, in operator norm). Restricting to `1ᗮ` can only
decrease the norm. -/
theorem lipschitz_hessP (hreg : ∀ v, G.degree v = 3) :
    LipschitzWith (Real.toNNReal (6 * Real.sqrt 2))
      (fun θ : onePerp V => hessP G (fun v => (θ : EuclideanSpace ℝ V) v)) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  set θa : Config V := fun v => (a : EuclideanSpace ℝ V) v
  set θb : Config V := fun v => (b : EuclideanSpace ℝ V) v
  have hres : ‖hessP G θa - hessP G θb‖ ≤ ‖hessL G θa - hessL G θb‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    calc ‖(hessP G θa - hessP G θb) y‖
        = ‖(hessL G θa - hessL G θb) (y : EuclideanSpace ℝ V)‖ := by
          rw [← Submodule.norm_coe]; rfl
      _ ≤ ‖hessL G θa - hessL G θb‖ * ‖(y : EuclideanSpace ℝ V)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖hessL G θa - hessL G θb‖ * ‖y‖ := by rw [Submodule.norm_coe]
  refine le_trans hres (le_trans (norm_hessL_sub_le G hreg θa θb) (le_of_eq ?_))
  rw [← Submodule.norm_coe, Submodule.coe_sub, norm_eucl]
  congr 2

/-- `⟨H(θ) y, y⟩` is the quadratic form of `hess`, so the spectral hypothesis of
Proposition 3.3 (stated with `quadForm`) applies to the operator `hessL`. -/
theorem inner_hessL_self (θ : Config V) (y : EuclideanSpace ℝ V) :
    inner ℝ (hessL G θ y) y = quadForm (hess G θ) (fun u => y u) := by
  have hcos : ∀ u v : V, Real.cos (θ v - θ u) = Real.cos (θ u - θ v) := fun u v => by
    rw [← Real.cos_neg, neg_sub]
  rw [quadForm_hess, PiLp.inner_apply]
  simp only [hessL_apply, RCLike.inner_apply, conj_trivial]
  -- symmetrize: `∑∑ c (y_u - y_v) y_v = -∑∑ c (y_u - y_v) y_u`
  set A : ℝ := ∑ u, ∑ v ∈ G.neighborFinset u, y u * (Real.cos (θ u - θ v) * (y u - y v))
  have hB : ∑ u, ∑ v ∈ G.neighborFinset u, y v * (Real.cos (θ u - θ v) * (y u - y v)) = -A := by
    rw [sum_neighbor_comm G (fun u v => y v * (Real.cos (θ u - θ v) * (y u - y v))),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hcos]; ring
  have hsq : ∑ u, ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (y u - y v) ^ 2
      = A - ∑ u, ∑ v ∈ G.neighborFinset u, y v * (Real.cos (θ u - θ v) * (y u - y v)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsq, hB]
  have hA : ∑ u, y u * ∑ v ∈ G.neighborFinset u, Real.cos (θ u - θ v) * (y u - y v) = A :=
    Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
  rw [hA]
  ring

/-! ## `F'(θ̂)` is invertible, with `‖F'(θ̂)⁻¹‖ ≤ 1/μ` -/

/-- On `1ᗮ` the spectral gap is exactly the hypothesis: `μ ‖z‖ ≤ ‖H z‖`. -/
theorem norm_hessP_ge (θhat : Config V) {μ : ℝ}
    (hspec : ∀ x : V → ℝ, OnePerp x → x ≠ 0 → μ * (∑ v, x v ^ 2) ≤ quadForm (hess G θhat) x)
    (z : onePerp V) : μ * ‖z‖ ≤ ‖hessP G θhat z‖ := by
  have hco : μ * ‖z‖ ^ 2 ≤ inner ℝ (hessP G θhat z) z := by
    rw [Submodule.coe_inner, coe_hessP_apply, inner_hessL_self, ← Submodule.norm_coe, norm_eucl,
      Real.sq_sqrt (by positivity)]
    by_cases hz0 : (fun u => (z : EuclideanSpace ℝ V) u) = 0
    · have hzv : ∀ v, (z : EuclideanSpace ℝ V) v = 0 := fun v => congrFun hz0 v
      rw [hz0]
      simp [hzv, quadForm]
    · exact hspec _ ((mem_onePerp).mp z.2) hz0
  have hcs := real_inner_le_norm (hessP G θhat z) z
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h]; simp
  · nlinarith

/-- **`F'(θ̂)` is an isomorphism of `1ᗮ` with `‖F'(θ̂)⁻¹‖ ≤ 1/μ`.** Injective by the spectral
gap, hence bijective in finite dimension; the norm bound is `μ ‖z‖ ≤ ‖H z‖` read backwards. -/
theorem exists_hessPEquiv (θhat : Config V) {μ : ℝ} (hμ : 0 < μ)
    (hspec : ∀ x : V → ℝ, OnePerp x → x ≠ 0 → μ * (∑ v, x v ^ 2) ≤ quadForm (hess G θhat) x) :
    ∃ A : onePerp V ≃L[ℝ] onePerp V,
      (A : onePerp V →L[ℝ] onePerp V) = hessP G θhat ∧
      ‖(A.symm : onePerp V →L[ℝ] onePerp V)‖ ≤ 1 / μ := by
  have hinj : Function.Injective (hessP G θhat) := by
    intro a b hab
    have h := norm_hessP_ge G θhat hspec (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h
    have hn : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  set A := (LinearEquiv.ofInjectiveEndo (hessP G θhat).toLinearMap hinj).toContinuousLinearEquiv
    with hA
  have hcoe : (A : onePerp V →L[ℝ] onePerp V) = hessP G θhat :=
    ContinuousLinearMap.ext fun _ => rfl
  refine ⟨A, hcoe, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_⟩
  have hz : hessP G θhat (A.symm y) = y := by rw [← hcoe]; exact A.apply_symm_apply y
  have hge := norm_hessP_ge G θhat hspec (A.symm y)
  rw [hz] at hge
  show ‖A.symm y‖ ≤ 1 / μ * ‖y‖
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hμ]
  linarith

/-! ## The Kantorovich condition `α₀ ≤ 1/2` -/

/-- The second entry of `R₀` is exactly what makes `α₀ = K ‖F'(0)⁻¹‖ h₀ ≤ ½`, with
`K = 6√2`, `‖F'(0)⁻¹‖ ≤ 1/μ` and `h₀ ≤ ε_ℓ(R)/μ`. -/
theorem kantorovich_condition {ℓ R : ℕ} {μ δ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hR : R₀ μ δ ℓ ≤ R) :
    6 * Real.sqrt 2 * (1 / μ) * (gradNorm ℓ R / μ) ≤ 1 / 2 := by
  have hR1 : 1 ≤ R := by have := four_le_of_R₀_le hR; omega
  have hsl : (0 : ℝ) < Real.sqrt (2 * ℓ) := Real.sqrt_pos.mpr (by positivity)
  set c : ℝ := 12 * Real.sqrt (2 * ℓ) / μ ^ 2 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set t : ℝ := ((R - 1 : ℕ) : ℝ) / 2 with ht
  have hRcast : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by push_cast [Nat.cast_sub hR1]; ring
  have hR2 : (R : ℝ) ≥ 1 + 2 * Real.logb 2 c :=
    le_trans (Nat.le_ceil _)
      (Nat.cast_le.mpr (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR))
  have htlog : Real.logb 2 c ≤ t := by rw [ht, hRcast]; linarith
  have hpow0 : (0 : ℝ) < (1 / 2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hpow : (1 / 2 : ℝ) ^ t ≤ 1 / c := by
    have e1 : (1 / 2 : ℝ) ^ t = (2 : ℝ) ^ (-t) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), one_div,
        ← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
    have e2 : (1 : ℝ) / c = (2 : ℝ) ^ (-Real.logb 2 c) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) hc0, one_div]
    rw [e1, e2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hgn : gradNorm ℓ R ≤ Real.sqrt ℓ * (1 / 2 : ℝ) ^ t := by
    rw [gradNorm, ← ht]
    calc Real.sqrt ℓ * Real.sin (Gadget.root R) * (1 / 2 : ℝ) ^ t
        = (Real.sqrt ℓ * (1 / 2 : ℝ) ^ t) * Real.sin (Gadget.root R) := by ring
      _ ≤ (Real.sqrt ℓ * (1 / 2 : ℝ) ^ t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
      _ = Real.sqrt ℓ * (1 / 2 : ℝ) ^ t := by ring
  have hsplit : Real.sqrt 2 * Real.sqrt (ℓ : ℝ) = Real.sqrt (2 * ℓ) :=
    (Real.sqrt_mul (by norm_num) _).symm
  have hkey : 6 * Real.sqrt 2 * gradNorm ℓ R ≤ μ ^ 2 / 2 := by
    have h1 : 6 * Real.sqrt 2 * gradNorm ℓ R ≤ 6 * Real.sqrt (2 * ℓ) * (1 / 2 : ℝ) ^ t := by
      rw [← hsplit]
      nlinarith [Real.sqrt_nonneg 2, hgn]
    have h2 : 6 * Real.sqrt (2 * ℓ) * (1 / 2 : ℝ) ^ t ≤ 6 * Real.sqrt (2 * ℓ) * (1 / c) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h3 : 6 * Real.sqrt (2 * ℓ) * (1 / c) = μ ^ 2 / 2 := by
      rw [hc]; field_simp; ring
    linarith
  calc 6 * Real.sqrt 2 * (1 / μ) * (gradNorm ℓ R / μ)
      = (6 * Real.sqrt 2 * gradNorm ℓ R) / μ ^ 2 := by field_simp
    _ ≤ (μ ^ 2 / 2) / μ ^ 2 := by gcongr
    _ = 1 / 2 := by field_simp

/-! ## Applying Kantorovich -/

/-- **The Kantorovich step of Proposition 3.3**, following the paper line by line. If the
Hessian at `θ̂` has spectral gap `μ` on `1ᗮ` and the gradient is small enough that
`6√2 · (1/μ) · (ε/μ) ≤ ½`, there is an equilibrium `θ* ∈ 1ᗮ` with `‖θ* − θ̂‖₂ ≤ 2ε/μ`, where
`θ̂` has been centered. -/
theorem kantorovich_step (hreg : ∀ v, G.degree v = 3) (hG : G.Connected)
    (θhat : Config V) {μ : ℝ} (hμ : 0 < μ) {ε : ℝ}
    (hspec : ∀ x : V → ℝ, OnePerp x → x ≠ 0 → μ * (∑ v, x v ^ 2) ≤ quadForm (hess G θhat) x)
    (hgrad : Real.sqrt (∑ v, grad G θhat v ^ 2) ≤ ε)
    (hcond : 6 * Real.sqrt 2 * (1 / μ) * (ε / μ) ≤ 1 / 2) :
    ∃ θstar : Config V, OnePerp θstar ∧ IsEquilibrium G θstar ∧
      Real.sqrt (∑ v, (θstar v - center θhat v) ^ 2) ≤ 2 * ε / μ := by
  obtain ⟨u₀⟩ := hG.nonempty
  have : Nonempty V := ⟨u₀⟩
  -- "we replace `θ̂` by `θ̂ − mean(θ̂)·1` and work on `1ᗮ`"
  set θ₀ : onePerp V :=
    ⟨WithLp.toLp 2 (center θhat), (mem_onePerp).mpr (sum_center Fintype.card_pos θhat)⟩
  have hθ₀ : (fun v => (θ₀ : EuclideanSpace ℝ V) v) = center θhat := rfl
  -- "Set `F = ∇𝓔|_{1ᗮ}`. Since `⟨∇𝓔(θ),1⟩ = 0`, `F` maps `1ᗮ` to itself and `F' = H|_{1ᗮ}`":
  -- these are `gradP`, `hessP` and `hasFDerivAt_gradP`.
  -- "Since `F'(θ̂)` is invertible with `‖F'(θ̂)⁻¹‖ ≤ 1/μ` …"
  obtain ⟨A, hA, hAn⟩ := exists_hessPEquiv G θhat hμ hspec
  have hA0 : (A : onePerp V →L[ℝ] onePerp V) = hessP G (fun v => (θ₀ : EuclideanSpace ℝ V) v) := by
    rw [hA, hθ₀, hessP_center]
  -- "… we have `h₀ = ‖F'(θ̂)⁻¹ F(θ̂)‖ ≤ ε(R)/μ`"
  have hF0 : ‖gradP G θ₀‖ ≤ ε := by
    rw [← Submodule.norm_coe, norm_eucl]
    show Real.sqrt (∑ v, grad G (center θhat) v ^ 2) ≤ ε
    rw [grad_center]; exact hgrad
  set h₀ : ℝ := ‖A.symm (gradP G θ₀)‖ with hh₀
  have hh₀le : h₀ ≤ ε / μ := by
    calc h₀ ≤ ‖(A.symm : onePerp V →L[ℝ] onePerp V)‖ * ‖gradP G θ₀‖ :=
          (A.symm : onePerp V →L[ℝ] onePerp V).le_opNorm _
      _ ≤ (1 / μ) * ε := mul_le_mul hAn hF0 (norm_nonneg _) (by positivity)
      _ = ε / μ := by ring
  -- "By Lemma 3.2, `F'` is `L`-Lipschitz with `L = 6√2`": `lipschitz_hessP`.
  -- "The condition `α₀ ≤ ½` of Theorem 3.1 holds"
  have hα : 6 * Real.sqrt 2 * ‖(A.symm : onePerp V →L[ℝ] onePerp V)‖ * h₀ ≤ 1 / 2 := by
    refine le_trans ?_ hcond
    have h1 := mul_le_mul_of_nonneg_left hAn (by positivity : (0 : ℝ) ≤ 6 * Real.sqrt 2)
    exact mul_le_mul h1 hh₀le (norm_nonneg _) (by positivity)
  -- "That is, there exists `θ*` such that `F(θ*) = 0` and `‖θ* − θ̂‖₂ ≤ 2h₀`."
  obtain ⟨θstar, hF, hd⟩ := NK.newton_kantorovich (gradP G)
    (fun θ => hessP G (fun v => (θ : EuclideanSpace ℝ V) v)) (hasFDerivAt_gradP G)
    (6 * Real.sqrt 2) (lipschitz_hessP G hreg) θ₀ A hA0 h₀ hh₀ hα
  refine ⟨fun v => (θstar : EuclideanSpace ℝ V) v, (mem_onePerp).mp θstar.2, fun u => ?_, ?_⟩
  · -- `F(θ*) = 0` says `∇𝓔(θ*) = 0`
    have := congrArg (fun w : onePerp V => (w : EuclideanSpace ℝ V) u) hF
    simpa only [gradP, gradFull, PiLp.toLp_apply, Submodule.coe_zero, PiLp.zero_apply] using this
  · rw [← Submodule.norm_coe, Submodule.coe_sub, norm_eucl] at hd
    calc Real.sqrt (∑ v, ((θstar : EuclideanSpace ℝ V) v - center θhat v) ^ 2)
        = Real.sqrt (∑ v, (((θstar : EuclideanSpace ℝ V) - (θ₀ : EuclideanSpace ℝ V)) v) ^ 2) := by
          congr 1
      _ ≤ 2 * h₀ := hd
      _ ≤ 2 * (ε / μ) := by linarith
      _ = 2 * ε / μ := by ring

/-! ## The transplant `θ̂` -/

/-- The leaves of the gadget carry phase `0` at `η*(R)`: that is the definition of `η*`
(Proposition 2.1 (iii)). -/
theorem leaf_phase_root {ℓ R : ℕ} [NeZero ℓ] (hR : 4 ≤ R) :
    ∀ w : Gadget.Vtx ℓ R, Gadget.Vtx.IsLeaf ℓ R w → Gadget.phase ℓ R (Gadget.root R) w = 0 := by
  obtain ⟨hmem, hzero⟩ := Gadget.root_spec hR
  exact fun w hw => (Gadget.leaf_phase_eq_zero_iff ℓ R hmem.1 hmem.2 w hw).mpr hzero

omit [DecidableRel G.Adj] [Fintype V] in
/-- "Proposition 2.1 applies, and since every edge not in `Q_{ℓ,R}` joins two vertices of the
same phase, `|Δ_e(θ̂)| ≤ η*(R)` for every `e ∈ E(G)`." -/
theorem transplant_near {ℓ R : ℕ} [NeZero ℓ] {f : Gadget.Vtx ℓ R → V}
    (hball : IsGadgetBall G ℓ R f) (hℓ4 : ℓ % 4 = 0) (hR : 4 ≤ R) :
    ∀ u v, G.Adj u v → ∃ k : ℤ,
      |transplant ℓ R f (Gadget.root R) u - transplant ℓ R f (Gadget.root R) v - 2 * π * k|
        ≤ Gadget.root R := by
  obtain ⟨hmem, _⟩ := Gadget.root_spec hR
  have hleaf := leaf_phase_root (ℓ := ℓ) hR
  -- a gadget vertex adjacent to the outside is a leaf, hence carries phase `0`
  have hzero_of_out : ∀ w y, G.Adj (f w) y → y ∉ Set.range f →
      transplant ℓ R f (Gadget.root R) (f w) = 0 := by
    intro w y hy hyr
    rw [transplant_apply hball.inj]
    by_contra hne
    exact hyr (hball.interior w (fun hl => hne (hleaf w hl)) y hy)
  have hsmall : ∀ k : ℤ, k = 0 → |(0 : ℝ) - 0 - 2 * π * k| ≤ Gadget.root R := by
    rintro k rfl; simp [hmem.1.le]
  intro u v huv
  by_cases hu : u ∈ Set.range f <;> by_cases hv : v ∈ Set.range f
  · obtain ⟨w, rfl⟩ := hu
    obtain ⟨w', rfl⟩ := hv
    rw [transplant_apply hball.inj, transplant_apply hball.inj]
    exact Gadget.phase_diff_near ℓ R hℓ4 hmem.1 hmem.2 ((hball.adj_iff w w').mp huv)
  · obtain ⟨w, rfl⟩ := hu
    refine ⟨0, ?_⟩
    rw [hzero_of_out w v huv hv, transplant_off _ hv]
    exact hsmall 0 rfl
  · obtain ⟨w', rfl⟩ := hv
    refine ⟨0, ?_⟩
    rw [hzero_of_out w' u huv.symm hu, transplant_off _ hu]
    exact hsmall 0 rfl
  · refine ⟨0, ?_⟩
    rw [transplant_off _ hu, transplant_off _ hv]
    exact hsmall 0 rfl


/-! ## Non-triviality: the cycle edge with `Δ₁₂(θ̂) = η*` -/

/-- Vertex `0` of the cycle has sign `+`, and one of its two cycle neighbours has sign `−`. The
real difference across that edge is `2t = 2π − η`, i.e. `Δ₁₂ = η` modulo `2π`. -/
theorem exists_cycle_edge {ℓ R : ℕ} [NeZero ℓ] (hℓ4 : ℓ % 4 = 0) (hℓ3 : 3 ≤ ℓ) (η : ℝ) :
    ∃ j : ZMod ℓ, (Gadget.Q ℓ R).Adj (Gadget.Vtx.cyc 0) (Gadget.Vtx.cyc j) ∧
      Gadget.phase ℓ R η (Gadget.Vtx.cyc 0) - Gadget.phase ℓ R η (Gadget.Vtx.cyc j)
        = 2 * π - η := by
  have hs0 : Gadget.sgn (0 : ZMod ℓ).val = 1 := by
    rw [ZMod.val_zero]; exact Gadget.sgn_eq_one (Or.inl (by norm_num))
  obtain ⟨hne1, hne2⟩ := Gadget.cyc_ne_succ ℓ (by omega) (0 : ZMod ℓ)
  rcases Gadget.sgn_neighbors ℓ hℓ4 0 with ⟨_, hb⟩ | ⟨ha, _⟩
  · refine ⟨0 - 1, ?_, ?_⟩
    · rw [Gadget.adj_cyc_cyc]; exact ⟨hne2, Or.inr (by ring)⟩
    · rw [Gadget.phase_cyc, Gadget.phase_cyc, hb, hs0]; ring
  · refine ⟨0 + 1, ?_, ?_⟩
    · rw [Gadget.adj_cyc_cyc]; exact ⟨hne1, Or.inl rfl⟩
    · rw [Gadget.phase_cyc, Gadget.phase_cyc, ha, hs0]; ring

omit [Fintype V] [DecidableEq V] in
/-- "moreover `Δ₁₂(θ̂) = η*(R)`": across the cycle edge of `exists_cycle_edge` the real
difference of the transplant is `2π − η*`, whose representative (§1.3) is `η*`. -/
theorem phaseDiff_transplant_cycle_edge {ℓ R : ℕ} [NeZero ℓ] {f : Gadget.Vtx ℓ R → V}
    (hf : Function.Injective f) (hR : 4 ≤ R) {j : ZMod ℓ}
    (hdiff : Gadget.phase ℓ R (Gadget.root R) (Gadget.Vtx.cyc 0)
      - Gadget.phase ℓ R (Gadget.root R) (Gadget.Vtx.cyc j) = 2 * π - Gadget.root R) :
    phaseDiff (transplant ℓ R f (Gadget.root R)) (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j))
      = Gadget.root R := by
  obtain ⟨hmem, _⟩ := Gadget.root_spec hR
  have hpi := Real.pi_pos
  have h : transplant ℓ R f (Gadget.root R) (f (Gadget.Vtx.cyc j))
      - transplant ℓ R f (Gadget.root R) (f (Gadget.Vtx.cyc 0)) = Gadget.root R - 2 * π := by
    rw [transplant_apply hf, transplant_apply hf]; linarith
  rw [phaseDiff_eq _ _ _ (-1) (by push_cast; linarith [hmem.1, hmem.2])
    (by push_cast; linarith [hmem.1, hmem.2]), h]
  push_cast; ring

/-- A positive lower bound `λ₂(H(θ)) ≥ μ > 0` on `1ᗮ` forces `G` to be connected: the centered
indicator of a connected component is a nonzero vector of `1ᗮ` on which every edge term of
`⟨H(θ) x, x⟩ = ½ ∑ cos(θ_u − θ_v)(x_u − x_v)²` vanishes. The paper uses connectedness of `G`
implicitly; in Proposition 3.3 it is a consequence of the hypothesis `λ₂(H(θ̂)) ≥ μ`. -/
theorem connected_of_hess_gap [Nonempty V] (θ : Config V) {μ : ℝ} (hμ : 0 < μ)
    (hspec : ∀ x : V → ℝ, OnePerp x → x ≠ 0 → μ * (∑ v, x v ^ 2) ≤ quadForm (hess G θ) x) :
    G.Connected := by
  refine ⟨fun u v => ?_⟩
  by_contra hne
  classical
  set x : V → ℝ := fun w => if G.Reachable u w then 1 else 0 with hx
  have hy : OnePerp (center x) := sum_center Fintype.card_pos x
  have hq : quadForm (hess G θ) (center x) = 0 := by
    rw [quadForm_hess]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b hb => ?_)
    have hab : G.Adj a b := (G.mem_neighborFinset a b).mp hb
    have hxab : x a = x b := by
      simp only [hx]
      by_cases ha : G.Reachable u a
      · rw [ite_eq_left ha, ite_eq_left (ha.trans hab.reachable)]
      · rw [ite_eq_right ha, ite_eq_right fun hb' => ha (hb'.trans hab.symm.reachable)]
    rw [center_sub, hxab, sub_self]; ring
  have hxuv : center x u - center x v = 1 := by
    rw [center_sub]; simp only [hx, ite_eq_left (SimpleGraph.Reachable.refl u), ite_eq_right hne]; ring
  have hy0 : center x ≠ 0 := by
    intro h; rw [h] at hxuv; simp at hxuv
  have hpos : 0 < ∑ w, center x w ^ 2 := by
    obtain ⟨w, hw⟩ : ∃ w, center x w ≠ 0 := by
      by_contra h; push Not at h; exact hy0 (funext h)
    exact Finset.sum_pos' (fun w _ => sq_nonneg _) ⟨w, Finset.mem_univ w, by positivity⟩
  have := hspec (center x) hy hy0
  rw [hq] at this
  nlinarith

/-! ## Proposition 3.3 -/

/-- **Proposition 3.3.** Let `ℓ ≡ 0 (mod 4)`, fix `δ ∈ (0, δ₀]` with `δ₀` as in
Proposition 2.1 (iii), let `μ > 0`, let `R ≥ R₀(μ, δ, ℓ)`, and let `G` be a `3`-regular graph
containing `Q_{ℓ,R}` as an induced subgraph (`IsInducedCopy`). Let `θ̂` be the transplant of `θ^{η*}` (centered
as in the paper). If `λ₂(H(θ̂)) ≥ μ`, then there exists `θ* ∈ 1ᗮ` with

  (i)   `‖θ* − θ̂‖₂ ≤ 2 ε_ℓ(R)/μ`, where `ε_ℓ(R) = √ℓ · sin η*(R) · 2^{-(R-1)/2}`;
  (ii)  `max_e |Δ_e(θ*)| < π/2`;
  (iii) `∇𝓔(θ*) = 0` and `Δ₁₂(θ*) ≥ η*(R) − δ > 0`.

The cycle vertices `1, 2` of the paper are `f (cyc 0)` and `f (cyc j)`, where `cyc j` is the
cycle neighbour of `cyc 0` of opposite sign, so that `Δ₁₂(θ̂) = η*(R)`; this is also part of
the conclusion.

The hypotheses are exactly the paper's. Connectedness of `G`, `R ≥ 4`, `IsGadgetBall`
(no non-leaf vertex of the copy has a neighbour outside it), "every leaf of
`Q_{ℓ,R}` has phase `0`" and `|Δ_e(θ̂)| ≤ π/2 − δ` are derived, the last one from
Proposition 2.1 (iii) and `δ ≤ δ₀`. The gradient bound `‖∇𝓔(θ̂)‖ ≤ ε_ℓ(R)` is derived from the
embedding (`norm_grad_transplant_le`). -/
theorem glue (hreg : ∀ v, G.degree v = 3)
    {ℓ R : ℕ} [NeZero ℓ] (hℓ : ℓ % 4 = 0) {f : Gadget.Vtx ℓ R → V}
    (hQ : IsInducedCopy G ℓ R f)
    {δ : ℝ} (hδ : δ ∈ Set.Ioc 0 Gadget.δ₀) {μ : ℝ} (hμ : 0 < μ) (hR : R₀ μ δ ℓ ≤ R)
    (hspec : ∀ x : V → ℝ, OnePerp x → x ≠ 0 →
      μ * (∑ v, x v ^ 2) ≤ quadForm (hess G (transplant ℓ R f (Gadget.root R))) x) :
    ∃ θstar : Config V, OnePerp θstar ∧
      -- (i)
      Real.sqrt (∑ v, (θstar v - center (transplant ℓ R f (Gadget.root R)) v) ^ 2)
        ≤ 2 * gradNorm ℓ R / μ ∧
      -- (ii)
      (∀ u v, G.Adj u v → |phaseDiff θstar u v| < π / 2) ∧
      -- (iii)
      IsEquilibrium G θstar ∧
      ∃ j : ZMod ℓ, G.Adj (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j)) ∧
        phaseDiff (transplant ℓ R f (Gadget.root R)) (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j))
          = Gadget.root R ∧
        Gadget.root R - δ ≤ phaseDiff θstar (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j)) ∧
        0 < Gadget.root R - δ := by
  have hpi := Real.pi_pos
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hδ18 := Gadget.δ₀_lt
  have hℓ3 : 3 ≤ ℓ := by have := NeZero.ne ℓ; omega
  have hR4 : 4 ≤ R := four_le_of_R₀_le hR
  -- "since `G` is `3`-regular, all neighbors of a non-leaf vertex of `Q_{ℓ,R}` lie in `Q_{ℓ,R}`"
  have hball : IsGadgetBall G ℓ R f := isGadgetBall_of_induced G hreg hℓ3 hQ
  have : Nonempty V := ⟨f (Gadget.Vtx.cyc 0)⟩
  -- `λ₂(H(θ̂)) ≥ μ > 0` makes `G` connected
  have hG : G.Connected := connected_of_hess_gap G _ hμ hspec
  set θhat : Config V := transplant ℓ R f (Gadget.root R) with hθhat
  -- Proposition 2.1 (iii): `4π/9 < η*(R) ≤ π/2 − δ₀ ≤ π/2 − δ`
  obtain ⟨hηgt, hηle⟩ := Gadget.etabounds hR4
  -- "`|Δ_e(θ̂)| ≤ η*(R) ≤ π/2 − δ` for every `e ∈ E(G)`" (read modulo `2π`)
  have hcoh' : ∀ u v, G.Adj u v → ∃ k : ℤ, |θhat u - θhat v - 2 * π * k| ≤ π / 2 - δ :=
    fun u v huv => by
      obtain ⟨k, hk⟩ := transplant_near G hball hℓ hR4 u v huv
      exact ⟨k, by linarith⟩
  -- `‖∇𝓔(θ̂)‖₂ ≤ ε_ℓ(R)`, from the embedding
  have hgrad : Real.sqrt (∑ v, grad G θhat v ^ 2) ≤ gradNorm ℓ R :=
    norm_grad_transplant_le G hball hℓ hℓ3 hR4 (leaf_phase_root hR4)
  -- the Kantorovich step; `R ≥ R₀` gives `α₀ ≤ ½` through the second entry of `R₀`
  obtain ⟨θstar, hperp, hEq, hdist⟩ :=
    kantorovich_step G hreg hG θhat hμ hspec hgrad
      (kantorovich_condition hμ (by omega) hR)
  -- every phase difference moved by less than `δ`, through the third entry of `R₀`.
  -- Centering changes no phase difference, so it does not matter which `θ̂` we compare with.
  have hmove : ∀ u v, G.Adj u v → |(θstar u - θstar v) - (θhat u - θhat v)| < δ := by
    intro u v huv
    rw [← center_sub θhat u v]
    calc |(θstar u - θstar v) - (center θhat u - center θhat v)|
        ≤ Real.sqrt 2 * Real.sqrt (∑ z, (θstar z - center θhat z) ^ 2) :=
          edge_move_le (G.ne_of_adj huv)
      _ ≤ Real.sqrt 2 * (2 * gradNorm ℓ R / μ) :=
          mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg 2)
      _ < δ := sqrt_two_mul_gradNorm_lt hμ hδ0 (by omega) hR
  -- (ii) `Δ_e(θ*) = Δ_e(θ̂) + B_e(θ* − θ̂)`
  have hpc : ∀ u v, G.Adj u v → |phaseDiff θstar u v| < π / 2 :=
    (phaseCohesive_iff G θstar).mp (phaseCohesive_of_close G hcoh' hmove)
  -- (iii) "moreover `Δ₁₂(θ̂) = η*(R)`", hence `Δ₁₂(θ*) ≥ η*(R) − δ > 0`
  obtain ⟨j, hadjQ, hdiff⟩ := exists_cycle_edge (R := R) hℓ hℓ3 (Gadget.root R)
  have hadj : G.Adj (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j)) := (hball.adj_iff _ _).mpr hadjQ
  have hθhat12 : θhat (f (Gadget.Vtx.cyc 0)) - θhat (f (Gadget.Vtx.cyc j))
      = 2 * π - Gadget.root R := by
    rw [hθhat, transplant_apply hball.inj, transplant_apply hball.inj, hdiff]
  have hm := abs_lt.mp (hmove _ _ hadj)
  rw [hθhat12] at hm
  have hΔ12star : phaseDiff θstar (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j))
      = θstar (f (Gadget.Vtx.cyc j)) - θstar (f (Gadget.Vtx.cyc 0)) - 2 * π * (-1 : ℤ) :=
    phaseDiff_eq θstar _ _ (-1) (by push_cast; linarith) (by push_cast; linarith)
  refine ⟨θstar, hperp, hdist, hpc, hEq, j, hadj,
    phaseDiff_transplant_cycle_edge hball.inj hR4 hdiff, ?_, by linarith⟩
  rw [hΔ12star]; push_cast; linarith

/-- `cos x ≠ 1` for `0 < x < 2π`. Used with `x = Δ₁₂(θ*) ∈ (0, π]`: a positive phase difference
means the state is not synchronized. -/
theorem cos_ne_one_of_pos {x : ℝ} (h0 : 0 < x) (h2 : x < 2 * π) : Real.cos x ≠ 1 := by
  have hpi := Real.pi_pos
  intro hc
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff x).mp hc
  rw [← hn] at h0 h2
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have : (0 : ℤ) < n := by exact_mod_cast hn0
  have : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

/-- **Proposition 3.3, "Consequently".** Under the hypotheses of Proposition 3.3, `θ*` is a
stable non-synchronized equilibrium, and `G` is not globally synchronizing. -/
theorem glue_consequently (hreg : ∀ v, G.degree v = 3)
    {ℓ R : ℕ} [NeZero ℓ] (hℓ : ℓ % 4 = 0) {f : Gadget.Vtx ℓ R → V}
    (hQ : IsInducedCopy G ℓ R f)
    {δ : ℝ} (hδ : δ ∈ Set.Ioc 0 Gadget.δ₀) {μ : ℝ} (hμ : 0 < μ) (hR : R₀ μ δ ℓ ≤ R)
    (hspec : ∀ x : V → ℝ, OnePerp x → x ≠ 0 →
      μ * (∑ v, x v ^ 2) ≤ quadForm (hess G (transplant ℓ R f (Gadget.root R))) x) :
    (∃ θstar : Config V, StableEquilibrium G θstar ∧ ¬ Synchronized θstar) ∧
      ¬ GloballySynchronizing G := by
  have : Nonempty V := ⟨f (Gadget.Vtx.cyc 0)⟩
  have hG : G.Connected := connected_of_hess_gap G _ hμ hspec
  obtain ⟨θstar, -, -, hpcP, hEq, j, hadj, -, h12, hpos⟩ :=
    glue G hreg hℓ hQ hδ hμ hR hspec
  have hpc : PhaseCohesive G θstar := (phaseCohesive_iff G θstar).mpr hpcP
  have hpi := Real.pi_pos
  -- `0 < Δ₁₂(θ*) ≤ π`, so the endpoints of the edge `12` carry different phases
  have hne : Real.cos (θstar (f (Gadget.Vtx.cyc 0)) - θstar (f (Gadget.Vtx.cyc j))) ≠ 1 := by
    rw [cos_eq_cos_phaseDiff]
    exact cos_ne_one_of_pos (by linarith)
      (by linarith [Real.Angle.toReal_le_pi
            ((θstar (f (Gadget.Vtx.cyc j)) - θstar (f (Gadget.Vtx.cyc 0)) : ℝ) : Real.Angle),
        show phaseDiff θstar (f (Gadget.Vtx.cyc 0)) (f (Gadget.Vtx.cyc j))
          = ((θstar (f (Gadget.Vtx.cyc j)) - θstar (f (Gadget.Vtx.cyc 0)) : ℝ) : Real.Angle).toReal
          from rfl])
  exact ⟨⟨θstar, stableEquilibrium_of_phaseCohesive G hG hEq hpc, fun hs => hne (hs _ _)⟩,
    not_globallySynchronizing_of_certificate G hG hEq hpc hadj hne⟩

end Kuramoto
