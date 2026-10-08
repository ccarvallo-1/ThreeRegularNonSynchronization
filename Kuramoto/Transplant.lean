/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Gadget
public import Kuramoto.Kantorovich

/-!
# The transplanted configuration `θ̂`

Section 3 of the paper works with `θ̂`: the gadget configuration `θ^{η*}` of Proposition 2.1
carried into `G` along an induced copy of `Q_{ℓ,R}`, and extended by `0` outside.

* `IsInducedCopy`, `IsGadgetBall`, `isGadgetBall_of_induced`: the embedding.
* `transplant`: the configuration `θ̂`.
* `grad_transplant_eq_zero_of_induced`: Proposition 2.1 (i) inside `G`.
* `norm_grad_transplant_le`: `‖∇𝓔(θ̂)‖₂ = ε_ℓ(R) = √ℓ sin η*(R) 2^{-(R-1)/2}`.
* `R₀`: the threshold of Proposition 3.3, and the two inequalities its entries guarantee
  (`sqrt_two_mul_gradNorm_lt`; `kantorovich_condition` is in `Correction.lean`).
-/

@[expose] public section

namespace Kuramoto

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## The transplant

Section 3 of the paper works with `θ̂`: the gadget configuration `θ^{η*}` carried into `G`
along an embedding of `Q_{ℓ,R}` as a radius-`R` ball, extended by `0` outside. The gradient
bound that feeds Kantorovich is a property of *that* configuration, so the embedding has to be
part of the hypotheses. -/

open scoped Classical in
/-- `f` embeds `Q_{ℓ,R}` into `G` as the radius-`R` ball around its cycle: the embedding is
induced (`adj_iff`), and no non-leaf vertex of the gadget has a neighbour outside it
(`interior`). Leaves may, and do, have neighbours outside — that is where the gradient fails
to vanish. In a `3`-regular graph `interior` is automatic (`isGadgetBall_of_induced`), so this
is the paper's "`G` contains `Q_{ℓ,R}` as an induced subgraph". -/
structure IsGadgetBall (G : SimpleGraph V) (ℓ R : ℕ) (f : Gadget.Vtx ℓ R → V) : Prop where
  inj : Function.Injective f
  adj_iff : ∀ w w', G.Adj (f w) (f w') ↔ (Gadget.Q ℓ R).Adj w w'
  interior : ∀ w, ¬ Gadget.Vtx.IsLeaf ℓ R w → ∀ y, G.Adj (f w) y → y ∈ Set.range f

/-- `f` embeds `Q_{ℓ,R}` into `G` as an induced subgraph: the paper's hypothesis in
Proposition 3.3 and the event `A_n¹`. -/
structure IsInducedCopy (G : SimpleGraph V) (ℓ R : ℕ) (f : Gadget.Vtx ℓ R → V) : Prop where
  inj : Function.Injective f
  adj_iff : ∀ w w', G.Adj (f w) (f w') ↔ (Gadget.Q ℓ R).Adj w w'

omit [DecidableEq V] in
/-- "A non-leaf vertex `v` of `Q_{ℓ,R}` has degree `3` in `Q_{ℓ,R}`, and since `G` is
`3`-regular, all of its neighbors in `G` lie in `Q_{ℓ,R}`." So in a `3`-regular graph an induced
copy of `Q_{ℓ,R}` is a gadget ball. -/
theorem isGadgetBall_of_induced (hreg : ∀ v, G.degree v = 3) {ℓ R : ℕ} [NeZero ℓ] (hℓ : 3 ≤ ℓ)
    {f : Gadget.Vtx ℓ R → V} (hf : IsInducedCopy G ℓ R f) : IsGadgetBall G ℓ R f := by
  refine ⟨hf.inj, hf.adj_iff, fun w hw y hy => ?_⟩
  set S := ((Gadget.Q ℓ R).neighborFinset w).map ⟨f, hf.inj⟩ with hS
  have hsub : S ⊆ G.neighborFinset (f w) := by
    intro z hz
    obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hz
    exact (G.mem_neighborFinset _ _).mpr
      ((hf.adj_iff w w').mpr (((Gadget.Q ℓ R).mem_neighborFinset _ _).mp hw'))
  have hcard : (G.neighborFinset (f w)).card ≤ S.card := by
    rw [hS, Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree, hreg, Gadget.degree_eq_three ℓ R hℓ w hw]
  have hy' : y ∈ S :=
    (Finset.eq_of_subset_of_card_le hsub hcard) ▸ (G.mem_neighborFinset _ _).mpr hy
  obtain ⟨w', _, rfl⟩ := Finset.mem_map.mp hy'
  exact ⟨w', rfl⟩

open scoped Classical in
/-- The transplant `θ̂` of §3: `θ^η` inside the ball, `0` outside. -/
noncomputable def transplant (ℓ R : ℕ) (f : Gadget.Vtx ℓ R → V) (η : ℝ) : Config V :=
  fun v => if h : ∃ w, f w = v then Gadget.phase ℓ R η h.choose else 0

omit [Fintype V] [DecidableEq V] in
theorem transplant_apply {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} (hf : Function.Injective f)
    (η : ℝ) (w : Gadget.Vtx ℓ R) : transplant ℓ R f η (f w) = Gadget.phase ℓ R η w := by
  classical
  have hex : ∃ w', f w' = f w := ⟨w, rfl⟩
  rw [transplant, dite_eq_left hex]
  congr 1
  exact hf hex.choose_spec

omit [Fintype V] [DecidableEq V] in
theorem transplant_off {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} (η : ℝ) {v : V}
    (hv : v ∉ Set.range f) : transplant ℓ R f η v = 0 := by
  classical
  rw [transplant, dite_eq_right]
  rintro ⟨w, rfl⟩
  exact hv ⟨w, rfl⟩

/-- Around a non-leaf gadget vertex, the `G`-neighbourhood is exactly the image of the
gadget neighbourhood. -/
theorem IsGadgetBall.neighborFinset_eq {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} [NeZero ℓ]
    (hball : IsGadgetBall G ℓ R f) (w : Gadget.Vtx ℓ R) (hw : ¬ Gadget.Vtx.IsLeaf ℓ R w) :
    G.neighborFinset (f w) = ((Gadget.Q ℓ R).neighborFinset w).image f := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · intro hy
    obtain ⟨w', rfl⟩ := hball.interior w hw y hy
    exact ⟨w', (hball.adj_iff w w').mp hy, rfl⟩
  · rintro ⟨w', hw', rfl⟩
    exact (hball.adj_iff w w').mpr hw'

/-- At a non-leaf vertex of the ball the transplant inherits the gadget's gradient, hence
vanishes by Proposition 2.1 (i). -/
theorem grad_transplant_interior {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} [NeZero ℓ]
    (hball : IsGadgetBall G ℓ R f) (η : ℝ) (w : Gadget.Vtx ℓ R)
    (hw : ¬ Gadget.Vtx.IsLeaf ℓ R w) :
    grad G (transplant ℓ R f η) (f w)
      = grad (Gadget.Q ℓ R) (Gadget.phase ℓ R η) w := by
  rw [grad, grad, IsGadgetBall.neighborFinset_eq G hball w hw,
    Finset.sum_image (fun a _ b _ h => hball.inj h)]
  exact Finset.sum_congr rfl fun w' _ => by
    rw [transplant_apply hball.inj, transplant_apply hball.inj]

/-- **Proposition 2.1 (i), in `G`.** "Assume `G` contains `Q_{ℓ,R}` as an induced subgraph. Then
`∂𝓔/∂θ_v(θ^η) = 0` at every non-leaf vertex of `Q_{ℓ,R}`", with `θ^η` carried into `G` (and
extended by `0`). This needs `G` to be `3`-regular: otherwise a non-leaf vertex of the copy may
have further neighbours in `G`. -/
theorem grad_transplant_eq_zero_of_induced (hreg : ∀ v, G.degree v = 3) {ℓ R : ℕ}
    {f : Gadget.Vtx ℓ R → V} [NeZero ℓ] (hℓ : ℓ % 4 = 0) (hQ : IsInducedCopy G ℓ R f)
    {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) (w : Gadget.Vtx ℓ R)
    (hw : ¬ Gadget.Vtx.IsLeaf ℓ R w) :
    grad G (transplant ℓ R f η) (f w) = 0 := by
  have hℓ3 : 3 ≤ ℓ := by have := NeZero.ne ℓ; omega
  rw [grad_transplant_interior G (isGadgetBall_of_induced G hreg hℓ3 hQ) η w hw]
  exact Gadget.grad_eq_zero_of_nonleaf ℓ R hℓ hℓ3 h₀ h₁ w hw

/-- Outside the ball every neighbour carries phase `0`, so the gradient vanishes there too.
The only gadget vertices that can be adjacent to the outside are the leaves, and those carry
phase `0` by the definition of `η*`. -/
theorem grad_transplant_outside {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} [NeZero ℓ]
    (hball : IsGadgetBall G ℓ R f) {η : ℝ}
    (hleaf : ∀ w : Gadget.Vtx ℓ R, Gadget.Vtx.IsLeaf ℓ R w → Gadget.phase ℓ R η w = 0)
    {v : V} (hv : v ∉ Set.range f) :
    grad G (transplant ℓ R f η) v = 0 := by
  have hzero : ∀ y : V, G.Adj v y → transplant ℓ R f η y = 0 := by
    intro y hy
    by_cases hyr : y ∈ Set.range f
    · obtain ⟨w, rfl⟩ := hyr
      by_cases hwl : Gadget.Vtx.IsLeaf ℓ R w
      · rw [transplant_apply hball.inj]; exact hleaf w hwl
      · exact absurd (hball.interior w hwl v hy.symm) hv
    · exact transplant_off η hyr
  rw [grad, transplant_off η hv]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [hzero y ((G.mem_neighborFinset v y).mp hy), sub_zero, Real.sin_zero]

/-- **The support of the gradient.** `∇𝓔(θ̂)` vanishes at every vertex except the images of
the gadget's leaves: at interior gadget vertices by Proposition 2.1 (i), and outside the ball
because every phase there is `0`. -/
theorem grad_transplant_eq_zero_of_not_leaf {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} [NeZero ℓ]
    (hball : IsGadgetBall G ℓ R f) (hℓ4 : ℓ % 4 = 0) (hℓ3 : 3 ≤ ℓ)
    {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2)
    (hleaf : ∀ w : Gadget.Vtx ℓ R, Gadget.Vtx.IsLeaf ℓ R w → Gadget.phase ℓ R η w = 0)
    {v : V} (hv : ∀ w : Gadget.Vtx ℓ R, Gadget.Vtx.IsLeaf ℓ R w → v ≠ f w) :
    grad G (transplant ℓ R f η) v = 0 := by
  by_cases hvr : v ∈ Set.range f
  · obtain ⟨w, rfl⟩ := hvr
    have hw : ¬ Gadget.Vtx.IsLeaf ℓ R w := fun hc => hv w hc rfl
    rw [grad_transplant_interior G hball η w hw]
    exact Gadget.grad_eq_zero_of_nonleaf ℓ R hℓ4 hℓ3 h₀ h₁ w hw
  · exact grad_transplant_outside G hball hleaf hvr

/-- The gradient of the transplanted configuration is supported on the sphere of radius `R`,
where each of the `ℓ 2^{R-1}` vertices carries the leftover current `2^{-(R-1)} sin η*`. Hence
`‖∇𝓔(θhat)‖ = √ℓ sin η*(R) 2^{-(R-1)/2}`, the quantity `ε_ℓ(R)` of Proposition 3.3. -/
noncomputable def gradNorm (ℓ R : ℕ) : ℝ :=
  Real.sqrt ℓ * Real.sin (Gadget.root R) * (1 / 2 : ℝ) ^ ((R - 1 : ℕ) / 2 : ℝ)

/-- The threshold of Proposition 3.3,
`R₀(μ, δ, ℓ) = max {4, ⌈1 + 2 log₂(12√(2ℓ)/μ²)⌉, ⌈2 + 2 log₂(2√(2ℓ)/(μδ))⌉}`.
(`⌈·⌉₊` is the ceiling truncated at `0`; inside a `max` with `4` this is the paper's `⌈·⌉`.) -/
noncomputable def R₀ (μ δ : ℝ) (ℓ : ℕ) : ℕ :=
  max 4 (max ⌈1 + 2 * Real.logb 2 (12 * Real.sqrt (2 * (ℓ : ℝ)) / μ ^ 2)⌉₊
             ⌈2 + 2 * Real.logb 2 (2 * Real.sqrt (2 * (ℓ : ℝ)) / (μ * δ))⌉₊)

theorem four_le_of_R₀_le {μ δ : ℝ} {ℓ R : ℕ} (hR : R₀ μ δ ℓ ≤ R) : 4 ≤ R :=
  le_trans (le_max_left _ _) hR

/-- A phase difference moves by at most `√2` times the `ℓ²` displacement. This is the
`|B_e(θ* - θhat)| ≤ √2 ‖θ* - θhat‖` step of the paper. -/
theorem edge_move_le {θ' θhat : Config V} {u v : V} (huv : u ≠ v) :
    |(θ' u - θ' v) - (θhat u - θhat v)|
      ≤ Real.sqrt 2 * Real.sqrt (∑ z, (θ' z - θhat z) ^ 2) := by
  have h : (θ' u - θ' v) - (θhat u - θhat v)
      = (fun z => θ' z - θhat z) u - (fun z => θ' z - θhat z) v := by simp; ring
  rw [h]
  exact abs_sub_le_sqrt_two_mul (w := fun z => θ' z - θhat z) huv

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- If every phase difference of `θhat` is within `π/2 - δ` of `2πℤ`, and every phase
difference moves by less than `δ`, the result is phase-cohesive. This is the last step of
Proposition 3.3: `Δ_e(θ*) = Δ_e(θhat) + B_e(θ* − θhat)`.

The distance is to `2πℤ`, not to `0`, because the paper's `Δ_e` is the representative of the
difference *modulo `2π`* in `(-π, π]`. On a cycle edge of the gadget with opposite signs the
real difference is `±2t = ±(2π − η*)`, whose representative is `∓η*`. -/
theorem phaseCohesive_of_close {θ' θhat : Config V} {δ : ℝ}
    (hcoh : ∀ u v, G.Adj u v → ∃ k : ℤ, |θhat u - θhat v - 2 * π * k| ≤ π / 2 - δ)
    (hmove : ∀ u v, G.Adj u v → |(θ' u - θ' v) - (θhat u - θhat v)| < δ) :
    PhaseCohesive G θ' := by
  intro u v huv
  obtain ⟨k, hk⟩ := hcoh u v huv
  have h2 := hmove u v huv
  have hlt : |θ' u - θ' v - 2 * π * k| < π / 2 := by
    calc |θ' u - θ' v - 2 * π * k|
        = |(θhat u - θhat v - 2 * π * k) + ((θ' u - θ' v) - (θhat u - θhat v))| := by ring_nf
      _ ≤ |θhat u - θhat v - 2 * π * k| + |(θ' u - θ' v) - (θhat u - θhat v)| := abs_add_le _ _
      _ < (π / 2 - δ) + δ := by linarith
      _ = π / 2 := by ring
  have hcos : Real.cos (θ' u - θ' v) = Real.cos (θ' u - θ' v - 2 * π * k) := by
    rw [show θ' u - θ' v - 2 * π * k = θ' u - θ' v - (k : ℝ) * (2 * π) by ring,
      Real.cos_sub_int_mul_two_pi]
  rw [hcos]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_lt.mp hlt], (abs_lt.mp hlt).2⟩

/-- The third entry of `R₀` is exactly what makes the Newton correction move every phase
difference by less than the margin `δ`. -/
theorem sqrt_two_mul_gradNorm_lt {ℓ R : ℕ} {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (hℓ : 0 < ℓ) (hR : R₀ μ δ ℓ ≤ R) :
    Real.sqrt 2 * (2 * gradNorm ℓ R / μ) < δ := by
  have hR1 : 1 ≤ R := by have := four_le_of_R₀_le hR; omega
  have hsl : (0 : ℝ) < Real.sqrt (2 * ℓ) := Real.sqrt_pos.mpr (by positivity)
  set c : ℝ := 2 * Real.sqrt (2 * ℓ) / (μ * δ) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set t : ℝ := ((R - 1 : ℕ) : ℝ) / 2 with ht
  have hRcast : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by push_cast [Nat.cast_sub hR1]; ring
  have hR3 : (R : ℝ) ≥ 2 + 2 * Real.logb 2 c :=
    le_trans (Nat.le_ceil _)
      (Nat.cast_le.mpr (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR))
  have htlog : Real.logb 2 c < t := by rw [ht, hRcast]; linarith
  have hpow0 : (0 : ℝ) < (1 / 2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  -- `(1/2)^t < 1/c`, which is the content of `R ≥ 2 + 2 log₂ c`
  have hpow : (1 / 2 : ℝ) ^ t < 1 / c := by
    have e1 : (1 / 2 : ℝ) ^ t = (2 : ℝ) ^ (-t) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), one_div,
        ← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
    have e2 : (1 : ℝ) / c = (2 : ℝ) ^ (-Real.logb 2 c) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) hc0, one_div]
    rw [e1, e2]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  -- `sin η* ≤ 1` bounds `gradNorm`
  have hgn : gradNorm ℓ R ≤ Real.sqrt ℓ * (1 / 2 : ℝ) ^ t := by
    rw [gradNorm, ← ht]
    calc Real.sqrt ℓ * Real.sin (Gadget.root R) * (1 / 2 : ℝ) ^ t
        = (Real.sqrt ℓ * (1 / 2 : ℝ) ^ t) * Real.sin (Gadget.root R) := by ring
      _ ≤ (Real.sqrt ℓ * (1 / 2 : ℝ) ^ t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
      _ = Real.sqrt ℓ * (1 / 2 : ℝ) ^ t := by ring
  have hsplit : Real.sqrt 2 * Real.sqrt (ℓ : ℝ) = Real.sqrt (2 * ℓ) :=
    (Real.sqrt_mul (by norm_num) _).symm
  have hfinal : Real.sqrt (2 * ℓ) * (1 / 2 : ℝ) ^ t < μ * δ / 2 := by
    have h1 : Real.sqrt (2 * ℓ) * (1 / 2 : ℝ) ^ t < Real.sqrt (2 * ℓ) * (1 / c) :=
      mul_lt_mul_of_pos_left hpow hsl
    have h2 : Real.sqrt (2 * ℓ) * (1 / c) = μ * δ / 2 := by
      rw [hc]; field_simp
    linarith
  have key : Real.sqrt 2 * (2 * gradNorm ℓ R) < μ * δ := by
    have e : Real.sqrt 2 * (2 * (Real.sqrt ℓ * (1 / 2 : ℝ) ^ t))
        = 2 * (Real.sqrt (2 * ℓ) * (1 / 2 : ℝ) ^ t) := by rw [← hsplit]; ring
    nlinarith [Real.sqrt_nonneg 2, hgn, hfinal]
  calc Real.sqrt 2 * (2 * gradNorm ℓ R / μ) = Real.sqrt 2 * (2 * gradNorm ℓ R) / μ := by ring
    _ < δ := by rw [div_lt_iff₀ hμ]; linarith

/-- **The residual gradient at a leaf.** A leaf carries phase `0`; its two edges to the
exterior carry `0` as well, so the whole gradient there is the current `sin Δ_k` coming down
its own branch. -/
theorem grad_transplant_leaf {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} [NeZero ℓ]
    (hball : IsGadgetBall G ℓ R f) {η : ℝ} (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 = R)
    (hz : Gadget.phase ℓ R η (Gadget.Vtx.brn i k b) = 0) :
    grad G (transplant ℓ R f η) (f (Gadget.Vtx.brn i k b))
      = -(Gadget.sgn i.val * Real.sin (Gadget.Δ η (k : ℕ))) := by
  set w : Gadget.Vtx ℓ R := Gadget.Vtx.brn i k b with hwdef
  set p : Gadget.Vtx ℓ R := Gadget.parent ℓ R i k b with hpdef
  have hmem : f p ∈ G.neighborFinset (f w) :=
    (G.mem_neighborFinset _ _).mpr ((hball.adj_iff w p).mpr (Gadget.adj_brn_parent ℓ R i k b hk))
  have hzero : ∀ y ∈ G.neighborFinset (f w), y ≠ f p →
      Real.sin (transplant ℓ R f η (f w) - transplant ℓ R f η y) = 0 := by
    intro y hy hne
    have hy' : G.Adj (f w) y := (G.mem_neighborFinset _ _).mp hy
    have hy0 : transplant ℓ R f η y = 0 := by
      by_cases hyr : y ∈ Set.range f
      · obtain ⟨w', rfl⟩ := hyr
        -- the only gadget neighbour of a leaf is its parent
        have hadj : (Gadget.Q ℓ R).Adj w w' := (hball.adj_iff w w').mp hy'
        have : w' ∈ ({p} : Finset (Gadget.Vtx ℓ R)) := by
          rw [← Gadget.neighborFinset_brn_leaf ℓ R i k b hk]
          exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj
        exact absurd (by rw [Finset.mem_singleton] at this; rw [this]) hne
      · exact transplant_off η hyr
    rw [hy0, transplant_apply hball.inj, hz, sub_zero, Real.sin_zero]
  rw [grad, Finset.sum_eq_single_of_mem (f p) hmem hzero,
    transplant_apply hball.inj, transplant_apply hball.inj, hz, zero_sub,
    Gadget.phase_parent_of_leaf_zero ℓ R i k b hz, Real.sin_neg, Gadget.sgn_mul_sin]

/-- **The gradient bound of §3.** `‖∇𝓔(θ̂)‖₂ = √ℓ · sin η*(R) · 2^{-(R-1)/2} = ε_ℓ(R)`.

The sum collapses to the `ℓ · 2^{R-1}` leaves (`grad_transplant_eq_zero_of_not_leaf`), each
carrying the current `sin Δ_{R-1} = 2^{-(R-1)} sin η*` up its own branch. -/
theorem norm_grad_transplant_le {ℓ R : ℕ} {f : Gadget.Vtx ℓ R → V} [NeZero ℓ]
    (hball : IsGadgetBall G ℓ R f) (hℓ4 : ℓ % 4 = 0) (hℓ3 : 3 ≤ ℓ) (hR : 4 ≤ R)
    (hleaf : ∀ w : Gadget.Vtx ℓ R, Gadget.Vtx.IsLeaf ℓ R w →
      Gadget.phase ℓ R (Gadget.root R) w = 0) :
    Real.sqrt (∑ v, grad G (transplant ℓ R f (Gadget.root R)) v ^ 2) ≤ gradNorm ℓ R := by
  classical
  set η : ℝ := Gadget.root R with hη
  set θhat : Config V := transplant ℓ R f η with hθhat
  obtain ⟨hmem, hzero⟩ := Gadget.root_spec hR
  have hR0 : 0 < R := by omega
  have hη0 : 0 < η := hmem.1
  have hη1 : η < π / 2 := hmem.2
  -- the support: the images of the leaves
  set S : Finset V :=
    Finset.univ.image (fun p : ZMod ℓ × Fin (2 ^ (R - 1)) => f (Gadget.leafVtx ℓ R hR0 p.1 p.2))
    with hS
  have hsupp : ∀ v ∈ (Finset.univ : Finset V), v ∉ S → grad G θhat v ^ 2 = 0 := by
    intro v _ hvS
    have hv : ∀ w : Gadget.Vtx ℓ R, Gadget.Vtx.IsLeaf ℓ R w → v ≠ f w := by
      intro w hw hvw
      obtain ⟨i, b, rfl⟩ := Gadget.exists_leafVtx ℓ R hR0 w hw
      exact hvS (by rw [hS, Finset.mem_image]; exact ⟨(i, b), Finset.mem_univ _, hvw.symm⟩)
    rw [grad_transplant_eq_zero_of_not_leaf G hball hℓ4 hℓ3 hη0 hη1 hleaf hv]
    ring
  -- each leaf contributes `sin² Δ_{R-1}`
  have hleafval : ∀ p : ZMod ℓ × Fin (2 ^ (R - 1)),
      grad G θhat (f (Gadget.leafVtx ℓ R hR0 p.1 p.2)) ^ 2
        = Real.sin (Gadget.Δ η (R - 1)) ^ 2 := by
    rintro ⟨i, b⟩
    rw [Gadget.leafVtx, grad_transplant_leaf G hball i _ b (by show R - 1 + 1 = R; omega)
      (hleaf _ (Gadget.isLeaf_leafVtx ℓ R hR0 i b))]
    rcases Gadget.sgn_eq_one_or i.val with h | h <;> rw [h] <;> ring
  have hsum : ∑ v, grad G θhat v ^ 2
      = (ℓ : ℝ) * 2 ^ (R - 1) * Real.sin (Gadget.Δ η (R - 1)) ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ S) hsupp, hS,
      Finset.sum_image (fun a _ b _ h => Gadget.leafVtx_injective ℓ R hR0 (hball.inj h))]
    rw [Finset.sum_congr rfl fun p _ => hleafval p, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- `sin Δ_{R-1} = 2^{-(R-1)} sin η`, so the norm is `√ℓ · 2^{-(R-1)/2} · sin η`
  have hsinΔ : Real.sin (Gadget.Δ η (R - 1)) = (1 / 2 : ℝ) ^ (R - 1) * Real.sin η :=
    Gadget.sin_Δ η (R - 1)
  have hsinpos : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos])
  rw [hsum, hsinΔ]
  -- now a direct computation with `√`
  have hPQ : ((1 : ℝ) / 2) ^ (R - 1) * (2 : ℝ) ^ (R - 1) = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀]
    positivity
  have e1 : Real.sqrt (ℓ : ℝ) ^ 2 = (ℓ : ℝ) := Real.sq_sqrt (by positivity)
  have e2 : ((1 / 2 : ℝ) ^ (((R - 1 : ℕ) : ℝ) / 2)) ^ 2 = (1 / 2 : ℝ) ^ (R - 1) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (((R - 1 : ℕ) : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hval : (ℓ : ℝ) * 2 ^ (R - 1) * ((1 / 2 : ℝ) ^ (R - 1) * Real.sin η) ^ 2
      = (Real.sqrt ℓ * Real.sin η * (1 / 2 : ℝ) ^ (((R - 1 : ℕ) : ℝ) / 2)) ^ 2 := by
    simp only [mul_pow]
    rw [e1, e2]
    linear_combination ((ℓ : ℝ) * Real.sin η ^ 2 * (1 / 2 : ℝ) ^ (R - 1)) * hPQ
  rw [hval, Real.sqrt_sq (by positivity), gradNorm, ← hη]

end Kuramoto
