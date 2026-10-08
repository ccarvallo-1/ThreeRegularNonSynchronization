/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Certificate
public import Kuramoto.GadgetCount
public import Kuramoto.Correction

/-!
# Theorem 1.2

Paper cross-reference: Theorem 1.2 -> `Kuramoto.main_theorem`
(`lim_n P(G_{2n,3} is not globally synchronizing) = 1`).

The proof follows the paper's. Fix `δ ∈ (0, δ₀]` (we take `δ = δ₀`) and
`μ = ½ sin δ (3 − 2√2)`. On the events

  `A_n¹ = {G_{n,3} contains Q_{ℓ, R₀(μ,δ,ℓ)} as an induced subgraph for some ℓ = 4k}`,
  `A_n² = {λ₂(A) ≤ 2√2 + ½(3 − 2√2)}` (so `λ₂(L) ≥ ½(3 − 2√2)`)

the transplant satisfies the hypotheses of Proposition 3.3 with `R = R₀(μ, δ, ℓ)`, which
produces a stable non-synchronized equilibrium. Then
`P(globally synchronizing) ≤ P((A_n¹)ᶜ) + P((A_n²)ᶜ) → 0`, by Lemma 2.2 (`Random.gadgetcount`)
and Friedman (`Random.friedman`).

The deterministic half is `not_globallySynchronizing_of_gadgetBall`; the probabilistic half is
`prob_globallySynchronizing_le`, and `main_theorem` turns it into the limit.
-/

@[expose] public section

namespace Kuramoto

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## The transplant satisfies the hypotheses of Proposition 3.3 -/

/-- Within `π/2 − δ` of `2πℤ` means `cos ≥ cos (π/2 − δ) = sin δ`. -/
theorem sin_le_cos_of_near {a δ : ℝ} {k : ℤ} (hδ₀ : 0 ≤ δ) (hδ : δ < π / 2)
    (h : |a - 2 * π * k| ≤ π / 2 - δ) : Real.sin δ ≤ Real.cos a := by
  have hpi := Real.pi_pos
  have hc : Real.cos a = Real.cos (a - 2 * π * k) := by
    rw [show a - 2 * π * k = a - (k : ℝ) * (2 * π) by ring, Real.cos_sub_int_mul_two_pi]
  rw [hc, ← Real.cos_abs, ← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h

/-- "`cos Δ_e(θ̂) ≥ sin δ` for every `e ∈ E(G)`, and consequently `H(θ̂) − sin δ · L ⪰ 0`.
Since both vanish on `1`, `λ₂(H(θ̂)) ≥ sin δ · λ₂(L)`." -/
theorem hess_spectral_bound (θ : Config V) {δ gap : ℝ} (hδ : 0 ≤ Real.sin δ)
    (hcos : ∀ u v, G.Adj u v → Real.sin δ ≤ Real.cos (θ u - θ v))
    (hgap : Random.SpectralGap G gap) :
    ∀ x : V → ℝ, OnePerp x → x ≠ 0 →
      (Real.sin δ * gap) * (∑ v, x v ^ 2) ≤ quadForm (hess G θ) x := by
  intro x hx _
  have h1 : Real.sin δ * quadForm (hess G (fun _ => 0)) x ≤ quadForm (hess G θ) x := by
    rw [quadForm_hess, quadForm_hess]
    simp only [sub_self, Real.cos_zero, one_mul]
    rw [← mul_assoc, mul_comm (Real.sin δ) (1 / 2), mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (by norm_num)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    exact mul_le_mul_of_nonneg_right (hcos u v ((G.mem_neighborFinset u v).mp hv)) (sq_nonneg _)
  calc (Real.sin δ * gap) * (∑ v, x v ^ 2) = Real.sin δ * (gap * ∑ v, x v ^ 2) := by ring
    _ ≤ Real.sin δ * quadForm (hess G (fun _ => 0)) x := mul_le_mul_of_nonneg_left (hgap x hx) hδ
    _ ≤ quadForm (hess G θ) x := h1

/-! ## The deterministic half of Theorem 1.2 -/

/-- **On `A_n¹ ∩ A_n²`, the graph is not globally synchronizing.** If `G` is `3`-regular, has
spectral gap `λ₂(L) ≥ gap > 0`, and contains `Q_{ℓ,R}` as an induced subgraph with
`R ≥ R₀(μ, δ, ℓ)`, `μ = sin δ · gap`, `δ ∈ (0, δ₀]`, then `G` is not globally synchronizing.

This is the paper's argument on the event `A_n¹ ∩ A_n²`: "Since `R ≥ 4`, Proposition 2.1 gives
`|Δ_e(θ̂)| ≤ η* ≤ π/2 − δ`" on every edge, hence `cos Δ_e(θ̂) ≥ sin δ`, hence
`λ₂(H(θ̂)) ≥ sin δ · λ₂(L) ≥ μ`; "thus all the hypotheses of Proposition 3.3 are satisfied". -/
theorem not_globallySynchronizing_of_gadgetBall (hreg : ∀ v, G.degree v = 3)
    {gap : ℝ} (hgap0 : 0 < gap) (hgap : Random.SpectralGap G gap)
    {ℓ R : ℕ} [NeZero ℓ] (hℓ : ℓ % 4 = 0)
    {δ : ℝ} (hδ : δ ∈ Set.Ioc 0 Gadget.δ₀) (hR : R₀ (Real.sin δ * gap) δ ℓ ≤ R)
    {f : Gadget.Vtx ℓ R → V} (hQ : IsInducedCopy G ℓ R f) :
    ¬ GloballySynchronizing G := by
  have hpi := Real.pi_pos
  have hδ18 := Gadget.δ₀_lt
  have hδpi : δ < π / 2 := by linarith [hδ.2]
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ.1 (by linarith)
  have hR4 : 4 ≤ R := four_le_of_R₀_le hR
  have hball : IsGadgetBall G ℓ R f :=
    isGadgetBall_of_induced G hreg (by have := NeZero.ne ℓ; omega) hQ
  -- "Since `R ≥ 4`, Proposition 2.1 gives `|Δ_e(θ̂)| ≤ η* ≤ π/2 − δ` for every edge"
  have hηle : Gadget.root R ≤ π / 2 - δ := by linarith [(Gadget.etabounds hR4).2, hδ.2]
  have hcoh : ∀ u v, G.Adj u v → ∃ k : ℤ,
      |transplant ℓ R f (Gadget.root R) u - transplant ℓ R f (Gadget.root R) v - 2 * π * k|
        ≤ π / 2 - δ := fun u v huv => by
    obtain ⟨k, hk⟩ := transplant_near G hball hℓ hR4 u v huv
    exact ⟨k, hk.trans hηle⟩
  -- "therefore `cos Δ_e(θ̂) ≥ sin δ`, and `λ₂(H(θ̂)) ≥ sin δ · λ₂(L) ≥ μ`"
  have hspec := hess_spectral_bound G (transplant ℓ R f (Gadget.root R)) hsinδ.le
    (fun u v huv => by
      obtain ⟨k, hk⟩ := hcoh u v huv
      exact sin_le_cos_of_near hδ.1.le hδpi hk) hgap
  -- "Thus all the hypotheses of Proposition 3.3 are satisfied"
  exact (glue_consequently G hreg hℓ hQ hδ (mul_pos hsinδ hgap0) hR hspec).2

/-! ## The probabilistic half: Theorem 1.2 -/

open scoped Classical in
/-- **The proof of Theorem 1.2**, for one target probability: for every `κ > 0`, for all large
even `n`, `P(G_{n,3} is globally synchronizing) ≤ κ`.

"Fix `δ ∈ (0, δ₀]` and set `μ := ½ sin δ (3 − 2√2)`" (we take `δ = δ₀`). The events are

  `A_n¹ = {G_{n,3} contains Q_{ℓ, R₀(μ,δ,ℓ)} as an induced subgraph for some ℓ = 4k}`,
  `A_n² = {λ₂(A) ≤ 2√2 + ½(3 − 2√2)}`, i.e. `λ₂(L) ≥ ½(3 − 2√2)`.

On `A_n¹ ∩ A_n²` the graph does not synchronize (`not_globallySynchronizing_of_gadgetBall`,
with `R := R₀(μ, δ, ℓ)` for the `ℓ` of `A_n¹`), so
`P(globally synchronizing) ≤ P((A_n¹)ᶜ) + P((A_n²)ᶜ)`, and both terms tend to `0`, by
Lemma 2.2 (`Random.gadgetcount` with `R(ℓ) = R₀(μ, δ, ℓ)`) and Friedman's theorem
(`Random.friedman`). -/
theorem prob_globallySynchronizing_le (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ n in Filter.atTop, Even n →
      Random.prob n {G | GloballySynchronizing G} ≤ ENNReal.ofReal κ := by
  -- "Fix `δ ∈ (0, δ₀]` and set `μ := ½ sin δ (3 − 2√2)`"
  set δ : ℝ := Gadget.δ₀ with hδ
  have hδmem : δ ∈ Set.Ioc 0 Gadget.δ₀ := ⟨Gadget.δ₀_pos, le_rfl⟩
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- Friedman with `ε = ½(3 − 2√2)`: `λ₂(A) ≤ 2√2 + ε`, hence `λ₂(L) ≥ gap := ½(3 − 2√2)`, and
  -- `μ = sin δ · gap`
  set ε : ℝ := (3 - 2 * Real.sqrt 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set gap : ℝ := 3 - 2 * Real.sqrt 2 - ε with hgap
  have hgap0 : 0 < gap := by rw [hgap, hε]; linarith
  -- the radius, as a function of the cycle length: `R(ℓ) = R₀(μ, δ, ℓ)`
  set Rℓ : ℕ → ℕ := fun ℓ => R₀ (Real.sin δ * gap) δ ℓ with hRℓ
  have hRpos : ∀ ℓ, 0 < Rℓ ℓ := fun ℓ => by
    have := four_le_of_R₀_le (le_refl (R₀ (Real.sin δ * gap) δ ℓ)); simp only [hRℓ]; omega
  -- "By Lemma 2.2, `P((A_n¹)ᶜ) → 0`. By Friedman's theorem, `P((A_n²)ᶜ) → 0`."
  have h1 := Random.gadgetcount Rℓ hRpos (κ / 2) (by positivity)
  have hF := Random.friedman ε hε0 (κ / 2) (by positivity)
  filter_upwards [h1, hF, Filter.eventually_ge_atTop 2] with n hn1 hnF hn2 heven
  have hA1 := hn1 heven
  have hA2 := hnF heven
  set A₁ := {G : SimpleGraph (Fin n) | ∃ k : ℕ, Random.HasGadgetBall G (4 * (k + 1)) (Rℓ (4 * (k + 1)))}
  set A₂ := {G : SimpleGraph (Fin n) | Random.lambda2 G ≤ 2 * Real.sqrt 2 + ε}
  -- "From now on we work on `A_n¹ ∩ A_n²`": there the graph does not synchronize
  have hsub : {G : SimpleGraph (Fin n) | GloballySynchronizing G} ⊆ A₁ᶜ ∪ A₂ᶜ := by
    intro G hGS
    by_contra hcon
    simp only [A₁, A₂, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not]
      at hcon
    obtain ⟨⟨k, hreg, f, hQ⟩, hlam⟩ := hcon
    -- "Since `L = 3I − A`, `λ₂(L) = 3 − λ₂(A) ≥ ½(3 − 2√2)`"
    have hgapG : Random.SpectralGap G gap := by
      have := Random.spectralGap_of_lambda2 G hreg (by rw [Fintype.card_fin]; omega) hlam
      rwa [show (3 : ℝ) - (2 * Real.sqrt 2 + ε) = gap by rw [hgap]; ring] at this
    -- "let `ℓ` be as in the definition of `A_n¹`, set `R := R₀(μ, δ, ℓ)`"
    exact not_globallySynchronizing_of_gadgetBall G hreg hgap0 hgapG (ℓ := 4 * (k + 1))
      (by omega) hδmem le_rfl hQ hGS
  -- "`P(globally synchronizing) ≤ P((A_n¹)ᶜ) + P((A_n²)ᶜ)`"
  calc Random.prob n {G | GloballySynchronizing G}
      ≤ Random.prob n (A₁ᶜ ∪ A₂ᶜ) :=
        MeasureTheory.measure_mono (μ := (Random.Gnt n).toOuterMeasure) hsub
    _ ≤ Random.prob n A₁ᶜ + Random.prob n A₂ᶜ :=
        MeasureTheory.measure_union_le (μ := (Random.Gnt n).toOuterMeasure) _ _
    _ ≤ ENNReal.ofReal (κ / 2) + ENNReal.ofReal (κ / 2) := add_le_add hA1 hA2
    _ = ENNReal.ofReal κ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

open scoped Classical in
/-- **Theorem 1.2.** `lim_{n→∞} P(G_{2n,3} is not globally synchronizing) = 1`, where `G_{2n,3}`
is the uniformly random simple `3`-regular graph on `2n` vertices.

This disproves the conjecture that random 3-regular graphs are globally synchronizing with high
probability (Abdalla et al., Section 7; Bandeira, Oberwolfach report, Conjecture 8). -/
theorem main_theorem :
    Filter.Tendsto (fun n => Random.prob (2 * n) {G | ¬ GloballySynchronizing G})
      Filter.atTop (nhds 1) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => Filter.Eventually.of_forall fun n => ?_⟩
  · -- below `1`: from `P(globally synchronizing) ≤ κ` with `κ = (1 − a)/2`
    have hatop : a ≠ ⊤ := ne_top_of_lt ha
    have har : a.toReal < 1 := by
      have := ENNReal.toReal_lt_of_lt_ofReal (b := 1) (by rwa [ENNReal.ofReal_one])
      exact this
    set κ : ℝ := (1 - a.toReal) / 2 with hκ
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (prob_globallySynchronizing_le κ hκ0)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hGS := hN (2 * n) (by omega) (even_two_mul n)
    rw [show {G : SimpleGraph (Fin (2 * n)) | ¬ GloballySynchronizing G}
        = {G | GloballySynchronizing G}ᶜ from rfl, Random.prob_compl]
    calc a < ENNReal.ofReal (1 - κ) :=
          (ENNReal.lt_ofReal_iff_toReal_lt hatop).mpr (by rw [hκ]; linarith)
      _ = 1 - ENNReal.ofReal κ := by rw [ENNReal.ofReal_sub _ hκ0.le, ENNReal.ofReal_one]
      _ ≤ 1 - Random.prob (2 * n) {G | GloballySynchronizing G} := tsub_le_tsub_left hGS 1
  · -- above `1`: a probability is at most `1`
    have hle : Random.prob (2 * n) {G | ¬ GloballySynchronizing G} ≤ 1 := by
      rw [← Random.prob_add_compl (2 * n) {G | ¬ GloballySynchronizing G}]
      exact le_self_add
    exact lt_of_le_of_lt hle ha

end Kuramoto
