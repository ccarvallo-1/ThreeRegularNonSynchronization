/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.ConfigModel

/-!
# Lemma 2.2: `Q_{ℓ,R}` appears as an induced subgraph

* `cycles_poisson` (Bollobás 1980; Wormald 1981): `ℓ`-cycle counts are asymptotically
  Poisson (assumed).
* `simple_prob_pos` (Bender–Canfield 1978; Bollobás 1980): a random configuration is simple
  with probability bounded away from `0` (assumed).
* `sparse_whp`: w.h.p. no set of at most `M` vertices spans more edges than vertices — the
  `O(1/n)` step of the proof, from the configuration model (`ConfigModel.lean`).
* `gadgetBall_whp`: for one fixed `ℓ₀`, `limsup_n P(no induced Q_{ℓ₀,R}) ≤ e^{-2^{ℓ₀-1}/ℓ₀}`,
  from the above and the deterministic extension lemma `exists_inducedCopy` (`Extension.lean`).
* `gadgetcount`: **Lemma 2.2**, with the radius `R = R(ℓ)` allowed to depend on `ℓ`.
-/

@[expose] public section

namespace Kuramoto.Random

open Finset Real

open scoped Classical

/-! ## Lemma 2.2 (`lem:gadgetcount`) -/

/-- The Poisson mean of the number of `ℓ`-cycles in `G_{n,3}`: `λ_ℓ = (d-1)^ℓ / (2ℓ) = 2^{ℓ-1}/ℓ`. -/
noncomputable def poissonMean (ℓ : ℕ) : ℝ := 2 ^ (ℓ - 1) / ℓ

/-- `G` is `3`-regular and contains `Q_{ℓ,R}` as an induced subgraph. This is the event `A_n^1`
of the proof of Theorem 1.2. -/
def HasGadgetBall {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ℓ R : ℕ) [NeZero ℓ] :
    Prop :=
  (∀ v, G.degree v = 3) ∧ ∃ f : Gadget.Vtx ℓ R → Fin n, IsInducedCopy G ℓ R f

/-- **Short cycles are asymptotically Poisson, ASSUMED** (Bollobás 1980; Wormald 1981). For
fixed `ℓ ≥ 3`, the number of `ℓ`-cycles of `G_{n,3}` converges in distribution to
`Poisson(λ_ℓ)`, `λ_ℓ = (d − 1)^ℓ/(2ℓ) = 2^{ℓ-1}/ℓ`. Only the consequence
`limsup_n P(no ℓ-cycle) ≤ e^{-λ_ℓ}` is used, written as: for every `κ > e^{-λ_ℓ}`, eventually
`P(no ℓ-cycle) ≤ κ`. These are the references the paper cites in the proof of Lemma 2.2. -/
axiom cycles_poisson (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (κ : ℝ) (hκ : Real.exp (-poissonMean ℓ) < κ) :
    ∀ᶠ n in Filter.atTop, Even n → prob n {G | HasCycle G ℓ}ᶜ ≤ ENNReal.ofReal κ

/-- **A random configuration is simple with probability bounded away from `0`, ASSUMED**
(Bender–Canfield 1978; Bollobás 1980): for `3n` half-edges paired uniformly at random, the
probability of no loops and no multiple edges tends to `e^{-(d²-1)/4} = e^{-2}` for `d = 3`.
This is the "well known" fact the paper's proof of Lemma 2.2 uses to pass from the
configuration model to `G_{n,3}`. Stated as a ratio of counts; it also forces pairings to exist
(a ratio `0/0` is `0` in Lean). -/
axiom simple_prob_pos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, Even n →
    c ≤ (#(CM.simpleMatchings n) : ℝ) / #(CM.matchings (CM.Half n))

/-- The arithmetic of the conditioning: if `c ≤ A/B`, `A = 6ⁿ R`, `6ⁿ D ≤ K B / n` and
`K ≤ c η n`, then `D ≤ η R`. -/
theorem condition_arith {c η K A B R D n6 nn : ℝ} (hc0 : 0 < c) (hB : 0 < B) (hR : 0 ≤ R)
    (hK0 : 0 ≤ K) (h6 : 0 < n6) (hn : 0 < nn) (hcAB : c ≤ A / B) (hA : A = n6 * R)
    (hD : n6 * D ≤ K * B / nn) (hK : K ≤ c * η * nn) : D ≤ η * R := by
  have h1 : c * B ≤ n6 * R := by rw [← hA]; rw [le_div_iff₀ hB] at hcAB; linarith
  have h2 : n6 * D * nn ≤ K * B := by rwa [le_div_iff₀ hn] at hD
  have h3 : (c * n6 * nn) * D ≤ (c * n6 * nn) * (η * R) := by
    calc (c * n6 * nn) * D = c * (n6 * D * nn) := by ring
      _ ≤ c * (K * B) := mul_le_mul_of_nonneg_left h2 hc0.le
      _ = K * (c * B) := by ring
      _ ≤ K * (n6 * R) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ (c * η * nn) * (n6 * R) := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = (c * n6 * nn) * (η * R) := by ring
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- **No small dense subgraphs.** For fixed `M`, with probability `→ 1` every set of at most `M`
vertices of `G_{n,3}` spans at most as many edges as vertices.

This is the `O(1/n)` step of the paper's proof of Lemma 2.2, done as in the paper: in the
configuration model the bad pairings are a fraction `≤ K_M/n` (`CM.card_bad_le`, a first-moment
count), `G_{n,3}` is the configuration model conditioned on being simple
(`CM.card_simple_filter`), and conditioning divides by `P(simple) ≥ c` (`simple_prob_pos`). -/
theorem sparse_whp (M : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, Even n → prob n {G | Sparse G M}ᶜ ≤ ENNReal.ofReal η := by
  obtain ⟨c, hc0, hc⟩ := simple_prob_pos
  set K : ℝ := ∑ s ∈ Finset.range (M + 1), ((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K / (c * η) ≤ N := exists_nat_ge _
  filter_upwards [hc, Filter.eventually_ge_atTop (max (2 * M + 2) (N + 1))] with n hcn hn heven
  have hcn := hcn heven
  have hn1 : 2 * M + 2 ≤ n := le_of_max_le_left hn
  have hnN : N + 1 ≤ n := le_of_max_le_right hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- `P(simple) ≥ c > 0` forces pairings to exist
  have hMt : (0 : ℝ) < #(CM.matchings (CM.Half n)) := by
    by_contra h
    have h0 : ((#(CM.matchings (CM.Half n)) : ℕ) : ℝ) = 0 := le_antisymm (not_lt.mp h) (by positivity)
    rw [h0, div_zero] at hcn
    linarith
  -- `#simple = 6ⁿ · #regular`, and the same for the non-sparse ones
  have hreg : #(CM.simpleMatchings n) = 6 ^ n * #(regularGraphs n) := by
    simpa using CM.card_simple_filter (n := n) (fun _ => True)
  have hbN : #((CM.simpleMatchings n).filter fun σ => ¬ Sparse (CM.cgraph σ) M)
      = 6 ^ n * #((regularGraphs n).filter fun G => ¬ Sparse G M) := by
    convert CM.card_simple_filter (n := n) (fun G => ¬ Sparse G M) using 2 <;> congr!
  have hbound := CM.card_bad_le M hn1
  rw [hbN, show ((6 ^ n * #((regularGraphs n).filter fun G => ¬ Sparse G M) : ℕ) : ℝ)
      = (6 : ℝ) ^ n * #((regularGraphs n).filter fun G => ¬ Sparse G M) by push_cast; ring]
    at hbound
  have hregR : ((#(CM.simpleMatchings n) : ℕ) : ℝ) = 6 ^ n * #(regularGraphs n) := by
    exact_mod_cast hreg
  have hK' : K ≤ c * η * n := by
    have : K / (c * η) ≤ n := hN.trans (by exact_mod_cast (by omega : N ≤ n))
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  -- `#bad ≤ η · #reg`
  have hkey : ((#((regularGraphs n).filter fun G => ¬ Sparse G M) : ℕ) : ℝ)
      ≤ η * #(regularGraphs n) :=
    condition_arith hc0 hMt (by positivity) hK (by positivity) hn0 hcn hregR hbound hK'
  -- there are `3`-regular graphs on `Fin n`
  have hne : (regularGraphs n).Nonempty := by
    rw [← Finset.card_pos]
    have hA : (0 : ℝ) < #(CM.simpleMatchings n) := by
      have := (le_div_iff₀ hMt).mp hcn
      nlinarith
    rw [hregR] at hA
    have : (0 : ℝ) < #(regularGraphs n) := pos_of_mul_pos_right hA (by positivity)
    exact_mod_cast this
  -- back to probabilities
  have final : ((#((regularGraphs n).filter fun G => ¬ Sparse G M) : ℕ) : ENNReal)
      / #(regularGraphs n) ≤ ENNReal.ofReal η := by
    refine ENNReal.div_le_of_le_mul ?_
    calc ((#((regularGraphs n).filter fun G => ¬ Sparse G M) : ℕ) : ENNReal)
        = ENNReal.ofReal (#((regularGraphs n).filter fun G => ¬ Sparse G M) : ℕ) :=
          (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (η * #(regularGraphs n)) := ENNReal.ofReal_le_ofReal hkey
      _ = ENNReal.ofReal η * #(regularGraphs n) := by
          rw [ENNReal.ofReal_mul hη.le, ENNReal.ofReal_natCast]
  simp only [prob, Gnt, dite_eq_left hne]
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  convert final using 3
  · congr 1
    ext G
    simp


/-- For even `n ≥ 4` the measure `G_{n,3}` is uniform on the `3`-regular graphs, so almost
surely `3`-regular. -/
theorem prob_not_regular {n : ℕ} (hne : (regularGraphs n).Nonempty) :
    prob n {G | ∀ v, G.degree v = 3}ᶜ = 0 := by
  simp only [prob, Gnt, dite_eq_left hne]
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, PMF.support_uniformOfFinset, Set.disjoint_left]
  intro G hG hG'
  exact hG' (Finset.mem_filter.mp hG).2

/-- **Lemma 2.2 for a fixed `ℓ₀`: the core of its proof.** For fixed `ℓ ≡ 0 (mod 4)` and `R ≥ 1`,

  `limsup_{n even} P(G_{n,3} does not contain Q_{ℓ,R} as an induced subgraph) ≤ e^{-2^{ℓ-1}/ℓ}`,

written, as a `limsup` bound always can be, as: for every `κ > e^{-2^{ℓ-1}/ℓ}`, eventually the
probability is `≤ κ`. For fixed `ℓ` the probability does **not** tend to `0`: it tends to
`e^{-λ_ℓ}`. Lemma 2.2 (`gadgetcount`) applies this with `ℓ = ℓ₀(ε)`.

The proof follows the paper's: with probability `→ 1 − e^{-λ_ℓ}` there is an `ℓ`-cycle
(`cycles_poisson`), and w.h.p. it extends to an induced `Q_{ℓ,R}`. The extension is
deterministic once small vertex sets are sparse (`exists_inducedCopy`, proved), and small vertex
sets are sparse w.h.p. (`sparse_whp`). -/
theorem gadgetBall_whp (ℓ R : ℕ) [NeZero ℓ] (hℓ4 : ℓ % 4 = 0) (hR : 0 < R)
    (κ : ℝ) (hκ : Real.exp (-poissonMean ℓ) < κ) :
    ∀ᶠ n in Filter.atTop, Even n →
      prob n {G | HasGadgetBall G ℓ R}ᶜ ≤ ENNReal.ofReal κ := by
  have hℓ3 : 3 ≤ ℓ := by have := NeZero.ne ℓ; omega
  have hpm : 0 < poissonMean ℓ := by unfold poissonMean; positivity
  have he1 : Real.exp (-poissonMean ℓ) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  -- split `κ = κ₁ + (κ − κ₁)` with `e^{-λ_ℓ} < κ₁ < min κ 1`
  set e := Real.exp (-poissonMean ℓ) with he
  have hmin : e < min κ 1 := lt_min hκ he1
  set κ₁ := (e + min κ 1) / 2 with hκ₁
  have h1 : e < κ₁ := by rw [hκ₁]; linarith
  have h2 : κ₁ < min κ 1 := by rw [hκ₁]; linarith
  have h2a : κ₁ < κ := h2.trans_le (min_le_left _ _)
  have h2b : κ₁ < 1 := h2.trans_le (min_le_right _ _)
  have he0 : 0 < e := Real.exp_pos _
  filter_upwards [cycles_poisson ℓ hℓ3 κ₁ h1, sparse_whp (2 ^ R * ℓ) (κ - κ₁) (by linarith)]
    with n hc hs heven
  have hc := hc heven
  have hs := hs heven
  -- there are `3`-regular graphs on `Fin n`: otherwise `G_{n,3}` is the empty graph, which has
  -- no cycle, and `P(no ℓ-cycle) = 1 > κ₁`
  have hne : (regularGraphs n).Nonempty := by
    by_contra hne
    have hone : prob n {G | HasCycle G ℓ}ᶜ = 1 := by
      simp only [prob, Gnt, dite_eq_right hne]
      rw [PMF.toOuterMeasure_pure_apply, ite_eq_left]
      rintro ⟨c, _, hadj⟩
      simpa using hadj 0
    rw [hone] at hc
    have hlt : ENNReal.ofReal κ₁ < 1 := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr h2b
    exact absurd hc (not_le.mpr hlt)
  -- `{no induced Q_{ℓ,R}} ⊆ {no ℓ-cycle} ∪ {not sparse} ∪ {not 3-regular}`
  have hsub : {G : SimpleGraph (Fin n) | HasGadgetBall G ℓ R}ᶜ
      ⊆ ({G | HasCycle G ℓ}ᶜ ∪ {G | Sparse G (2 ^ R * ℓ)}ᶜ) ∪ {G | ∀ v, G.degree v = 3}ᶜ := by
    intro G hG
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hcon hG
    obtain ⟨⟨hcy, hsp⟩, hreg⟩ := hcon
    obtain ⟨f, hf⟩ := exists_inducedCopy G hreg hℓ3 hR hcy hsp
    exact hG ⟨hreg, f, hf⟩
  calc prob n {G | HasGadgetBall G ℓ R}ᶜ
      ≤ prob n (({G | HasCycle G ℓ}ᶜ ∪ {G | Sparse G (2 ^ R * ℓ)}ᶜ)
          ∪ {G | ∀ v, G.degree v = 3}ᶜ) :=
        MeasureTheory.measure_mono (μ := (Gnt n).toOuterMeasure) hsub
    _ ≤ prob n {G | HasCycle G ℓ}ᶜ + prob n {G | Sparse G (2 ^ R * ℓ)}ᶜ
          + prob n {G | ∀ v, G.degree v = 3}ᶜ :=
        (MeasureTheory.measure_union_le (μ := (Gnt n).toOuterMeasure) _ _).trans
          (add_le_add (MeasureTheory.measure_union_le (μ := (Gnt n).toOuterMeasure) _ _) le_rfl)
    _ ≤ ENNReal.ofReal κ₁ + ENNReal.ofReal (κ - κ₁) + 0 := by
        rw [prob_not_regular hne]; exact add_le_add (add_le_add hc hs) le_rfl
    _ = ENNReal.ofReal κ := by
        rw [add_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

/-- `16^k ≥ (k+1)²`, the elementary growth bound behind `λ_ℓ → ∞`. -/
theorem sq_le_sixteen_pow (k : ℕ) : ((k : ℝ) + 1) ^ 2 ≤ 16 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    push_cast
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    calc ((k : ℝ) + 1 + 1) ^ 2 ≤ 16 * ((k : ℝ) + 1) ^ 2 := by nlinarith
      _ ≤ 16 * 16 ^ k := by linarith
      _ = 16 ^ (k + 1) := by ring

/-- `λ_{4(k+1)} ≥ k + 1`. -/
theorem poissonMean_ge (k : ℕ) : (k : ℝ) + 1 ≤ poissonMean (4 * (k + 1)) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have h2 : (2 : ℝ) ^ (4 * (k + 1) - 1) = 8 * 16 ^ k := by
    rw [show 4 * (k + 1) - 1 = 3 + 4 * k by omega, pow_add, pow_mul]; norm_num
  rw [poissonMean, h2, le_div_iff₀ (by positivity)]
  push_cast
  nlinarith [sq_le_sixteen_pow k]

/-- "Given `κ`, choose `ℓ ≡ 0 (mod 4)` such that `e^{-λ_ℓ} < κ`. This is possible because
`λ_ℓ = 2^{ℓ-1}/ℓ → ∞`." -/
theorem exists_ell (κ : ℝ) (hκ : 0 < κ) :
    ∃ ℓ : ℕ, ℓ % 4 = 0 ∧ 4 ≤ ℓ ∧ Real.exp (-poissonMean ℓ) < κ := by
  set k : ℕ := ⌈-Real.log κ⌉₊
  refine ⟨4 * (k + 1), by omega, by omega, ?_⟩
  have hk : -Real.log κ ≤ k := Nat.le_ceil _
  calc Real.exp (-poissonMean (4 * (k + 1))) ≤ Real.exp (-((k : ℝ) + 1)) :=
        Real.exp_le_exp.mpr (by linarith [poissonMean_ge k])
    _ < Real.exp (Real.log κ) := Real.exp_lt_exp.mpr (by linarith)
    _ = κ := Real.exp_log hκ

instance (k : ℕ) : NeZero (4 * (k + 1)) := ⟨by omega⟩

/-- **Lemma 2.2 (`lem:gadgetcount`).** With probability tending to `1` (over even `n`) there
exists `ℓ = 4k`, `k ≥ 1`, such that `Q_{ℓ,R}` is an induced subgraph of `G_{n,3}`.

The radius may depend on `ℓ`, `R = R(ℓ)`, as the proof of Theorem 1.2 needs
(`A_n¹` asks for `Q_{ℓ, R₀(μ,δ,ℓ)}`); a fixed `R` is the constant function. The proof is the
paper's: given `ε` (here `κ`), fix `ℓ₀` with `e^{-2^{ℓ₀-1}/ℓ₀} < ε` (`exists_ell`); then `R(ℓ₀)`
is a fixed number, and w.h.p. an `ℓ₀`-cycle exists and extends to an induced `Q_{ℓ₀,R(ℓ₀)}`
(`gadgetBall_whp`). -/
theorem gadgetcount (Rℓ : ℕ → ℕ) (hR : ∀ ℓ, 0 < Rℓ ℓ) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ n in Filter.atTop, Even n →
      prob n {G | ∃ k : ℕ, HasGadgetBall G (4 * (k + 1)) (Rℓ (4 * (k + 1)))}ᶜ
        ≤ ENNReal.ofReal κ := by
  -- "there exists `ℓ₀ = ℓ₀(ε)` such that `P(there is no cycle C_{ℓ₀}) ≤ ε/2`"
  obtain ⟨ℓ, hℓ4, hℓ4', hℓκ⟩ := exists_ell κ hκ
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = 4 * (k + 1) := ⟨ℓ / 4 - 1, by omega⟩
  -- "each such cycle can be extended to `Q_{ℓ₀,R}` with probability `1 − o(1)`"
  filter_upwards [gadgetBall_whp (4 * (k + 1)) (Rℓ (4 * (k + 1))) hℓ4 (hR _) κ hℓκ]
    with n hn heven
  refine le_trans (MeasureTheory.measure_mono (μ := (Gnt n).toOuterMeasure) ?_) (hn heven)
  intro G hG hk
  exact hG ⟨k, hk⟩

end Kuramoto.Random
