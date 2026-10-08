/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Extension
public import Kuramoto.RandomGraph
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.BigOperators

/-!
# The configuration model, and the `O(1/n)` step of Lemma 2.2

The proof of Lemma 2.2 works "in the configuration model, as the probability for a simple
configuration is well known to be a constant bounded away from `0`", and shows that the
exploration around an `ℓ`-cycle meets an already exposed vertex only with probability
`O(1/n)`. This file formalizes that part.

* **Pairings.** The `3n` half-edges `Half n = Fin n × Fin 3`; a configuration is a perfect
  matching of them (`matchings`, as fixed-point-free involutions). `card_fixes_mul`: the pairings
  containing `k` given disjoint pairs are a fraction `1/((N−1)(N−3)⋯(N−2k+1))` of all, proved by
  symmetry (conjugating by a transposition).
* **Graph of a pairing.** `cgraph σ`; a simple pairing (`IsSimple`: no loops, no multiple edges)
  gives a `3`-regular graph. `card_fibre`: every `3`-regular graph comes from exactly `6ⁿ` simple
  pairings (a pairing over `G` is a labelling of the half-edges at each vertex by its three
  neighbours). Hence `card_simple_filter`: `G_{n,3}` is the configuration model conditioned on
  being simple.
* **First moment.** `card_bad_le`: the fraction of pairings whose graph is simple and has a set
  `S` of at most `M` vertices spanning more than `|S|` edges is at most `K_M / n`. Such a set
  contains `|S| + 1` disjoint pairs of half-edges (`exists_pairs`); there are `≤ n^s` sets of size
  `s` and `≤ (9s²)^{s+1}` choices of pairs, each present with probability `≤ (2n)^{-(s+1)}`.

The only probabilistic input left, `P(simple) ≥ c > 0`, is the axiom `Random.simple_prob_pos`
(Bender–Canfield 1978, Bollobás 1980) in `GadgetCount.lean`.
-/

@[expose] public section

namespace Kuramoto.CM

open Finset

/-! ## Pairings -/

section Matching

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- A perfect matching of `H`, as a fixed-point-free involution. -/
def IsMatching (σ : Equiv.Perm H) : Prop := (∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x

open scoped Classical in
noncomputable def matchings (H : Type*) [Fintype H] [DecidableEq H] : Finset (Equiv.Perm H) :=
  univ.filter IsMatching

/-- The half-edges occurring in a list of pairs. -/
def flat (L : List (H × H)) : List H := L.flatMap fun p => [p.1, p.2]

/-- `σ` matches every pair of `L`. -/
def Fixes (L : List (H × H)) (σ : Equiv.Perm H) : Prop := ∀ p ∈ L, σ p.1 = p.2

omit [Fintype H] [DecidableEq H] in
theorem flat_cons (a b : H) (L : List (H × H)) : flat ((a, b) :: L) = a :: b :: flat L := rfl

omit [Fintype H] [DecidableEq H] in
theorem length_flat (L : List (H × H)) : (flat L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [flat, List.flatMap_cons] at ih ⊢; omega

omit [Fintype H] in
/-- Conjugating a matching by a transposition gives a matching. -/
theorem isMatching_conj {σ : Equiv.Perm H} (hσ : IsMatching σ) (b c : H) :
    IsMatching (Equiv.swap b c * σ * Equiv.swap b c) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp [Equiv.Perm.mul_apply, hσ.1]
  · simp only [Equiv.Perm.mul_apply]
    intro h
    have := congrArg (Equiv.swap b c) h
    simp only [Equiv.swap_apply_self] at this
    exact hσ.2 _ this

open scoped Classical in
/-- **Adding one pair divides the count by `N − 2|L| − 1`.** Among the matchings containing the
pairs of `L`, the partner of a new half-edge `a` is equally likely to be any of the
`N − 2|L| − 1` half-edges not yet used: conjugating by the transposition `(b c)` moves the
matchings with `a ↦ b` bijectively onto those with `a ↦ c`. -/
theorem card_fixes_cons (a b : H) (L : List (H × H)) (hnd : (a :: b :: flat L).Nodup) :
    #((matchings H).filter (Fixes ((a, b) :: L))) * (Fintype.card H - (flat L).length - 1)
      = #((matchings H).filter (Fixes L)) := by
  obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
  obtain ⟨hb, hL⟩ := List.nodup_cons.mp hnd'
  have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
  have haL : a ∉ flat L := fun h => ha (List.mem_cons_of_mem _ h)
  set A := (matchings H).filter (Fixes L) with hA
  set C := univ \ insert a (flat L).toFinset with hC
  have hCcard : #C = Fintype.card H - (flat L).length - 1 := by
    rw [hC, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_insert_of_notMem (by simpa using haL), List.toFinset_card_of_nodup hL]
    omega
  have hbC : b ∈ C := by
    simp only [hC, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, List.mem_toFinset,
      true_and, not_or]
    exact ⟨Ne.symm hab, hb⟩
  -- a matching containing `L` sends `a` outside `L ∪ {a}`
  have hmaps : (A : Set (Equiv.Perm H)).MapsTo (fun σ => σ a) C := by
    intro σ hσ
    have hσ' := Finset.mem_coe.mp hσ
    rw [hA, Finset.mem_filter, matchings, Finset.mem_filter] at hσ'
    obtain ⟨⟨_, hinv, hfix⟩, hfixes⟩ := hσ'
    simp only [hC, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.mem_univ,
      Finset.mem_insert, List.mem_toFinset, true_and, not_or]
    refine ⟨hfix a, fun hmem => ?_⟩
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · -- `σ a = p.1`, so `a = σ p.1 = p.2`
      have : a = p.2 := by rw [← hfixes p hp, ← hx, hinv]
      exact haL (List.mem_flatMap.mpr ⟨p, hp, by simp [this]⟩)
    · -- `σ a = p.2 = σ p.1`, so `a = p.1`
      have : a = p.1 := by
        have h2 := congrArg σ hx
        rw [hinv, ← hfixes p hp, hinv] at h2
        exact h2
      exact haL (List.mem_flatMap.mpr ⟨p, hp, by simp [this]⟩)
  -- all fibres have the size of the fibre over `b`
  have hfib : ∀ c ∈ C, #(A.filter (fun σ => σ a = c)) = #(A.filter (fun σ => σ a = b)) := by
    intro c hc
    have hcL : c ∉ flat L ∧ c ≠ a := by
      simp only [hC, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, List.mem_toFinset,
        true_and, not_or] at hc
      exact ⟨hc.2, hc.1⟩
    set τ := Equiv.swap b c
    have hτL : ∀ x ∈ flat L, τ x = x := fun x hx =>
      Equiv.swap_apply_of_ne_of_ne (fun h => hb (h ▸ hx)) (fun h => hcL.1 (h ▸ hx))
    have hτa : τ a = a := Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hcL.2)
    have hmem : ∀ p ∈ L, p.1 ∈ flat L ∧ p.2 ∈ flat L := fun p hp =>
      ⟨List.mem_flatMap.mpr ⟨p, hp, by simp⟩, List.mem_flatMap.mpr ⟨p, hp, by simp⟩⟩
    have hconj : ∀ σ ∈ A, τ * σ * τ ∈ A := by
      intro σ hσ
      simp only [hA, Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hσ ⊢
      refine ⟨isMatching_conj hσ.1 b c, fun p hp => ?_⟩
      simp only [Equiv.Perm.mul_apply, hτL _ (hmem p hp).1, hσ.2 p hp, hτL _ (hmem p hp).2]
    refine Finset.card_nbij' (fun σ => τ * σ * τ) (fun σ => τ * σ * τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hσ ⊢
      refine ⟨hconj σ hσ.1, ?_⟩
      simp only [Equiv.Perm.mul_apply, hτa, hσ.2, τ, Equiv.swap_apply_right]
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hσ ⊢
      refine ⟨hconj σ hσ.1, ?_⟩
      simp only [Equiv.Perm.mul_apply, hτa, hσ.2, τ, Equiv.swap_apply_left]
    · intro σ _
      show τ * (τ * σ * τ) * τ = σ
      simp only [τ, mul_assoc, Equiv.swap_mul_self, mul_one]
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
    · intro σ _
      show τ * (τ * σ * τ) * τ = σ
      simp only [τ, mul_assoc, Equiv.swap_mul_self, mul_one]
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  have hsplit := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hCcard] at hsplit
  have hfilter : A.filter (fun σ => σ a = b) = (matchings H).filter (Fixes ((a, b) :: L)) := by
    ext σ
    simp only [hA, Finset.mem_filter, Fixes, List.mem_cons, forall_eq_or_imp]
    tauto
  rw [hsplit, hfilter, mul_comm]

open scoped Classical in
/-- **`P(the pairs of L are all matched) = 1/((N−1)(N−3)⋯(N−2k+1))`**, `k = |L|`, as a count. -/
theorem card_fixes_mul (L : List (H × H)) (hnd : (flat L).Nodup) :
    #((matchings H).filter (Fixes L)) * ∏ t ∈ range L.length, (Fintype.card H - 2 * t - 1)
      = #(matchings H) := by
  induction L with
  | nil =>
    simp only [List.length_nil, range_zero, prod_empty, mul_one]
    congr 1
    ext σ
    simp [Fixes]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [flat_cons] at hnd
    have hL : (flat L).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    rw [List.length_cons, prod_range_succ,
      mul_comm (∏ x ∈ range L.length, (Fintype.card H - 2 * x - 1)), ← mul_assoc,
      ← length_flat, card_fixes_cons a b L hnd, ih hL]

open scoped Classical in
/-- The crude form used in the first-moment bound: `#{σ ⊇ L} · (N − 2k)^k ≤ #matchings`. -/
theorem card_fixes_le (L : List (H × H)) (hnd : (flat L).Nodup) :
    #((matchings H).filter (Fixes L)) * (Fintype.card H - 2 * L.length) ^ L.length
      ≤ #(matchings H) := by
  rw [← card_fixes_mul L hnd]
  refine Nat.mul_le_mul_left _ ?_
  have hc : (Fintype.card H - 2 * L.length) ^ L.length
      = ∏ _t ∈ range L.length, (Fintype.card H - 2 * L.length) := by simp
  rw [hc]
  exact Finset.prod_le_prod fun t ht => by rw [Finset.mem_range] at ht; omega

end Matching


/-! ## The graph of a pairing -/

section Graph

variable {n : ℕ}

/-- The `3n` half-edges: three at each vertex. -/
abbrev Half (n : ℕ) := Fin n × Fin 3

/-- The (simple) graph underlying a pairing: `u ~ v` when a half-edge of `u` is paired with a
half-edge of `v`, `u ≠ v`. -/
def cgraph (σ : Equiv.Perm (Half n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ i j, σ (u, i) = (v, j)

/-- No loops and no multiple edges. -/
def IsSimple (σ : Equiv.Perm (Half n)) : Prop :=
  (∀ v i, (σ (v, i)).1 ≠ v) ∧ ∀ v i j, (σ (v, i)).1 = (σ (v, j)).1 → i = j

open scoped Classical in
noncomputable def simpleMatchings (n : ℕ) : Finset (Equiv.Perm (Half n)) :=
  (matchings (Half n)).filter IsSimple

theorem cgraph_adj_iff {σ : Equiv.Perm (Half n)} (hσ : IsMatching σ) (hs : IsSimple σ)
    (v u : Fin n) : (cgraph σ).Adj v u ↔ ∃ i, (σ (v, i)).1 = u := by
  rw [cgraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨i, j, h⟩ | ⟨j, i, h⟩⟩
    · exact ⟨i, by rw [h]⟩
    · refine ⟨i, ?_⟩
      have := congrArg σ h
      rw [hσ.1] at this
      rw [← this]
  · rintro ⟨i, rfl⟩
    exact ⟨fun h => hs.1 v i h.symm, Or.inl ⟨i, (σ (v, i)).2, rfl⟩⟩

open scoped Classical in
theorem degree_cgraph {σ : Equiv.Perm (Half n)} (hσ : IsMatching σ) (hs : IsSimple σ) (v : Fin n) :
    (cgraph σ).degree v = 3 := by
  have : (cgraph σ).neighborFinset v = univ.image fun i => (σ (v, i)).1 := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, cgraph_adj_iff hσ hs, Finset.mem_image,
      Finset.mem_univ, true_and]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, this,
    Finset.card_image_of_injective _ (fun i j h => hs.2 v i j h)]
  simp

section Fibre

open scoped Classical

variable (G : SimpleGraph (Fin n))

/-- Labellings of the half-edges at each vertex by its neighbours. -/
abbrev Labelling := (v : Fin n) → (Fin 3 ≃ G.neighborFinset v)

theorem mem_nbr_symm (ℓ : Labelling G) (v : Fin n) (i : Fin 3) :
    v ∈ G.neighborFinset (ℓ v i) := by
  have := (ℓ v i).2
  rw [SimpleGraph.mem_neighborFinset] at this ⊢
  exact this.symm

theorem symm_apply_of (ℓ : Labelling G) {x y w : Fin n} (hxy : x = y)
    (h : w ∈ G.neighborFinset x) {j : Fin 3} (hj : (ℓ y j : Fin n) = w) :
    (ℓ x).symm ⟨w, h⟩ = j := by
  subst hxy
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext hj.symm

/-- The pairing of a labelling: half-edge `i` at `v` goes to the half-edge of `w = ℓ_v(i)` that
`w` labels by `v`. -/
def pairFun (ℓ : Labelling G) (h : Half n) : Half n :=
  ((ℓ h.1 h.2 : Fin n), (ℓ (ℓ h.1 h.2)).symm ⟨h.1, mem_nbr_symm G ℓ h.1 h.2⟩)

theorem pairFun_involutive (ℓ : Labelling G) : Function.Involutive (pairFun G ℓ) := by
  rintro ⟨v, i⟩
  have h1 : (ℓ (ℓ v i : Fin n)) ((ℓ (ℓ v i : Fin n)).symm ⟨v, mem_nbr_symm G ℓ v i⟩)
      = ⟨v, mem_nbr_symm G ℓ v i⟩ := Equiv.apply_symm_apply _ _
  have h1' : ((ℓ (ℓ v i : Fin n)) ((ℓ (ℓ v i : Fin n)).symm ⟨v, mem_nbr_symm G ℓ v i⟩) : Fin n)
      = v := by rw [h1]
  exact Prod.ext h1' (symm_apply_of G ℓ h1' _ rfl)

/-- The pairing of a labelling, as a permutation. -/
def pairPerm (ℓ : Labelling G) : Equiv.Perm (Half n) :=
  Function.Involutive.toPerm _ (pairFun_involutive G ℓ)

theorem pairPerm_apply (ℓ : Labelling G) (h : Half n) : pairPerm G ℓ h = pairFun G ℓ h := rfl

theorem pairPerm_mem (ℓ : Labelling G) :
    pairPerm G ℓ ∈ simpleMatchings n ∧ cgraph (pairPerm G ℓ) = G := by
  have hne : ∀ v i, ((ℓ v i : Fin n)) ≠ v := fun v i h => by
    have := (ℓ v i).2
    rw [SimpleGraph.mem_neighborFinset, h] at this
    exact G.irrefl this
  have hmatch : IsMatching (pairPerm G ℓ) :=
    ⟨fun x => pairFun_involutive G ℓ x, fun ⟨v, i⟩ h => hne v i (congrArg Prod.fst h)⟩
  have hsimple : IsSimple (pairPerm G ℓ) :=
    ⟨fun v i => hne v i, fun v i j h => (ℓ v).injective (Subtype.ext h)⟩
  refine ⟨by simp [simpleMatchings, matchings, hmatch, hsimple], ?_⟩
  ext v u
  rw [cgraph_adj_iff hmatch hsimple]
  constructor
  · rintro ⟨i, rfl⟩
    exact (G.mem_neighborFinset _ _).mp (ℓ v i).2
  · intro h
    obtain ⟨i, hi⟩ := (ℓ v).surjective ⟨u, (G.mem_neighborFinset _ _).mpr h⟩
    exact ⟨i, by simp [pairPerm_apply, pairFun, hi]⟩

theorem fibre_spec (σ : {σ // σ ∈ simpleMatchings n ∧ cgraph σ = G}) :
    IsMatching σ.1 ∧ IsSimple σ.1 := by
  have := σ.2.1
  simp only [simpleMatchings, matchings, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

theorem fibre_adj (σ : {σ // σ ∈ simpleMatchings n ∧ cgraph σ = G}) (v u : Fin n) :
    G.Adj v u ↔ ∃ i, (σ.1 (v, i)).1 = u := by
  rw [← cgraph_adj_iff (fibre_spec G σ).1 (fibre_spec G σ).2, σ.2.2]

/-- The labelling read off a pairing in the fibre over `G`. -/
noncomputable def labelOf (σ : {σ // σ ∈ simpleMatchings n ∧ cgraph σ = G}) : Labelling G :=
  fun v => Equiv.ofBijective
    (fun i => ⟨(σ.1 (v, i)).1, (G.mem_neighborFinset _ _).mpr ((fibre_adj G σ v _).mpr ⟨i, rfl⟩)⟩)
    ⟨fun i j h => (fibre_spec G σ).2.2 v i j (congrArg Subtype.val h), fun w => by
      obtain ⟨i, hi⟩ := (fibre_adj G σ v w).mp ((G.mem_neighborFinset _ _).mp w.2)
      exact ⟨i, Subtype.ext hi⟩⟩

theorem labelOf_apply (σ : {σ // σ ∈ simpleMatchings n ∧ cgraph σ = G}) (v : Fin n) (i : Fin 3) :
    ((labelOf G σ v i : Fin n)) = (σ.1 (v, i)).1 := rfl

/-- **The fibre over `G` is the set of labellings.** -/
noncomputable def fibreEquiv : {σ // σ ∈ simpleMatchings n ∧ cgraph σ = G} ≃ Labelling G where
  toFun := labelOf G
  invFun ℓ := ⟨pairPerm G ℓ, pairPerm_mem G ℓ⟩
  left_inv σ := by
    have hσ := (fibre_spec G σ).1
    apply Subtype.ext
    ext ⟨v, i⟩ : 1
    show pairFun G (labelOf G σ) (v, i) = σ.1 (v, i)
    refine Prod.ext (labelOf_apply G σ v i) (symm_apply_of G _ rfl _ ?_)
    rw [labelOf_apply]
    show (σ.1 (σ.1 (v, i))).1 = v
    rw [hσ.1]
  right_inv ℓ := by
    funext v
    ext i
    rw [labelOf_apply]
    rfl

theorem card_fibre (hreg : ∀ v, G.degree v = 3) :
    #((simpleMatchings n).filter fun σ => cgraph σ = G) = 6 ^ n := by
  have h1 : #((simpleMatchings n).filter fun σ => cgraph σ = G)
      = Fintype.card {σ // σ ∈ simpleMatchings n ∧ cgraph σ = G} := by
    rw [Fintype.card_subtype]; congr 1; ext σ; simp
  have h3 : ∀ v, Fintype.card (Fin 3 ≃ G.neighborFinset v) = 6 := fun v => by
    have hc : Fintype.card (Fin 3) = Fintype.card (G.neighborFinset v) := by
      rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree, hreg v, Fintype.card_fin]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc)]
    rfl
  rw [h1, Fintype.card_congr (fibreEquiv G), Fintype.card_pi,
    Finset.prod_congr rfl fun v _ => h3 v, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Fibre

open scoped Classical in
/-- **`G_{n,3}` is the configuration model conditioned on being simple**: for every property `P`,
the simple pairings whose graph has `P` are `6ⁿ` times the `3`-regular graphs with `P`. -/
theorem card_simple_filter (P : SimpleGraph (Fin n) → Prop) :
    #((simpleMatchings n).filter fun σ => P (cgraph σ)) = 6 ^ n * #((Random.regularGraphs n).filter P) := by
  have hmaps : Set.MapsTo cgraph
      (((simpleMatchings n).filter fun σ => P (cgraph σ) : Finset _) : Set (Equiv.Perm (Half n)))
      (((Random.regularGraphs n).filter P : Finset _) : Set (SimpleGraph (Fin n))) := by
    intro σ hσ
    rw [Finset.mem_coe, Finset.mem_filter] at hσ
    have hs := hσ.1
    simp only [simpleMatchings, matchings, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, hσ.2⟩
    simp only [Random.regularGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact degree_cgraph hs.1 hs.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ G ∈ (Random.regularGraphs n).filter P,
      #(((simpleMatchings n).filter fun σ => P (cgraph σ)).filter fun σ => cgraph σ = G)
        = 6 ^ n := by
    intro G hG
    rw [Finset.mem_filter] at hG
    have hreg : ∀ v, G.degree v = 3 := by simpa [Random.regularGraphs] using hG.1
    rw [← card_fibre G hreg, Finset.filter_filter]
    congr 1
    ext σ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hG.2, h2⟩
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

end Graph

/-! ## The first moment: no small dense sets -/

section FirstMoment

open scoped Classical

variable {n : ℕ}

/-- An injective numbering of the half-edges, used to pick one half-edge of each pair. -/
noncomputable def key (h : Half n) : ℕ := (Fintype.equivFin (Half n) h : ℕ)

theorem key_injective : Function.Injective (key (n := n)) := fun _ _ h =>
  (Fintype.equivFin _).injective (Fin.ext h)

/-- The edges of `G(σ)` inside `S` come from half-edges of `S` paired inside `S`. -/
theorem sum_nbr_le {σ : Equiv.Perm (Half n)} (hσ : IsMatching σ) (hs : IsSimple σ)
    (S : Finset (Fin n)) :
    ∑ x ∈ S, ((cgraph σ).neighborFinset x ∩ S).card
      ≤ #((S ×ˢ (univ : Finset (Fin 3))).filter fun h => (σ h).1 ∈ S) := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.card_filter]
  calc #((cgraph σ).neighborFinset x ∩ S)
      ≤ #((univ.filter fun i => (σ (x, i)).1 ∈ S).image fun i => (σ (x, i)).1) := by
        refine Finset.card_le_card fun u hu => ?_
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, cgraph_adj_iff hσ hs] at hu
        obtain ⟨⟨i, rfl⟩, hS⟩ := hu
        exact Finset.mem_image.mpr ⟨i, by simp [hS], rfl⟩
    _ ≤ _ := Finset.card_image_le

/-- **A dense set yields `|S| + 1` disjoint pairs inside it.** If `S` spans more than `|S|`
edges of `G(σ)`, then `σ` contains `|S| + 1` disjoint pairs of half-edges of `S`. -/
theorem exists_pairs {σ : Equiv.Perm (Half n)} (hσ : IsMatching σ) (hs : IsSimple σ)
    (S : Finset (Fin n))
    (hbig : 2 * S.card < ∑ x ∈ S, ((cgraph σ).neighborFinset x ∩ S).card) :
    ∃ p : Fin (S.card + 1) → Half n × Half n,
      (∀ t, p t ∈ (S ×ˢ (univ : Finset (Fin 3))) ×ˢ (S ×ˢ (univ : Finset (Fin 3)))) ∧
      (flat (List.ofFn p)).Nodup ∧ Fixes (List.ofFn p) σ := by
  set MS := (S ×ˢ (univ : Finset (Fin 3))).filter fun h => (σ h).1 ∈ S with hMSdef
  set R := MS.filter fun h => key h < key (σ h) with hRdef
  have hMS : MS ⊆ R ∪ R.image σ := by
    intro h hh
    have hne : key h ≠ key (σ h) := fun e => hσ.2 h (key_injective e).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh, hlt⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨σ h, ?_, hσ.1 h⟩)
      rw [hMSdef, Finset.mem_filter, Finset.mem_product] at hh
      rw [hRdef, hMSdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, hσ.1]
      exact ⟨⟨⟨hh.2, Finset.mem_univ _⟩, hh.1.1⟩, hgt⟩
  have hR : S.card + 1 ≤ #R := by
    have h1 : _ ≤ #MS := sum_nbr_le hσ hs S
    have h2 : #MS ≤ #R + #(R.image σ) := (Finset.card_le_card hMS).trans (Finset.card_union_le _ _)
    have h3 : #(R.image σ) = #R := Finset.card_image_of_injective _ σ.injective
    omega
  obtain ⟨T, hTR, hT⟩ := Finset.exists_subset_card_eq hR
  let q : Fin (S.card + 1) → Half n := fun t => (T.equivFin.symm (Fin.cast hT.symm t) : Half n)
  have hqR : ∀ t, q t ∈ R := fun t => hTR (T.equivFin.symm _).2
  have hqkey : ∀ t, key (q t) < key (σ (q t)) := fun t => (Finset.mem_filter.mp (hqR t)).2
  have hqinj : Function.Injective q := fun a b h =>
    Fin.cast_injective _ (T.equivFin.symm.injective (Subtype.ext h))
  -- the pairs `{q t, σ (q t)}` are disjoint
  have hcross : ∀ a b, q a ≠ σ (q b) := fun a b h => by
    have h1 := hqkey b
    have h2 := hqkey a
    rw [h, hσ.1] at h2
    omega
  refine ⟨fun t => (q t, σ (q t)), fun t => ?_, ?_, ?_⟩
  · have := hqR t
    rw [hRdef, hMSdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at this
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product]
    exact ⟨this.1.1, this.1.2, Finset.mem_univ _⟩
  · rw [flat, List.nodup_flatMap]
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hx
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      exact fun h => hσ.2 (q t) h.symm
    · rw [List.pairwise_ofFn]
      intro a b hab x hxa hxb
      have hne : a ≠ b := ne_of_lt hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxa hxb
      rcases hxa with rfl | rfl <;> rcases hxb with h | h
      · exact hne (hqinj h)
      · exact hcross a b h
      · exact hcross b a h.symm
      · exact hne (hqinj (σ.injective h))
  · intro x hx
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hx
    rfl

theorem card_half : Fintype.card (Half n) = 3 * n := by
  simp [Half, mul_comm]

/-- **The first moment.** For `n ≥ 2M + 2`, the fraction of pairings whose graph is simple and
has a set of at most `M` vertices spanning more edges than vertices is at most `K_M / n`. -/
theorem card_bad_le (M : ℕ) (hn : 2 * M + 2 ≤ n) :
    (#((simpleMatchings n).filter fun σ => ¬ Sparse (cgraph σ) M) : ℝ)
      ≤ (∑ s ∈ range (M + 1), ((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1)) * #(matchings (Half n)) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set Mt := #(matchings (Half n))
  let Pf : (s : ℕ) → Finset (Fin n) → Finset (Fin (s + 1) → Half n × Half n) := fun s S =>
    (Fintype.piFinset fun _ => (S ×ˢ (univ : Finset (Fin 3))) ×ˢ (S ×ˢ (univ : Finset (Fin 3)))).filter
      fun p => (flat (List.ofFn p)).Nodup
  set U := (range (M + 1)).biUnion fun s => (powersetCard s univ).biUnion fun S =>
    (Pf s S).biUnion fun p => (matchings (Half n)).filter (Fixes (List.ofFn p))
  -- every bad pairing lies in the union
  have hsub : ((simpleMatchings n).filter fun σ => ¬ Sparse (cgraph σ) M) ⊆ U := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨hsm, hbad⟩ := hσ
    have hsm' := hsm
    simp only [simpleMatchings, matchings, Finset.mem_filter, Finset.mem_univ, true_and] at hsm'
    simp only [Sparse, not_forall, not_le, exists_prop] at hbad
    obtain ⟨S, hSM, hSbig⟩ := hbad
    obtain ⟨p, hpS, hpnd, hpfix⟩ := exists_pairs hsm'.1 hsm'.2 S hSbig
    simp only [U, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    refine ⟨S.card, by omega, S, ⟨Finset.subset_univ _, rfl⟩, p, ?_, ?_⟩
    · simp only [Pf, Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨hpS, hpnd⟩
    · simp only [matchings, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hsm'.1, hpfix⟩
  -- each term: `#{σ ⊇ L} ≤ Mt / (2n)^{s+1}`
  have hterm : ∀ s ∈ range (M + 1), ∀ S ∈ powersetCard s (univ : Finset (Fin n)), ∀ p ∈ Pf s S,
      (#((matchings (Half n)).filter (Fixes (List.ofFn p))) : ℝ) ≤ Mt / (2 * n) ^ (s + 1) := by
    intro s hs S _ p hp
    rw [Finset.mem_range] at hs
    have hnd : (flat (List.ofFn p)).Nodup := (Finset.mem_filter.mp hp).2
    have h := card_fixes_le (List.ofFn p) hnd
    rw [List.length_ofFn, card_half] at h
    have hcast : (2 * n : ℝ) ≤ ((3 * n - 2 * (s + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith [(by exact_mod_cast (by omega : 2 * (s + 1) ≤ n) : (2 * (s + 1) : ℝ) ≤ n)]
    have hpos : (0 : ℝ) < (2 * n) ^ (s + 1) := by positivity
    rw [le_div_iff₀ hpos]
    calc (#((matchings (Half n)).filter (Fixes (List.ofFn p))) : ℝ) * (2 * n) ^ (s + 1)
        ≤ #((matchings (Half n)).filter (Fixes (List.ofFn p))) * ((3 * n - 2 * (s + 1) : ℕ) : ℝ) ^ (s + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcast _) (by positivity)
      _ ≤ Mt := by exact_mod_cast h
  have hPf : ∀ s, ∀ S ∈ powersetCard s (univ : Finset (Fin n)),
      (#(Pf s S) : ℝ) ≤ ((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) := by
    intro s S hS
    rw [Finset.mem_powersetCard] at hS
    have : #(Pf s S) ≤ (9 * s ^ 2) ^ (s + 1) := by
      refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
      rw [Fintype.card_piFinset_const, Finset.card_product, Finset.card_product, Finset.card_univ,
        Fintype.card_fin, hS.2]
      ring
    exact_mod_cast this
  calc (#((simpleMatchings n).filter fun σ => ¬ Sparse (cgraph σ) M) : ℝ)
      ≤ #U := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ s ∈ range (M + 1), ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ∑ p ∈ Pf s S,
          (#((matchings (Half n)).filter (Fixes (List.ofFn p))) : ℝ) := by
        refine (Nat.cast_le.mpr (Finset.card_biUnion_le)).trans ?_
        push_cast
        refine Finset.sum_le_sum fun s _ => ?_
        refine (Nat.cast_le.mpr (Finset.card_biUnion_le)).trans ?_
        push_cast
        refine Finset.sum_le_sum fun S _ => ?_
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ s ∈ range (M + 1), ∑ S ∈ powersetCard s (univ : Finset (Fin n)),
          ((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) * (Mt / (2 * n) ^ (s + 1)) := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun S hS => ?_
        calc ∑ p ∈ Pf s S, (#((matchings (Half n)).filter (Fixes (List.ofFn p))) : ℝ)
            ≤ ∑ _p ∈ Pf s S, (Mt / (2 * n) ^ (s + 1) : ℝ) := Finset.sum_le_sum (hterm s hs S hS)
          _ = #(Pf s S) * (Mt / (2 * n) ^ (s + 1) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hPf s S hS) (by positivity)
    _ ≤ ∑ s ∈ range (M + 1), ((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) * (Mt / n) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hch : ((n.choose s : ℕ) : ℝ) ≤ (n : ℝ) ^ s := by exact_mod_cast Nat.choose_le_pow n s
        have hkey : (n : ℝ) ^ s * (Mt / (2 * n) ^ (s + 1)) ≤ Mt / n := by
          have e : (n : ℝ) ^ s * (Mt / (2 * n) ^ (s + 1)) = Mt / (2 ^ (s + 1) * n) := by
            field_simp; ring
          have h2 : (1 : ℝ) ≤ 2 ^ (s + 1) := one_le_pow₀ (by norm_num)
          rw [e]
          exact div_le_div_of_nonneg_left (by positivity) hn0 (le_mul_of_one_le_left hn0.le h2)
        calc ((n.choose s : ℕ) : ℝ) * (((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) * (Mt / (2 * n) ^ (s + 1)))
            ≤ (n : ℝ) ^ s * (((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) * (Mt / (2 * n) ^ (s + 1))) :=
              mul_le_mul_of_nonneg_right hch (by positivity)
          _ = ((9 * s ^ 2 : ℕ) : ℝ) ^ (s + 1) * ((n : ℝ) ^ s * (Mt / (2 * n) ^ (s + 1))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

end FirstMoment

end Kuramoto.CM
