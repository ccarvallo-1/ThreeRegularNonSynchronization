/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Transplant

/-!
# Lemma 2.2, deterministic part: an `ℓ`-cycle of a sparse `3`-regular graph extends to `Q_{ℓ,R}`

The proof of Lemma 2.2 has two ingredients: `G_{n,3}` has an `ℓ`-cycle with probability
`→ 1 − e^{-λ_ℓ}`, and "each such cycle can be extended to `Q_{ℓ,R}`" because exploring the
ball of radius `R` around it only meets new vertices, except with probability `O(1/n)`.

This file proves the second ingredient *deterministically*: if `G` is `3`-regular, has an
`ℓ`-cycle, and every set `S` of at most `|V(Q_{ℓ,R})| = 2^R ℓ` vertices spans at most `|S|`
edges (`Sparse`), then `G` contains `Q_{ℓ,R}` as an induced subgraph
(`exists_inducedCopy`). That `G_{n,3}` is `Sparse` w.h.p. is `Random.sparse_whp`, proved from
the configuration model.

The argument: grow the copy of `Q_{ℓ,R}` one vertex at a time, cycle first, then each tree
vertex after its parent. A set of vertices of `Q_{ℓ,R}` grown this way spans exactly as many
edges as vertices. If the image of a new vertex collided with an earlier one, or if an extra
edge appeared, the image set would span more edges than vertices, contradicting `Sparse`.
-/

@[expose] public section

namespace Kuramoto

open Finset

/-! ## Sparse graphs -/

section Sparse

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every set of at most `M` vertices spans at most as many edges as vertices. By the
handshake lemma, `2 e(S) = ∑_{x ∈ S} |N(x) ∩ S|`, so this reads `e(S) ≤ |S|`. -/
def Sparse (M : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ M → ∑ x ∈ S, (G.neighborFinset x ∩ S).card ≤ 2 * S.card

/-- `G` contains an `ℓ`-cycle: `ℓ` distinct vertices `c 0, …, c (ℓ-1)` with `c i ~ c (i+1)`. -/
def HasCycle (ℓ : ℕ) : Prop :=
  ∃ c : ZMod ℓ → V, Function.Injective c ∧ ∀ i, G.Adj (c i) (c (i + 1))

end Sparse

/-! ## Growing a copy one vertex at a time -/

section Grow

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable (Q : SimpleGraph W) [DecidableRel Q.Adj] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If `f` maps `P` injectively, `Q[P]` spans `|P|` edges, and `G` is sparse, then `f` loses no
edge and creates none: around each `w ∈ P`, the neighbours of `f w` inside `f(P)` are exactly the
images of the neighbours of `w` inside `P`. -/
theorem nbr_image_eq {f : W → V} (hom : ∀ a b, Q.Adj a b → G.Adj (f a) (f b))
    (hsp : Sparse G (Fintype.card W)) {P : Finset W} (hinj : Set.InjOn f P)
    (hcount : ∑ w ∈ P, (Q.neighborFinset w ∩ P).card = 2 * P.card) :
    ∀ w ∈ P, G.neighborFinset (f w) ∩ P.image f = (Q.neighborFinset w ∩ P).image f := by
  have hsub : ∀ w ∈ P,
      (Q.neighborFinset w ∩ P).image f ⊆ G.neighborFinset (f w) ∩ P.image f := by
    intro w _ y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_inter] at hu ⊢
    exact ⟨(G.mem_neighborFinset _ _).mpr (hom w u ((Q.mem_neighborFinset _ _).mp hu.1)),
      Finset.mem_image_of_mem f hu.2⟩
  have hcardimg : ∀ w ∈ P,
      ((Q.neighborFinset w ∩ P).image f).card = (Q.neighborFinset w ∩ P).card := fun w _ =>
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr Finset.inter_subset_right))
  have hle : ∀ w ∈ P,
      (Q.neighborFinset w ∩ P).card ≤ (G.neighborFinset (f w) ∩ P.image f).card :=
    fun w hw => (hcardimg w hw) ▸ Finset.card_le_card (hsub w hw)
  have himgcard : (P.image f).card = P.card := Finset.card_image_of_injOn hinj
  have hreidx : ∑ x ∈ P.image f, (G.neighborFinset x ∩ P.image f).card
      = ∑ w ∈ P, (G.neighborFinset (f w) ∩ P.image f).card := Finset.sum_image hinj
  have htot : ∑ w ∈ P, (G.neighborFinset (f w) ∩ P.image f).card
      ≤ ∑ w ∈ P, (Q.neighborFinset w ∩ P).card := by
    rw [hcount, ← hreidx, ← himgcard]
    exact hsp _ (himgcard ▸ Finset.card_le_univ P)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) htot)
  intro w hw
  exact (Finset.eq_of_subset_of_card_le (hsub w hw) (by rw [hcardimg w hw, heq w hw])).symm

/-- **Growing the copy.** Let `d` be a depth function on `Q` such that every vertex of positive
depth has exactly one neighbour of smaller depth (its parent) and no neighbour of the same
depth. Let `f : Q → G` be a homomorphism, injective on every neighbourhood, and injective on the
depth-`0` layer `P₀`, which spans `|P₀|` edges. If `G` is sparse, then for every set `P ⊇ P₀`
closed under taking parents, `f` is injective on `P` and `Q[P]` spans `|P|` edges.

By induction on `|P \ P₀|`, removing a vertex `v` of maximal depth: its only neighbour left in
`P` is its parent `p`, and by `nbr_image_eq` at `p`, `f v` cannot be the image of an earlier
vertex. -/
theorem injOn_of_closed {f : W → V} (hom : ∀ a b, Q.Adj a b → G.Adj (f a) (f b))
    (hloc : ∀ w, ∀ u ∈ Q.neighborFinset w, ∀ v ∈ Q.neighborFinset w, f u = f v → u = v)
    (d : W → ℕ)
    (hpar : ∀ w u v, d w ≠ 0 → Q.Adj w u → Q.Adj w v → d u < d w → d v < d w → u = v)
    (hlow : ∀ w, d w ≠ 0 → ∃ u, Q.Adj w u ∧ d u < d w)
    (hsame : ∀ w u, d w ≠ 0 → Q.Adj w u → d u ≠ d w)
    (hsp : Sparse G (Fintype.card W))
    {P₀ : Finset W} (hP₀ : ∀ w, w ∈ P₀ ↔ d w = 0) (hinj₀ : Set.InjOn f P₀)
    (hcount₀ : ∑ w ∈ P₀, (Q.neighborFinset w ∩ P₀).card = 2 * P₀.card) :
    ∀ n (P : Finset W), (P \ P₀).card = n → P₀ ⊆ P →
      (∀ w ∈ P, ∀ u, Q.Adj w u → d u < d w → u ∈ P) →
      Set.InjOn f P ∧ ∑ w ∈ P, (Q.neighborFinset w ∩ P).card = 2 * P.card := by
  intro n
  induction n with
  | zero =>
    intro P hn h0 _
    have hP : P = P₀ := by
      refine le_antisymm (fun x hx => ?_) h0
      by_contra hx0
      have hmem : x ∈ P \ P₀ := Finset.mem_sdiff.mpr ⟨hx, hx0⟩
      rw [Finset.card_eq_zero.mp hn] at hmem
      exact Finset.notMem_empty x hmem
    subst hP
    exact ⟨hinj₀, hcount₀⟩
  | succ n ih =>
    intro P hn h0 hcl
    have hne : (P \ P₀).Nonempty := by rw [← Finset.card_pos, hn]; omega
    obtain ⟨v, hvmem, hvmax⟩ := Finset.exists_max_image (P \ P₀) d hne
    obtain ⟨hvP, hvP₀⟩ := Finset.mem_sdiff.mp hvmem
    have hdv : d v ≠ 0 := fun h => hvP₀ ((hP₀ v).mpr h)
    -- no vertex of `P` is deeper than `v`
    have habove : ∀ u ∈ P, d v < d u → False := fun u hu hlt => by
      have hu₀ : u ∉ P₀ := fun h => by rw [hP₀] at h; omega
      have := hvmax u (Finset.mem_sdiff.mpr ⟨hu, hu₀⟩)
      omega
    set P' := P.erase v with hP'
    have hvnot : v ∉ P' := Finset.notMem_erase v P
    have hP'card : (P' \ P₀).card = n := by
      have : P' \ P₀ = (P \ P₀).erase v := by
        ext x; simp only [hP', Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem hvmem, hn, Nat.add_sub_cancel]
    have h0' : P₀ ⊆ P' := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hvP₀ (h ▸ hx), h0 hx⟩
    have hcl' : ∀ w ∈ P', ∀ u, Q.Adj w u → d u < d w → u ∈ P' := by
      intro w hw u hwu hlt
      obtain ⟨_, hwP⟩ := Finset.mem_erase.mp hw
      refine Finset.mem_erase.mpr ⟨?_, hcl w hwP u hwu hlt⟩
      rintro rfl
      exact habove w hwP hlt
    obtain ⟨hinj', hcount'⟩ := ih P' hP'card h0' hcl'
    -- the parent `p` of `v` is the only neighbour of `v` in `P'`
    obtain ⟨p, hvp, hpv⟩ := hlow v hdv
    have hpP' : p ∈ P' := Finset.mem_erase.mpr ⟨(Q.ne_of_adj hvp).symm, hcl v hvP p hvp hpv⟩
    have hnbr : Q.neighborFinset v ∩ P' = {p} := by
      ext u
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨hvu, huP'⟩
        rcases lt_or_ge (d u) (d v) with h | h
        · exact hpar v u p hdv hvu hvp h hpv
        · exact (habove u (Finset.mem_of_mem_erase huP')
            (lt_of_le_of_ne h (hsame v u hdv hvu).symm)).elim
      · rintro rfl; exact ⟨hvp, hpP'⟩
    -- `f v` is not the image of an earlier vertex
    have htight := nbr_image_eq Q G hom hsp hinj' hcount' p hpP'
    have hfv : f v ∉ P'.image f := by
      intro hmem
      have hin : f v ∈ G.neighborFinset (f p) ∩ P'.image f :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hom p v hvp.symm), hmem⟩
      rw [htight] at hin
      obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hin
      obtain ⟨hqp, hqP'⟩ := Finset.mem_inter.mp hq
      have hqv' := hloc p q hqp v ((Q.mem_neighborFinset _ _).mpr hvp.symm) hqv
      exact hvnot (hqv' ▸ hqP')
    have hPins : P = insert v P' := (Finset.insert_erase hvP).symm
    refine ⟨?_, ?_⟩
    · rw [hPins, Finset.coe_insert]
      refine (Set.injOn_insert (by simpa using hvnot)).mpr ⟨hinj', ?_⟩
      rintro ⟨u, hu, hfu⟩
      exact hfv (Finset.mem_image.mpr ⟨u, hu, hfu⟩)
    · -- adding `v` adds exactly one edge, `vp`
      rw [hPins, Finset.sum_insert hvnot, Finset.card_insert_of_notMem hvnot]
      have h1 : (Q.neighborFinset v ∩ insert v P').card = 1 := by
        rw [Finset.inter_insert_of_notMem (by simp), hnbr, Finset.card_singleton]
      have h2 : ∀ w ∈ P', (Q.neighborFinset w ∩ insert v P').card
          = (Q.neighborFinset w ∩ P').card + if Q.Adj w v then 1 else 0 := by
        intro w _
        by_cases hwv : Q.Adj w v
        · rw [Finset.inter_insert_of_mem ((Q.mem_neighborFinset _ _).mpr hwv),
            Finset.card_insert_of_notMem (fun h => hvnot (Finset.mem_inter.mp h).2), ite_eq_left hwv]
        · rw [Finset.inter_insert_of_notMem (fun h => hwv ((Q.mem_neighborFinset _ _).mp h)),
            ite_eq_right hwv, add_zero]
      have h3 : (P'.filter (fun w => Q.Adj w v)).card = 1 := by
        rw [← Finset.card_singleton p, ← hnbr]
        congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        rw [SimpleGraph.adj_comm]
        tauto
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, hcount', h1, ← Finset.card_filter, h3]
      ring

/-- Conclusion of the growth argument with `P` = everything: `f` is injective and induced. -/
theorem induced_of_grow {f : W → V} (hom : ∀ a b, Q.Adj a b → G.Adj (f a) (f b))
    (hloc : ∀ w, ∀ u ∈ Q.neighborFinset w, ∀ v ∈ Q.neighborFinset w, f u = f v → u = v)
    (d : W → ℕ)
    (hpar : ∀ w u v, d w ≠ 0 → Q.Adj w u → Q.Adj w v → d u < d w → d v < d w → u = v)
    (hlow : ∀ w, d w ≠ 0 → ∃ u, Q.Adj w u ∧ d u < d w)
    (hsame : ∀ w u, d w ≠ 0 → Q.Adj w u → d u ≠ d w)
    (hsp : Sparse G (Fintype.card W))
    {P₀ : Finset W} (hP₀ : ∀ w, w ∈ P₀ ↔ d w = 0) (hinj₀ : Set.InjOn f P₀)
    (hcount₀ : ∑ w ∈ P₀, (Q.neighborFinset w ∩ P₀).card = 2 * P₀.card) :
    Function.Injective f ∧ ∀ a b, G.Adj (f a) (f b) ↔ Q.Adj a b := by
  obtain ⟨hinj, hcount⟩ := injOn_of_closed Q G hom hloc d hpar hlow hsame hsp hP₀ hinj₀ hcount₀
    _ Finset.univ rfl (Finset.subset_univ _) (fun _ _ u _ _ => Finset.mem_univ u)
  have hinj' : Function.Injective f := fun a b h => hinj (by simp) (by simp) h
  refine ⟨hinj', fun a b => ⟨fun h => ?_, hom a b⟩⟩
  have htight := nbr_image_eq Q G hom hsp hinj hcount a (Finset.mem_univ a)
  have hmem : f b ∈ G.neighborFinset (f a) ∩ Finset.univ.image f :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, Finset.mem_image_of_mem f (by simp)⟩
  rw [htight] at hmem
  obtain ⟨q, hq, hqb⟩ := Finset.mem_image.mp hmem
  rw [← hinj' hqb]
  exact (Q.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hq).1

end Grow

/-! ## The layers of `Q_{ℓ,R}` -/

section Layers

open Gadget

variable {ℓ R : ℕ}

theorem depth_parent (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    Vtx.depth ℓ R (parent ℓ R i k b) = k := by
  by_cases hk : (k : ℕ) = 0
  · rw [parent_of_zero ℓ R hk, hk]; rfl
  · obtain ⟨k', b', hpar, hkk, _⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk
    rw [hpar]
    show (k' : ℕ) + 1 = k
    omega

theorem adj_parent (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    (Q ℓ R).Adj (Vtx.brn i k b) (parent ℓ R i k b) := by
  by_cases hk : (k : ℕ) = 0
  · rw [parent_of_zero ℓ R hk, adj_brn_cyc]
    refine ⟨rfl, hk, ?_⟩
    have := b.isLt
    have h1 : (2 : ℕ) ^ (k : ℕ) = 1 := by rw [hk]; norm_num
    omega
  · obtain ⟨k', b', hpar, hkk, hbb⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk
    rw [hpar, adj_brn_brn]
    refine ⟨fun h => ?_, Or.inr ⟨rfl, hkk, hbb⟩⟩
    obtain ⟨_, h2, _⟩ := (brn_eq_brn_iff ℓ R).mp h
    omega

/-- A neighbour of a branch vertex at depth `k + 1` is its parent (depth `k`) or one of its
children (depth `k + 2`). -/
theorem adj_brn_cases (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) (u : Vtx ℓ R)
    (h : (Q ℓ R).Adj (Vtx.brn i k b) u) :
    u = parent ℓ R i k b ∨ Vtx.depth ℓ R u = (k : ℕ) + 2 := by
  cases u with
  | cyc j =>
    rw [adj_brn_cyc] at h
    obtain ⟨hj, hk0, _⟩ := h
    left
    rw [parent_of_zero ℓ R hk0, hj]
  | brn j k' b' =>
    rw [adj_brn_brn] at h
    obtain ⟨_, (⟨_, hkk, _⟩ | ⟨hi, hkk, hbb⟩)⟩ := h
    · right
      show (k' : ℕ) + 1 = k + 2
      omega
    · left
      have hk0 : (k : ℕ) ≠ 0 := by omega
      obtain ⟨kp, bp, hpar, hkp, hbp⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
      rw [hpar]
      exact (brn_eq_brn_iff ℓ R).mpr ⟨hi, by omega, by omega⟩

theorem depth_brn (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    Vtx.depth ℓ R (Vtx.brn i k b) = (k : ℕ) + 1 := rfl

theorem layer_par (w u v : Vtx ℓ R) (hw : Vtx.depth ℓ R w ≠ 0)
    (hu : (Q ℓ R).Adj w u) (hv : (Q ℓ R).Adj w v)
    (hdu : Vtx.depth ℓ R u < Vtx.depth ℓ R w) (hdv : Vtx.depth ℓ R v < Vtx.depth ℓ R w) :
    u = v := by
  cases w with
  | cyc i => exact absurd rfl hw
  | brn i k b =>
    rw [depth_brn] at hdu hdv
    rcases adj_brn_cases i k b u hu with rfl | h
    · rcases adj_brn_cases i k b v hv with rfl | h'
      · rfl
      · omega
    · omega

theorem layer_low (w : Vtx ℓ R) (hw : Vtx.depth ℓ R w ≠ 0) :
    ∃ u, (Q ℓ R).Adj w u ∧ Vtx.depth ℓ R u < Vtx.depth ℓ R w := by
  cases w with
  | cyc i => exact absurd rfl hw
  | brn i k b =>
    refine ⟨_, adj_parent i k b, ?_⟩
    rw [depth_parent, depth_brn]
    omega

theorem layer_same (w u : Vtx ℓ R) (hw : Vtx.depth ℓ R w ≠ 0) (hu : (Q ℓ R).Adj w u) :
    Vtx.depth ℓ R u ≠ Vtx.depth ℓ R w := by
  cases w with
  | cyc i => exact absurd rfl hw
  | brn i k b =>
    rw [depth_brn]
    rcases adj_brn_cases i k b u hu with rfl | h
    · rw [depth_parent]; omega
    · omega

/-- The depth-`0` layer is the `ℓ`-cycle: each cycle vertex has two neighbours in it. -/
theorem cycle_layer_count [NeZero ℓ] (hℓ : 3 ≤ ℓ) (hR : 0 < R) :
    ∑ w ∈ Finset.univ.filter (fun w : Vtx ℓ R => Vtx.depth ℓ R w = 0),
      ((Q ℓ R).neighborFinset w ∩ Finset.univ.filter (fun w => Vtx.depth ℓ R w = 0)).card
      = 2 * (Finset.univ.filter (fun w : Vtx ℓ R => Vtx.depth ℓ R w = 0)).card := by
  rw [Finset.sum_const_nat (m := 2), mul_comm]
  intro w hw
  cases w with
  | brn i k b => exact absurd (Finset.mem_filter.mp hw).2 (by rw [depth_brn]; omega)
  | cyc i =>
    have hne : (Vtx.cyc (i + 1) : Vtx ℓ R) ≠ Vtx.cyc (i - 1) := by
      intro h
      injection h with h
      exact two_ne_zero_zmod ℓ hℓ (by linear_combination h)
    have : (Q ℓ R).neighborFinset (Vtx.cyc i)
        ∩ Finset.univ.filter (fun w => Vtx.depth ℓ R w = 0) = {Vtx.cyc (i + 1), Vtx.cyc (i - 1)} := by
      rw [neighborFinset_cyc ℓ R hℓ hR i]
      ext u
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h | h | h, hd⟩
        · exact Or.inl h
        · exact Or.inr h
        · rw [h, depth_brn] at hd; omega
      · rintro (h | h) <;> rw [h] <;> exact ⟨by tauto, rfl⟩
    rw [this, Finset.card_pair hne]

end Layers

/-- Three points with distinct images. -/
theorem injOn_triple {α β : Type*} [DecidableEq α] (f : α → β) {x y z : α}
    (hxy : f x ≠ f y) (hxz : f x ≠ f z) (hyz : f y ≠ f z) :
    ∀ u ∈ ({x, y, z} : Finset α), ∀ v ∈ ({x, y, z} : Finset α), f u = f v → u = v := by
  intro u hu v hv h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | rfl | exact absurd h ‹_› | exact absurd h.symm ‹_›

/-! ## The embedding -/

section Embed

open Gadget

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {ℓ R : ℕ}

/-- An element of `s`, or `x` if `s` is empty. -/
noncomputable def pick (s : Finset V) (x : V) : V := if h : s.Nonempty then h.choose else x

omit [Fintype V] [DecidableEq V] in
theorem pick_mem {s : Finset V} (x : V) (h : s.Nonempty) : pick s x ∈ s := by
  rw [pick, dite_eq_left h]; exact h.choose_spec

/-- The two neighbours of `x` other than `p`. -/
noncomputable def child0 (x p : V) : V := pick ((G.neighborFinset x).erase p) x

noncomputable def child1 (x p : V) : V :=
  pick (((G.neighborFinset x).erase p).erase (child0 G x p)) x

theorem child_spec (hreg : ∀ v, G.degree v = 3) {x p : V} (hp : G.Adj x p) :
    G.Adj x (child0 G x p) ∧ G.Adj x (child1 G x p) ∧ child0 G x p ≠ p ∧ child1 G x p ≠ p ∧
      child1 G x p ≠ child0 G x p := by
  have hc : ((G.neighborFinset x).erase p).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hp),
      G.card_neighborFinset_eq_degree, hreg]
  have h0 : child0 G x p ∈ (G.neighborFinset x).erase p :=
    pick_mem _ (by rw [← Finset.card_pos, hc]; norm_num)
  have h1 : child1 G x p ∈ ((G.neighborFinset x).erase p).erase (child0 G x p) :=
    pick_mem _ (by rw [← Finset.card_pos, Finset.card_erase_of_mem h0, hc]; norm_num)
  obtain ⟨h0p, h0n⟩ := Finset.mem_erase.mp h0
  obtain ⟨h10, h1'⟩ := Finset.mem_erase.mp h1
  obtain ⟨h1p, h1n⟩ := Finset.mem_erase.mp h1'
  exact ⟨(G.mem_neighborFinset _ _).mp h0n, (G.mem_neighborFinset _ _).mp h1n, h0p, h1p, h10⟩

/-- The neighbour of the cycle vertex `c i` off the cycle. -/
noncomputable def pendant (c : ZMod ℓ → V) (i : ZMod ℓ) : V :=
  pick (((G.neighborFinset (c i)).erase (c (i + 1))).erase (c (i - 1))) (c i)

theorem pendant_spec (hreg : ∀ v, G.degree v = 3) [NeZero ℓ] (hℓ : 3 ≤ ℓ) {c : ZMod ℓ → V}
    (hinj : Function.Injective c) (hadj : ∀ i, G.Adj (c i) (c (i + 1))) (i : ZMod ℓ) :
    G.Adj (c i) (pendant G c i) ∧ pendant G c i ≠ c (i + 1) ∧ pendant G c i ≠ c (i - 1) := by
  have hne : c (i - 1) ≠ c (i + 1) := fun h =>
    two_ne_zero_zmod ℓ hℓ (by linear_combination -(hinj h))
  have hprev : G.Adj (c i) (c (i - 1)) := by
    have := hadj (i - 1); rw [sub_add_cancel] at this; exact this.symm
  have hc : ((G.neighborFinset (c i)).erase (c (i + 1))).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr (hadj i)),
      G.card_neighborFinset_eq_degree, hreg]
  have hmem : c (i - 1) ∈ (G.neighborFinset (c i)).erase (c (i + 1)) :=
    Finset.mem_erase.mpr ⟨hne, (G.mem_neighborFinset _ _).mpr hprev⟩
  have h := pick_mem (c i) (s := ((G.neighborFinset (c i)).erase (c (i + 1))).erase (c (i - 1)))
    (by rw [← Finset.card_pos, Finset.card_erase_of_mem hmem, hc]; norm_num)
  obtain ⟨h1, h'⟩ := Finset.mem_erase.mp h
  obtain ⟨h2, h3⟩ := Finset.mem_erase.mp h'
  exact ⟨(G.mem_neighborFinset _ _).mp h3, h2, h1⟩

/-- The tree hanging from `c i`: `treeMap i k b` is the image of `brn i k b` together with the
image of its parent. Vertex `b` at depth `k + 2` is child number `b % 2` of vertex `b / 2` at
depth `k + 1`, matching `childL`/`childR`. -/
noncomputable def treeMap (c : ZMod ℓ → V) (i : ZMod ℓ) : ℕ → ℕ → V × V
  | 0, _ => (pendant G c i, c i)
  | k + 1, b =>
    ((if b % 2 = 0 then child0 G (treeMap c i k (b / 2)).1 (treeMap c i k (b / 2)).2
      else child1 G (treeMap c i k (b / 2)).1 (treeMap c i k (b / 2)).2),
     (treeMap c i k (b / 2)).1)

/-- The candidate copy of `Q_{ℓ,R}`. -/
noncomputable def embed (c : ZMod ℓ → V) : Vtx ℓ R → V
  | .cyc i => c i
  | .brn i k b => (treeMap G c i k b).1

variable (hreg : ∀ v, G.degree v = 3) [NeZero ℓ] (hℓ : 3 ≤ ℓ) {c : ZMod ℓ → V}
  (hinj : Function.Injective c) (hadj : ∀ i, G.Adj (c i) (c (i + 1)))
include hreg hℓ hinj hadj

theorem treeMap_adj (i : ZMod ℓ) (k b : ℕ) : G.Adj (treeMap G c i k b).1 (treeMap G c i k b).2 := by
  induction k generalizing b with
  | zero => exact (pendant_spec G hreg hℓ hinj hadj i).1.symm
  | succ k ih =>
    have hs := child_spec G hreg (ih (b / 2))
    simp only [treeMap]
    split_ifs
    · exact hs.1.symm
    · exact hs.2.1.symm

omit hreg [NeZero ℓ] hℓ hinj hadj in
theorem embed_parent (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    embed G c (parent ℓ R i k b) = (treeMap G c i k b).2 := by
  by_cases hk : (k : ℕ) = 0
  · rw [parent_of_zero ℓ R hk]
    show c i = (treeMap G c i k b).2
    generalize (b : ℕ) = b'
    rw [hk]; rfl
  · rw [parent, dite_eq_right hk]
    show (treeMap G c i ((k : ℕ) - 1) ((b : ℕ) / 2)).1 = (treeMap G c i k b).2
    obtain ⟨m, hm⟩ : ∃ m, (k : ℕ) = m + 1 := ⟨(k : ℕ) - 1, by omega⟩
    generalize (b : ℕ) = b'
    rw [hm, Nat.add_sub_cancel]
    rfl

omit hreg [NeZero ℓ] hℓ hinj hadj in
theorem embed_childL (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) (hk : (k : ℕ) + 1 < R) :
    embed G c (childL ℓ R i k b hk)
      = child0 G (treeMap G c i k b).1 (treeMap G c i k b).2 := by
  rw [childL]
  show (treeMap G c i ((k : ℕ) + 1) (2 * (b : ℕ))).1 = _
  have e1 : 2 * (b : ℕ) / 2 = b := by omega
  have e2 : 2 * (b : ℕ) % 2 = 0 := by omega
  simp only [treeMap, e1, e2, ite_true]

omit hreg [NeZero ℓ] hℓ hinj hadj in
theorem embed_childR (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) (hk : (k : ℕ) + 1 < R) :
    embed G c (childR ℓ R i k b hk)
      = child1 G (treeMap G c i k b).1 (treeMap G c i k b).2 := by
  rw [childR]
  show (treeMap G c i ((k : ℕ) + 1) (2 * (b : ℕ) + 1)).1 = _
  have e1 : (2 * (b : ℕ) + 1) / 2 = b := by omega
  have e2 : (2 * (b : ℕ) + 1) % 2 = 1 := by omega
  simp only [treeMap, e1, e2, one_ne_zero, ite_false]

theorem embed_adj (hR : 0 < R) (w : Vtx ℓ R) :
    ∀ u ∈ (Q ℓ R).neighborFinset w, G.Adj (embed G c w) (embed G c u) := by
  cases w with
  | cyc i =>
    rw [neighborFinset_cyc ℓ R hℓ hR i]
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hadj i
    · have := hadj (i - 1); rw [sub_add_cancel] at this; exact this.symm
    · exact (pendant_spec G hreg hℓ hinj hadj i).1
  | brn i k b =>
    have hp := treeMap_adj G hreg hℓ hinj hadj i k b
    have hs := child_spec G hreg hp
    by_cases hk : (k : ℕ) + 1 < R
    · rw [neighborFinset_brn ℓ R i k b hk]
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · rw [embed_parent G]; exact hp
      · rw [embed_childL G]; exact hs.1
      · rw [embed_childR G]; exact hs.2.1
    · rw [neighborFinset_brn_leaf ℓ R i k b (by have := k.isLt; omega)]
      intro u hu
      rw [Finset.mem_singleton.mp hu, embed_parent G]
      exact hp

theorem embed_loc (hR : 0 < R) (w : Vtx ℓ R) :
    ∀ u ∈ (Q ℓ R).neighborFinset w, ∀ v ∈ (Q ℓ R).neighborFinset w,
      embed G c u = embed G c v → u = v := by
  cases w with
  | cyc i =>
    obtain ⟨_, hp1, hp2⟩ := pendant_spec G hreg hℓ hinj hadj i
    have hne : c (i + 1) ≠ c (i - 1) := fun h =>
      two_ne_zero_zmod ℓ hℓ (by linear_combination hinj h)
    rw [neighborFinset_cyc ℓ R hℓ hR i]
    exact injOn_triple (embed G c) hne (Ne.symm hp1) (Ne.symm hp2)
  | brn i k b =>
    have hs := child_spec G hreg (treeMap_adj G hreg hℓ hinj hadj i k b)
    by_cases hk : (k : ℕ) + 1 < R
    · rw [neighborFinset_brn ℓ R i k b hk]
      refine injOn_triple (embed G c) ?_ ?_ ?_
      · rw [embed_parent G, embed_childL G]
        exact Ne.symm hs.2.2.1
      · rw [embed_parent G, embed_childR G]
        exact Ne.symm hs.2.2.2.1
      · rw [embed_childL G, embed_childR G]
        exact Ne.symm hs.2.2.2.2
    · rw [neighborFinset_brn_leaf ℓ R i k b (by have := k.isLt; omega)]
      intro u hu v hv _
      rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]

end Embed

/-! ## The extension lemma -/

open Gadget in
/-- **The cycle extends to an induced `Q_{ℓ,R}`.** If `G` is `3`-regular, has an `ℓ`-cycle,
and every set of at most `2^R ℓ = |V(Q_{ℓ,R})|` vertices spans at most as many edges as
vertices, then `G` contains `Q_{ℓ,R}` as an induced subgraph. -/
theorem exists_inducedCopy {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hreg : ∀ v, G.degree v = 3) {ℓ R : ℕ} [NeZero ℓ] (hℓ : 3 ≤ ℓ)
    (hR : 0 < R) (hcyc : HasCycle G ℓ) (hsp : Sparse G (2 ^ R * ℓ)) :
    ∃ f : Vtx ℓ R → V, IsInducedCopy G ℓ R f := by
  obtain ⟨c, hinj, hadj⟩ := hcyc
  set P₀ := Finset.univ.filter (fun w : Vtx ℓ R => Vtx.depth ℓ R w = 0) with hP₀def
  have hP₀ : ∀ w, w ∈ P₀ ↔ Vtx.depth ℓ R w = 0 := fun w => by simp [hP₀def]
  have hinj₀ : Set.InjOn (embed G (R := R) c) P₀ := by
    intro u hu v hv h
    rw [Finset.mem_coe, hP₀] at hu hv
    cases u with
    | brn _ k _ => exact absurd hu (by rw [depth_brn]; omega)
    | cyc i =>
      cases v with
      | brn _ k _ => exact absurd hv (by rw [depth_brn]; omega)
      | cyc j => exact congrArg Vtx.cyc (hinj h)
  have hsp' : Sparse G (Fintype.card (Vtx ℓ R)) := by rwa [Vtx.card_vtx]
  obtain ⟨hf, hiff⟩ := induced_of_grow (Q ℓ R) G
    (fun a b h => embed_adj G hreg hℓ hinj hadj hR a b ((SimpleGraph.mem_neighborFinset _ _ _).mpr h))
    (embed_loc G hreg hℓ hinj hadj hR) (Vtx.depth ℓ R) layer_par layer_low layer_same hsp'
    hP₀ hinj₀ (cycle_layer_count hℓ hR)
  exact ⟨embed G c, ⟨hf, hiff⟩⟩

end Kuramoto
