/-
Copyright (c) 2026 Ciro Carvallo, Pablo Groisman, Dieter Mitsche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ciro Carvallo, Pablo Groisman, Dieter Mitsche
-/
module

public import Kuramoto.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 2: the ℓ-cycle gadget

Paper cross-reference:
  * §2, `Q_{ℓ,R}`    -> `Kuramoto.Gadget.Vtx`, `Kuramoto.Gadget.Q`
  * eq. (4)          -> `Kuramoto.Gadget.Δ`
  * eq. (5)–(6)      -> `Kuramoto.Gadget.phase`, `Kuramoto.Gadget.absDelta_branch`
  * Proposition 2.1  -> (i) `grad_eq_zero_of_nonleaf` (in `Q_{ℓ,R}`; in a `3`-regular `G`
                        containing it induced: `grad_transplant_eq_zero_of_induced`);
                        (ii) `phase_diff_near`,
                        `absDelta_branch`; (iii) `exists_unique_root`, `root`, `δ₀`,
                        `etabounds` (eq. `eq:etabounds`, from `root_le` and `root_gt`)
-/

@[expose] public section

namespace Kuramoto.Gadget

open Finset Real

variable (ℓ R : ℕ)

/-! ## The graph `Q_{ℓ,R}` -/

/-- Vertices of `Q_{ℓ,R}`: the `ℓ` cycle vertices, and for each cycle vertex `i` a full binary
tree, where `brn i k b` is the `b`-th vertex at depth `k + 1`.

Depth `k + 1` carries `2 ^ k` vertices, so each branch has `∑_{k<R} 2^k = 2^R - 1` vertices and
`|V| = ℓ + ℓ (2^R - 1) = 2^R ℓ`, matching §2. -/
inductive Vtx (ℓ R : ℕ)
  | cyc : ZMod ℓ → Vtx ℓ R
  | brn : ZMod ℓ → (k : Fin R) → Fin (2 ^ (k : ℕ)) → Vtx ℓ R
  deriving DecidableEq

namespace Vtx

/-- Distance from the cycle. -/
def depth : Vtx ℓ R → ℕ
  | .cyc _ => 0
  | .brn _ k _ => (k : ℕ) + 1

/-- Leaves are the vertices at depth `R`; these are the ones left unconstrained by the
equilibrium equations and clamped to phase `0` in Section 3. -/
def IsLeaf : Vtx ℓ R → Prop
  | .cyc _ => R = 0
  | .brn _ k _ => (k : ℕ) + 1 = R

/-- `Vtx ℓ R` is the cycle together with, for each cycle vertex, the levels of its binary tree:
level `k` has `2 ^ k` vertices. Making this explicit gives the `Fintype` instance. -/
def vtxEquiv : Vtx ℓ R ≃ ZMod ℓ ⊕ (ZMod ℓ × Σ k : Fin R, Fin (2 ^ (k : ℕ))) where
  toFun
    | .cyc i => Sum.inl i
    | .brn i k b => Sum.inr (i, ⟨k, b⟩)
  invFun
    | Sum.inl i => .cyc i
    | Sum.inr (i, ⟨k, b⟩) => .brn i k b
  left_inv := by rintro (i | ⟨i, k, b⟩) <;> rfl
  right_inv := by rintro (i | ⟨i, ⟨k, b⟩⟩) <;> rfl

instance [NeZero ℓ] : Fintype (Vtx ℓ R) := Fintype.ofEquiv _ (vtxEquiv ℓ R).symm

/-- `|V(Q_{ℓ,R})| = 2^R ℓ`, the count in §2. -/
theorem card_vtx [NeZero ℓ] : Fintype.card (Vtx ℓ R) = 2 ^ R * ℓ := by
  rw [Fintype.card_congr (vtxEquiv ℓ R)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, ZMod.card,
    Fintype.card_fin]
  have hgeom : ∑ k : Fin R, 2 ^ (k : ℕ) = 2 ^ R - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ k) R]
    simpa using Nat.geomSum_eq (le_refl 2) R
  rw [hgeom]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ R = m + 1 :=
    ⟨2 ^ R - 1, by have := Nat.one_le_two_pow (n := R); omega⟩
  rw [hm, Nat.add_sub_cancel]
  ring

end Vtx

/-- Adjacency, before symmetrization: consecutive cycle vertices, the pendant edge from each
cycle vertex to the root of its tree, and the two children of each branch vertex. -/
def rel : Vtx ℓ R → Vtx ℓ R → Prop
  | .cyc i, .cyc j => j = i + 1
  | .cyc i, .brn i' k b => i = i' ∧ (k : ℕ) = 0 ∧ (b : ℕ) = 0
  | .brn i k b, .brn i' k' b' =>
      i = i' ∧ (k' : ℕ) = (k : ℕ) + 1 ∧ ((b' : ℕ) = 2 * b ∨ (b' : ℕ) = 2 * b + 1)
  | _, _ => False

/-- The gadget `Q_{ℓ,R}` of §2. -/
def Q : SimpleGraph (Vtx ℓ R) := SimpleGraph.fromRel (rel ℓ R)

open scoped Classical in
noncomputable instance : DecidableRel (Q ℓ R).Adj := Classical.decRel _

/-! ### Adjacency in `Q_{ℓ,R}`

`Q` is built with `SimpleGraph.fromRel`, so its adjacency is `u ≠ v ∧ (rel u v ∨ rel v u)`.
These lemmas unfold that into usable form, one per pair of constructors. -/

theorem adj_iff (u v : Vtx ℓ R) :
    (Q ℓ R).Adj u v ↔ u ≠ v ∧ (rel ℓ R u v ∨ rel ℓ R v u) := Iff.rfl

theorem adj_cyc_cyc (i j : ZMod ℓ) :
    (Q ℓ R).Adj (.cyc i) (.cyc j) ↔ i ≠ j ∧ (j = i + 1 ∨ i = j + 1) := by
  rw [adj_iff]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun hij => hne (by rw [hij]), h⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun hij => hne (by injection hij), h⟩

theorem adj_cyc_brn (i i' : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    (Q ℓ R).Adj (.cyc i) (.brn i' k b) ↔ i = i' ∧ (k : ℕ) = 0 ∧ (b : ℕ) = 0 := by
  rw [adj_iff]
  simp only [rel, ne_eq, reduceCtorEq, not_false_eq_true, true_and, or_false]

theorem adj_brn_cyc (i i' : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    (Q ℓ R).Adj (.brn i' k b) (.cyc i) ↔ i = i' ∧ (k : ℕ) = 0 ∧ (b : ℕ) = 0 := by
  rw [SimpleGraph.adj_comm]; exact adj_cyc_brn ℓ R i i' k b

theorem adj_brn_brn (i i' : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (k' : Fin R) (b' : Fin (2 ^ (k' : ℕ))) :
    (Q ℓ R).Adj (.brn i k b) (.brn i' k' b') ↔
      Vtx.brn i k b ≠ Vtx.brn i' k' b' ∧
        ((i = i' ∧ (k' : ℕ) = (k : ℕ) + 1 ∧ ((b' : ℕ) = 2 * b ∨ (b' : ℕ) = 2 * b + 1)) ∨
         (i' = i ∧ (k : ℕ) = (k' : ℕ) + 1 ∧ ((b : ℕ) = 2 * b' ∨ (b : ℕ) = 2 * b' + 1))) :=
  Iff.rfl

/-- Equality of branch vertices, reduced to numeric equalities. Without this every comparison
of two `brn` values drags a `HEq` along, because `b : Fin (2 ^ k)` depends on `k`. -/
theorem brn_eq_brn_iff {i i' : ZMod ℓ} {k k' : Fin R}
    {b : Fin (2 ^ (k : ℕ))} {b' : Fin (2 ^ (k' : ℕ))} :
    Vtx.brn i k b = Vtx.brn i' k' b' ↔ i = i' ∧ (k : ℕ) = (k' : ℕ) ∧ (b : ℕ) = (b' : ℕ) := by
  constructor
  · intro h
    injection h with h1 h2 h3
    subst h1
    subst h2
    exact ⟨rfl, rfl, congrArg Fin.val (eq_of_heq h3)⟩
  · rintro ⟨h1, h2, h3⟩
    subst h1
    have hk : k = k' := Fin.ext h2
    subst hk
    rw [Fin.ext h3]

/-- In `ZMod ℓ` with `ℓ ≥ 2`, a vertex is distinct from both of its cycle neighbours. -/
theorem cyc_ne_succ (hℓ : 2 ≤ ℓ) (i : ZMod ℓ) : i ≠ i + 1 ∧ i ≠ i - 1 := by
  have : Fact (1 < ℓ) := ⟨by omega⟩
  have hone : (1 : ZMod ℓ) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_one, ZMod.val_zero] at hv
    exact one_ne_zero hv
  refine ⟨fun h => hone ?_, fun h => hone ?_⟩
  · linear_combination -h
  · linear_combination h

/-! ### Parent and children of a branch vertex -/

/-- The parent of the branch vertex `brn i k b`: the cycle vertex `i` when `k = 0`, and
`brn i (k-1) (b/2)` otherwise. -/
def parent (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) : Vtx ℓ R :=
  if h : (k : ℕ) = 0 then Vtx.cyc i
  else
    Vtx.brn i ⟨(k : ℕ) - 1, by omega⟩
      ⟨(b : ℕ) / 2, by
        show (b : ℕ) / 2 < 2 ^ ((k : ℕ) - 1)
        have hb := b.isLt
        have h2 : 2 ^ (k : ℕ) = 2 ^ ((k : ℕ) - 1) * 2 := by
          rw [← pow_succ]; congr 1; omega
        omega⟩

/-- The left child `brn i (k+1) (2b)`. -/
def childL (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) (hk : (k : ℕ) + 1 < R) : Vtx ℓ R :=
  Vtx.brn i ⟨(k : ℕ) + 1, hk⟩
    ⟨2 * (b : ℕ), by have hb := b.isLt; show 2 * (b : ℕ) < 2 ^ ((k : ℕ) + 1); rw [pow_succ]; omega⟩

/-- The right child `brn i (k+1) (2b+1)`. -/
def childR (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) (hk : (k : ℕ) + 1 < R) : Vtx ℓ R :=
  Vtx.brn i ⟨(k : ℕ) + 1, hk⟩
    ⟨2 * (b : ℕ) + 1, by
      have hb := b.isLt; show 2 * (b : ℕ) + 1 < 2 ^ ((k : ℕ) + 1); rw [pow_succ]; omega⟩

theorem parent_of_zero {i : ZMod ℓ} {k : Fin R} {b : Fin (2 ^ (k : ℕ))} (h : (k : ℕ) = 0) :
    parent ℓ R i k b = Vtx.cyc i := by
  rw [parent, dite_eq_left h]

theorem parent_of_pos {i : ZMod ℓ} {k : Fin R} {b : Fin (2 ^ (k : ℕ))} (h : (k : ℕ) ≠ 0) :
    ∃ (k' : Fin R) (b' : Fin (2 ^ (k' : ℕ))),
      parent ℓ R i k b = Vtx.brn i k' b' ∧ (k : ℕ) = (k' : ℕ) + 1 ∧
        ((b : ℕ) = 2 * (b' : ℕ) ∨ (b : ℕ) = 2 * (b' : ℕ) + 1) := by
  rw [parent, dite_eq_right h]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · show (k : ℕ) = ((k : ℕ) - 1) + 1
    omega
  · show (b : ℕ) = 2 * ((b : ℕ) / 2) ∨ (b : ℕ) = 2 * ((b : ℕ) / 2) + 1
    omega

/-- The neighbours of a cycle vertex: its two cycle neighbours and the root of its tree. -/
theorem neighborFinset_cyc [NeZero ℓ] (hℓ : 3 ≤ ℓ) (hR : 0 < R) (i : ZMod ℓ) :
    (Q ℓ R).neighborFinset (Vtx.cyc i)
      = {Vtx.cyc (i + 1), Vtx.cyc (i - 1), Vtx.brn i ⟨0, hR⟩ ⟨0, Nat.one_pos⟩} := by
  obtain ⟨hne1, hne2⟩ := cyc_ne_succ ℓ (by omega) i
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  cases v with
  | cyc j =>
    rw [adj_cyc_cyc]
    constructor
    · rintro ⟨hne, hj | hj⟩
      · exact Or.inl (by rw [hj])
      · exact Or.inr (Or.inl (by rw [hj]; ring_nf))
    · rintro (h | h | h)
      · injection h with h; subst h
        exact ⟨hne1, Or.inl rfl⟩
      · injection h with h; subst h
        exact ⟨hne2, Or.inr (by ring)⟩
      · exact absurd h (by simp)
  | brn i' k b =>
    rw [adj_cyc_brn]
    constructor
    · rintro ⟨hi, hk, hb⟩
      exact Or.inr (Or.inr ((brn_eq_brn_iff ℓ R).mpr ⟨hi.symm, hk, hb⟩))
    · rintro (h | h | h)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · obtain ⟨h1, h2, h3⟩ := (brn_eq_brn_iff ℓ R).mp h.symm
        exact ⟨h1, h2.symm, h3.symm⟩

/-- The neighbours of a non-leaf branch vertex: its parent and its two children. -/
theorem neighborFinset_brn [NeZero ℓ] (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 < R) :
    (Q ℓ R).neighborFinset (Vtx.brn i k b)
      = {parent ℓ R i k b, childL ℓ R i k b hk, childR ℓ R i k b hk} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  cases v with
  | cyc j =>
    rw [adj_brn_cyc]
    constructor
    · rintro ⟨hj, hk0, _⟩
      exact Or.inl (by rw [parent_of_zero ℓ R hk0, hj])
    · rintro (h | h | h)
      · by_cases hk0 : (k : ℕ) = 0
        · rw [parent_of_zero ℓ R hk0] at h
          injection h with hji
          have hb : (b : ℕ) = 0 := by
            have hlt := b.isLt
            have h1 : (2 : ℕ) ^ (k : ℕ) = 1 := by rw [hk0]; norm_num
            omega
          exact ⟨hji, hk0, hb⟩
        · obtain ⟨_, _, hpar, _, _⟩ := parent_of_pos ℓ R hk0
          rw [hpar] at h; exact absurd h (by simp)
      · rw [childL] at h; exact absurd h (by simp)
      · rw [childR] at h; exact absurd h (by simp)
  | brn i' k' b' =>
    rw [adj_brn_brn]
    constructor
    · rintro ⟨_, (⟨hi, hkk, hbb⟩ | ⟨hi, hkk, hbb⟩)⟩
      · -- `v` is a child of `brn i k b`
        rcases hbb with h | h
        · exact Or.inr (Or.inl ((brn_eq_brn_iff ℓ R).mpr ⟨hi.symm, hkk, h⟩))
        · exact Or.inr (Or.inr ((brn_eq_brn_iff ℓ R).mpr ⟨hi.symm, hkk, h⟩))
      · -- `v` is the parent of `brn i k b`
        refine Or.inl ?_
        have hk0 : (k : ℕ) ≠ 0 := by omega
        obtain ⟨kp, bp, hpar, hkp, hbp⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
        rw [hpar]
        exact (brn_eq_brn_iff ℓ R).mpr ⟨hi, by omega, by omega⟩
    · rintro (h | h | h)
      · by_cases hk0 : (k : ℕ) = 0
        · rw [parent_of_zero ℓ R hk0] at h; exact absurd h (by simp)
        · obtain ⟨kp, bp, hpar, hkp, hbp⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
          rw [hpar] at h
          obtain ⟨hi, hkk, hbb⟩ := (brn_eq_brn_iff ℓ R).mp h
          refine ⟨fun hc => ?_, Or.inr ⟨hi, by omega, by omega⟩⟩
          obtain ⟨_, hkc, _⟩ := (brn_eq_brn_iff ℓ R).mp hc
          omega
      · rw [childL] at h
        obtain ⟨hi, hkk, hbb⟩ := (brn_eq_brn_iff ℓ R).mp h
        simp only [] at hkk hbb
        refine ⟨fun hc => ?_, Or.inl ⟨hi.symm, by omega, Or.inl (by omega)⟩⟩
        obtain ⟨_, hkc, _⟩ := (brn_eq_brn_iff ℓ R).mp hc
        omega
      · rw [childR] at h
        obtain ⟨hi, hkk, hbb⟩ := (brn_eq_brn_iff ℓ R).mp h
        simp only [] at hkk hbb
        refine ⟨fun hc => ?_, Or.inl ⟨hi.symm, by omega, Or.inr (by omega)⟩⟩
        obtain ⟨_, hkc, _⟩ := (brn_eq_brn_iff ℓ R).mp hc
        omega

/-- The neighbours of a *leaf*: just its parent. The children would sit at depth `R + 1`,
which `k' < R` rules out. -/
theorem neighborFinset_brn_leaf [NeZero ℓ] (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 = R) :
    (Q ℓ R).neighborFinset (Vtx.brn i k b) = {parent ℓ R i k b} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  cases v with
  | cyc j =>
    rw [adj_brn_cyc]
    constructor
    · rintro ⟨hj, hk0, _⟩
      rw [parent_of_zero ℓ R hk0, hj]
    · intro h
      by_cases hk0 : (k : ℕ) = 0
      · rw [parent_of_zero ℓ R hk0] at h
        injection h with hji
        have hb : (b : ℕ) = 0 := by
          have hlt := b.isLt
          have h1 : (2 : ℕ) ^ (k : ℕ) = 1 := by rw [hk0]; norm_num
          omega
        exact ⟨hji, hk0, hb⟩
      · obtain ⟨_, _, hpar, _, _⟩ := parent_of_pos ℓ R hk0
        rw [hpar] at h; exact absurd h (by simp)
  | brn i' k' b' =>
    rw [adj_brn_brn]
    constructor
    · rintro ⟨_, (⟨_, hkk, _⟩ | ⟨hi, hkk, hbb⟩)⟩
      · -- a child would need depth `R`, impossible for `k' : Fin R`
        have := k'.isLt
        omega
      · have hk0 : (k : ℕ) ≠ 0 := by omega
        obtain ⟨kp, bp, hpar, hkp, hbp⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
        rw [hpar]
        exact (brn_eq_brn_iff ℓ R).mpr ⟨hi, by omega, by omega⟩
    · intro h
      by_cases hk0 : (k : ℕ) = 0
      · rw [parent_of_zero ℓ R hk0] at h; exact absurd h (by simp)
      · obtain ⟨kp, bp, hpar, hkp, hbp⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
        rw [hpar] at h
        obtain ⟨hi, hkk, hbb⟩ := (brn_eq_brn_iff ℓ R).mp h
        refine ⟨fun hc => ?_, Or.inr ⟨hi, by omega, by omega⟩⟩
        obtain ⟨_, hkc, _⟩ := (brn_eq_brn_iff ℓ R).mp hc
        omega

/-- A leaf is adjacent to its parent. -/
theorem adj_brn_parent [NeZero ℓ] (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 = R) : (Q ℓ R).Adj (Vtx.brn i k b) (parent ℓ R i k b) := by
  have := neighborFinset_brn_leaf ℓ R i k b hk
  have hmem : parent ℓ R i k b ∈ (Q ℓ R).neighborFinset (Vtx.brn i k b) := by
    rw [this]; exact Finset.mem_singleton_self _
  exact (SimpleGraph.mem_neighborFinset _ _ _).mp hmem

theorem two_ne_zero_zmod (hℓ : 3 ≤ ℓ) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have h2 : ((2 : ℤ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have : (ℓ : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
  omega

/-- A cycle vertex has degree `3`: two cycle neighbours and the root of its tree. -/
theorem degree_cyc [NeZero ℓ] (hℓ : 3 ≤ ℓ) (hR : 0 < R) (i : ZMod ℓ) :
    (Q ℓ R).degree (Vtx.cyc i) = 3 := by
  rw [SimpleGraph.degree, neighborFinset_cyc ℓ R hℓ hR i]
  have hne : (i + 1 : ZMod ℓ) ≠ i - 1 := by
    intro h
    exact two_ne_zero_zmod ℓ hℓ (by linear_combination h)
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

/-- Every non-leaf vertex has degree `3`.

The cycle case is `degree_cyc`; the branch case still needs the analogue of
`neighborFinset_cyc` for `brn i k b`, whose two children live in `Fin (2 ^ (k+1))`. -/
theorem degree_eq_three [NeZero ℓ] (hℓ : 3 ≤ ℓ) (v : Vtx ℓ R) (hv : ¬ Vtx.IsLeaf ℓ R v) :
    (Q ℓ R).degree v = 3 := by
  cases v with
  | cyc i =>
    simp only [Vtx.IsLeaf] at hv
    exact degree_cyc ℓ R hℓ (Nat.pos_of_ne_zero hv) i
  | brn i k b =>
    simp only [Vtx.IsLeaf] at hv
    have hk : (k : ℕ) + 1 < R := by have := k.isLt; omega
    have hLR : childL ℓ R i k b hk ≠ childR ℓ R i k b hk := by
      rw [childL, childR]
      intro hc
      obtain ⟨_, _, hb⟩ := (brn_eq_brn_iff ℓ R).mp hc
      simp only [] at hb
      omega
    have hPchild : ∀ c : Vtx ℓ R, (∃ bb hbb, c = Vtx.brn i ⟨(k : ℕ) + 1, hk⟩ ⟨bb, hbb⟩) →
        parent ℓ R i k b ≠ c := by
      rintro c ⟨bb, hbb, rfl⟩
      by_cases hk0 : (k : ℕ) = 0
      · rw [parent_of_zero ℓ R hk0]; simp
      · obtain ⟨kp, bp, hpar, hkp, _⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
        rw [hpar]
        intro hc
        obtain ⟨_, hkc, _⟩ := (brn_eq_brn_iff ℓ R).mp hc
        simp only [] at hkc
        omega
    have hPL : parent ℓ R i k b ≠ childL ℓ R i k b hk :=
      hPchild _ ⟨_, _, rfl⟩
    have hPR : parent ℓ R i k b ≠ childR ℓ R i k b hk :=
      hPchild _ ⟨_, _, rfl⟩
    rw [SimpleGraph.degree, neighborFinset_brn ℓ R i k b hk,
      Finset.card_insert_of_notMem (by simp [hPL, hPR]),
      Finset.card_insert_of_notMem (by simp [hLR]), Finset.card_singleton]

/-! ## The phase configuration -/

/-- The phase drops `Δ_k`, eq. (4). The recurrence `sin Δ_k = ½ sin Δ_{k-1}` with `Δ_0 = η`
is solved by `Δ_k = arcsin (2^{-k} sin η)`. -/
noncomputable def Δ (η : ℝ) (k : ℕ) : ℝ := arcsin ((1 / 2 : ℝ) ^ k * sin η)

/-- The argument of `arcsin` in the definition of `Δ` always lies in `[-1, 1]`. -/
theorem abs_arg_le_one (η : ℝ) (k : ℕ) : |(1 / 2 : ℝ) ^ k * sin η| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/2:ℝ) ^ k)]
  have h1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : |sin η| ≤ 1 := Real.abs_sin_le_one η
  nlinarith [abs_nonneg (sin η), pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) k]

theorem neg_one_le_arg (η : ℝ) (k : ℕ) : -1 ≤ (1 / 2 : ℝ) ^ k * sin η :=
  neg_le_of_abs_le (abs_arg_le_one η k)

theorem arg_le_one (η : ℝ) (k : ℕ) : (1 / 2 : ℝ) ^ k * sin η ≤ 1 :=
  le_of_abs_le (abs_arg_le_one η k)

theorem Δ_zero {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) : Δ η 0 = η := by
  unfold Δ
  rw [pow_zero, one_mul]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) h₁.le

theorem sin_Δ (η : ℝ) (k : ℕ) : sin (Δ η k) = (1 / 2 : ℝ) ^ k * sin η :=
  Real.sin_arcsin (neg_one_le_arg η k) (arg_le_one η k)

/-- The recurrence of eq. (4) holds: `sin Δ_k = ½ sin Δ_{k-1}`. -/
theorem sin_Δ_succ (η : ℝ) (k : ℕ) : sin (Δ η (k + 1)) = (1 / 2 : ℝ) * sin (Δ η k) := by
  rw [sin_Δ, sin_Δ, pow_succ]
  ring

theorem Δ_strictAnti {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) :
    StrictAnti (Δ η) := by
  have hsin : 0 < sin η := Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith [Real.pi_pos])
  intro j k hjk
  refine Real.arcsin_lt_arcsin (neg_one_le_arg η k) ?_ (arg_le_one η j)
  have : (1 / 2 : ℝ) ^ k < (1 / 2 : ℝ) ^ j :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hjk
  exact mul_lt_mul_of_pos_right this hsin

/-- The `4`-periodic sign pattern `+, +, -, -` on the cycle. This is where `ℓ ≡ 0 (mod 4)` is
used: the pattern must close up around the cycle. -/
def sgn (i : ℕ) : ℝ := if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1

/-- If `4 ∣ ℓ` then reducing mod `ℓ` first does not change the residue mod `4`. This is where
`ℓ ≡ 0 (mod 4)` enters: it is what lets the `4`-periodic sign pattern close up around the
cycle. -/
theorem mod_mod_of_dvd_four {n : ℕ} (hℓ : ℓ % 4 = 0) : (n % ℓ) % 4 = n % 4 := by
  obtain ⟨m, hm⟩ : 4 ∣ ℓ := Nat.dvd_of_mod_eq_zero hℓ
  conv_rhs => rw [← Nat.div_add_mod n ℓ]
  rw [hm, show 4 * m * (n / (4 * m)) = 4 * (m * (n / (4 * m))) by ring, Nat.mul_add_mod]

/-- Stepping once around the cycle steps the sign pattern by one. -/
theorem val_succ_mod_four [NeZero ℓ] (hℓ : ℓ % 4 = 0) (i : ZMod ℓ) :
    ((i + 1).val) % 4 = (i.val + 1) % 4 := by
  have : Fact (1 < ℓ) := ⟨by have := Nat.pos_of_ne_zero (NeZero.ne ℓ); omega⟩
  rw [ZMod.val_add, ZMod.val_one]
  exact mod_mod_of_dvd_four ℓ hℓ

/-- The configuration `θ^η` of eq. (5), in the closed form of eq. (6). -/
noncomputable def phase (η : ℝ) : Vtx ℓ R → ℝ
  | .cyc i => sgn i.val * (π - η / 2)
  | .brn i k _ => sgn i.val * (π - η / 2 - ∑ j ∈ range ((k : ℕ) + 1), Δ η j)

/-! ### Phases of the neighbours -/

theorem sgn_eq_one_or (i : ℕ) : sgn i = 1 ∨ sgn i = -1 := by
  unfold sgn; split <;> simp

theorem sgn_ne_zero (i : ℕ) : sgn i ≠ 0 := by
  rcases sgn_eq_one_or i with h | h <;> rw [h] <;> norm_num


theorem sgn_mul_sin (i : ℕ) (x : ℝ) : Real.sin (sgn i * x) = sgn i * Real.sin x := by
  rcases sgn_eq_one_or i with h | h <;> rw [h] <;> simp

theorem phase_cyc (η : ℝ) (i : ZMod ℓ) :
    phase ℓ R η (Vtx.cyc i) = sgn i.val * (π - η / 2) := rfl

theorem phase_brn (η : ℝ) (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    phase ℓ R η (Vtx.brn i k b)
      = sgn i.val * (π - η / 2 - ∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j) := rfl

/-- The parent sits one level up, i.e. it has one fewer drop, whether it is a cycle vertex
(`k = 0`) or a branch vertex (`k > 0`). -/
theorem phase_parent (η : ℝ) (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ))) :
    phase ℓ R η (parent ℓ R i k b)
      = sgn i.val * (π - η / 2 - ∑ j ∈ Finset.range (k : ℕ), Δ η j) := by
  by_cases hk0 : (k : ℕ) = 0
  · rw [parent_of_zero ℓ R hk0, phase_cyc, hk0]
    simp
  · rw [parent, dite_eq_right hk0, phase_brn]
    simp only []
    rw [show (k : ℕ) - 1 + 1 = (k : ℕ) from by omega]

theorem phase_childL (η : ℝ) (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 < R) :
    phase ℓ R η (childL ℓ R i k b hk)
      = sgn i.val * (π - η / 2 - ∑ j ∈ Finset.range ((k : ℕ) + 2), Δ η j) := by
  rw [childL, phase_brn]

theorem phase_childR (η : ℝ) (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 < R) :
    phase ℓ R η (childR ℓ R i k b hk)
      = sgn i.val * (π - η / 2 - ∑ j ∈ Finset.range ((k : ℕ) + 2), Δ η j) := by
  rw [childR, phase_brn]

theorem sgn_eq_one {i : ℕ} (h : i % 4 = 0 ∨ i % 4 = 1) : sgn i = 1 := by
  unfold sgn; rw [ite_eq_left h]

theorem sgn_eq_neg_one {i : ℕ} (h : ¬(i % 4 = 0 ∨ i % 4 = 1)) : sgn i = -1 := by
  unfold sgn; rw [ite_eq_right h]

/-- Of the two cycle neighbours of `i`, exactly one carries the same sign and one the
opposite. This is the combinatorial content of the `+,+,-,-` pattern, and it is what makes
the current `sin η` arrive at `i` along the cycle and leave down the pendant edge. -/
theorem sgn_neighbors [NeZero ℓ] (hℓ : ℓ % 4 = 0) (i : ZMod ℓ) :
    (sgn (i + 1).val = sgn i.val ∧ sgn (i - 1).val = -sgn i.val) ∨
    (sgn (i + 1).val = -sgn i.val ∧ sgn (i - 1).val = sgn i.val) := by
  have h1 : (i + 1).val % 4 = (i.val + 1) % 4 := val_succ_mod_four ℓ hℓ i
  have h2 : ((i - 1) + 1).val % 4 = ((i - 1).val + 1) % 4 := val_succ_mod_four ℓ hℓ (i - 1)
  rw [sub_add_cancel] at h2
  have hr : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
  rcases hr with h | h | h | h
  · exact Or.inl ⟨by rw [sgn_eq_one (Or.inr (by omega)), sgn_eq_one (Or.inl h)],
      by rw [sgn_eq_neg_one (by omega), sgn_eq_one (Or.inl h)]⟩
  · exact Or.inr ⟨by rw [sgn_eq_neg_one (by omega), sgn_eq_one (Or.inr h)],
      by rw [sgn_eq_one (Or.inl (by omega)), sgn_eq_one (Or.inr h)]⟩
  · exact Or.inl ⟨by rw [sgn_eq_neg_one (by omega), sgn_eq_neg_one (by omega)],
      by rw [sgn_eq_one (Or.inr (by omega)), sgn_eq_neg_one (by omega)]; norm_num⟩
  · exact Or.inr ⟨by rw [sgn_eq_one (Or.inl (by omega)), sgn_eq_neg_one (by omega)]; norm_num,
      by rw [sgn_eq_neg_one (by omega), sgn_eq_neg_one (by omega)]⟩

/-- Pulling the common sign out of a phase difference. -/
theorem sin_sgn_sub (i : ℕ) (x y : ℝ) :
    Real.sin (sgn i * x - sgn i * y) = sgn i * Real.sin (x - y) := by
  rw [show sgn i * x - sgn i * y = sgn i * (x - y) from by ring, sgn_mul_sin]

/-- The equilibrium equation at a non-leaf branch vertex: the incoming current `sin Δ_{k-1}`
splits evenly between the two children, which is exactly `sin Δ_{k-1} = 2 sin Δ_k`. -/
theorem grad_brn_eq_zero [NeZero ℓ] (η : ℝ) (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hk : (k : ℕ) + 1 < R) :
    Kuramoto.grad (Q ℓ R) (phase ℓ R η) (Vtx.brn i k b) = 0 := by
  have hLR : childL ℓ R i k b hk ≠ childR ℓ R i k b hk := by
    rw [childL, childR]
    intro hc
    obtain ⟨_, _, hb⟩ := (brn_eq_brn_iff ℓ R).mp hc
    simp only [] at hb
    omega
  have hPchild : ∀ c : Vtx ℓ R, (∃ bb hbb, c = Vtx.brn i ⟨(k : ℕ) + 1, hk⟩ ⟨bb, hbb⟩) →
      parent ℓ R i k b ≠ c := by
    rintro c ⟨bb, hbb, rfl⟩
    by_cases hk0 : (k : ℕ) = 0
    · rw [parent_of_zero ℓ R hk0]; simp
    · obtain ⟨kp, bp, hpar, hkp, _⟩ := parent_of_pos ℓ R (i := i) (k := k) (b := b) hk0
      rw [hpar]
      intro hc
      obtain ⟨_, hkc, _⟩ := (brn_eq_brn_iff ℓ R).mp hc
      simp only [] at hkc
      omega
  have hPL : parent ℓ R i k b ≠ childL ℓ R i k b hk := hPchild _ ⟨_, _, rfl⟩
  have hPR : parent ℓ R i k b ≠ childR ℓ R i k b hk := hPchild _ ⟨_, _, rfl⟩
  rw [Kuramoto.grad, neighborFinset_brn ℓ R i k b hk,
    Finset.sum_insert (by simp [hPL, hPR]), Finset.sum_insert (by simp [hLR]),
    Finset.sum_singleton, phase_brn, phase_parent, phase_childL, phase_childR]
  set S : ℝ := ∑ j ∈ Finset.range (k : ℕ), Δ η j with hS
  have e1 : ∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j = S + Δ η (k : ℕ) :=
    Finset.sum_range_succ _ _
  have e2 : ∑ j ∈ Finset.range ((k : ℕ) + 2), Δ η j = S + Δ η (k : ℕ) + Δ η ((k : ℕ) + 1) := by
    rw [show (k : ℕ) + 2 = ((k : ℕ) + 1) + 1 from rfl, Finset.sum_range_succ, e1]
  rw [e1, e2]
  simp only [sin_sgn_sub]
  rw [show π - η / 2 - (S + Δ η (k : ℕ)) - (π - η / 2 - S) = -Δ η (k : ℕ) from by ring,
    show π - η / 2 - (S + Δ η (k : ℕ))
        - (π - η / 2 - (S + Δ η (k : ℕ) + Δ η ((k : ℕ) + 1))) = Δ η ((k : ℕ) + 1) from by ring,
    Real.sin_neg, sin_Δ_succ]
  ring

/-- If a leaf carries phase `0`, its parent carries `ε_i Δ_k` — the one drop that is left
unbalanced, and hence the whole of the residual gradient. -/
theorem phase_parent_of_leaf_zero {η : ℝ} (i : ZMod ℓ) (k : Fin R) (b : Fin (2 ^ (k : ℕ)))
    (hz : phase ℓ R η (Vtx.brn i k b) = 0) :
    phase ℓ R η (parent ℓ R i k b) = sgn i.val * Δ η (k : ℕ) := by
  rw [phase_parent]
  rw [phase_brn, Finset.sum_range_succ] at hz
  linear_combination hz

/-! ### The leaves, indexed explicitly

For `R ≥ 1` the leaves are exactly the `brn i ⟨R-1, _⟩ b`, so they are indexed by
`ZMod ℓ × Fin (2^(R-1))`. That is what lets the residual gradient be summed. -/

/-- The leaf of branch `i` at position `b`. -/
def leafVtx (hR : 0 < R) (i : ZMod ℓ) (b : Fin (2 ^ (R - 1))) : Vtx ℓ R :=
  Vtx.brn i ⟨R - 1, by omega⟩ b

theorem isLeaf_leafVtx (hR : 0 < R) (i : ZMod ℓ) (b : Fin (2 ^ (R - 1))) :
    Vtx.IsLeaf ℓ R (leafVtx ℓ R hR i b) := by
  show R - 1 + 1 = R
  omega

theorem leafVtx_injective (hR : 0 < R) :
    Function.Injective (fun p : ZMod ℓ × Fin (2 ^ (R - 1)) => leafVtx ℓ R hR p.1 p.2) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  obtain ⟨h1, _, h3⟩ := (brn_eq_brn_iff ℓ R).mp h
  exact Prod.ext h1 (Fin.ext h3)

/-- Every leaf is of this form, once `R ≥ 1`. -/
theorem exists_leafVtx (hR : 0 < R) (w : Vtx ℓ R) (hw : Vtx.IsLeaf ℓ R w) :
    ∃ i b, w = leafVtx ℓ R hR i b := by
  cases w with
  | cyc i => exact absurd hw (by simp only [Vtx.IsLeaf]; omega)
  | brn i k b =>
    simp only [Vtx.IsLeaf] at hw
    have hkv : (k : ℕ) = R - 1 := by omega
    have h2 : (2 : ℕ) ^ (k : ℕ) = 2 ^ (R - 1) := by rw [hkv]
    refine ⟨i, ⟨(b : ℕ), ?_⟩, ?_⟩
    · have hb := b.isLt; omega
    · exact (brn_eq_brn_iff ℓ R).mpr ⟨rfl, hkv, rfl⟩

/-- **Proposition 2.1 (i).** `θ^η` satisfies the equilibrium equation at every non-leaf vertex,
for every `η`, with no constraint on `η` at all. The cycle vertices balance `sin η` against the
pendant edge; the branch vertices balance `sin Δ_{k-1} = 2 sin Δ_k`. -/
theorem grad_eq_zero_of_nonleaf [NeZero ℓ] (hℓ : ℓ % 4 = 0) (hℓ3 : 3 ≤ ℓ)
    {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) (v : Vtx ℓ R) (hv : ¬ Vtx.IsLeaf ℓ R v) :
    Kuramoto.grad (Q ℓ R) (phase ℓ R η) v = 0 := by
  cases v with
  | cyc i =>
    simp only [Vtx.IsLeaf] at hv
    have hR : 0 < R := Nat.pos_of_ne_zero hv
    have hne : (i + 1 : ZMod ℓ) ≠ i - 1 := fun h =>
      two_ne_zero_zmod ℓ hℓ3 (by linear_combination h)
    have h2t : Real.sin (2 * (π - η / 2)) = -Real.sin η := by
      rw [show 2 * (π - η / 2) = 2 * π - η from by ring, Real.sin_sub, Real.sin_two_pi,
        Real.cos_two_pi]
      ring
    rw [Kuramoto.grad, neighborFinset_cyc ℓ R hℓ3 hR i,
      Finset.sum_insert (by simp [hne]), Finset.sum_insert (by simp), Finset.sum_singleton]
    simp only [phase_cyc, phase_brn, Fin.val_mk, Nat.zero_add, Finset.sum_range_one,
      Δ_zero h₀ h₁]
    rcases sgn_neighbors ℓ hℓ i with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb,
        show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2) = sgn i.val * 0 from by ring,
        show sgn i.val * (π - η / 2) - -sgn i.val * (π - η / 2)
            = sgn i.val * (2 * (π - η / 2)) from by ring,
        show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2 - η)
            = sgn i.val * η from by ring]
      simp only [sgn_mul_sin, Real.sin_zero, h2t]
      ring
    · rw [ha, hb,
        show sgn i.val * (π - η / 2) - -sgn i.val * (π - η / 2)
            = sgn i.val * (2 * (π - η / 2)) from by ring,
        show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2) = sgn i.val * 0 from by ring,
        show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2 - η)
            = sgn i.val * η from by ring]
      simp only [sgn_mul_sin, Real.sin_zero, h2t]
      ring
  | brn i k b =>
    simp only [Vtx.IsLeaf] at hv
    exact grad_brn_eq_zero ℓ R η i k b (by have := k.isLt; omega)

/-- **Proposition 2.1 (ii), first half.** Every phase difference is at most `η < π/2`, so the
configuration is phase-cohesive. -/
theorem sgn_mul_cos (i : ℕ) (x : ℝ) : Real.cos (sgn i * x) = Real.cos x := by
  rcases sgn_eq_one_or i with h | h <;> rw [h] <;> simp

/-- Every drop `Δ_k` lies strictly inside `(0, π/2)`, so every branch edge has positive
weight. -/
theorem cos_Δ_pos {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) (k : ℕ) : 0 < Real.cos (Δ η k) := by
  have hpi := Real.pi_pos
  have hsin1 : Real.sin η < 1 := by
    have := Real.strictMonoOn_sin (a := η) ⟨by linarith, h₁.le⟩ ⟨by linarith, le_refl (π / 2)⟩ h₁
    rwa [Real.sin_pi_div_two] at this
  have hsin0 : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith)
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hlo : 0 < Δ η k := Real.arcsin_pos.mpr (mul_pos hpow hsin0)
  have hhi : Δ η k < π / 2 := Real.arcsin_lt_pi_div_two.mpr (by nlinarith)
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hhi⟩

theorem phaseCohesive_phase [NeZero ℓ] (hℓ : ℓ % 4 = 0)
    {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) :
    Kuramoto.PhaseCohesive (Q ℓ R) (phase ℓ R η) := by
  have hpi := Real.pi_pos
  have hcosη : 0 < Real.cos η := Real.cos_pos_of_mem_Ioo ⟨by linarith, h₁⟩
  have h2tc : Real.cos (2 * (π - η / 2)) = Real.cos η := by
    rw [show 2 * (π - η / 2) = 2 * π - η from by ring, Real.cos_sub, Real.sin_two_pi,
      Real.cos_two_pi]
    ring
  intro u v huv
  cases u with
  | cyc i =>
    cases v with
    | cyc j =>
      rw [adj_cyc_cyc] at huv
      obtain ⟨hij, hj⟩ := huv
      simp only [phase_cyc]
      -- `j` is `i ± 1`; either it carries the same sign (difference `0`) or the opposite
      -- (difference `±(2π - η)`), and `cos` of both is positive
      have key : ∀ sj : ℝ, sj = sgn i.val ∨ sj = -sgn i.val →
          0 < Real.cos (sgn i.val * (π - η / 2) - sj * (π - η / 2)) := by
        rintro sj (rfl | rfl)
        · rw [show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2) = sgn i.val * 0 from by ring,
            sgn_mul_cos, Real.cos_zero]
          norm_num
        · rw [show sgn i.val * (π - η / 2) - -sgn i.val * (π - η / 2)
              = sgn i.val * (2 * (π - η / 2)) from by ring, sgn_mul_cos, h2tc]
          exact hcosη
      rcases hj with rfl | hj
      · rcases sgn_neighbors ℓ hℓ i with ⟨ha, _⟩ | ⟨ha, _⟩
        · exact key _ (Or.inl ha)
        · exact key _ (Or.inr ha)
      · have hji : j = i - 1 := by rw [hj]; ring
        subst hji
        rcases sgn_neighbors ℓ hℓ i with ⟨_, hb⟩ | ⟨_, hb⟩
        · exact key _ (Or.inr hb)
        · exact key _ (Or.inl hb)
    | brn i' k b =>
      rw [adj_cyc_brn] at huv
      obtain ⟨rfl, hk, hb⟩ := huv
      simp only [phase_cyc, phase_brn, hk, Nat.zero_add, Finset.sum_range_one, Δ_zero h₀ h₁]
      rw [show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2 - η) = sgn i.val * η from by ring,
        sgn_mul_cos]
      exact hcosη
  | brn i k b =>
    cases v with
    | cyc j =>
      rw [adj_brn_cyc] at huv
      obtain ⟨rfl, hk, hb⟩ := huv
      simp only [phase_cyc, phase_brn, hk, Nat.zero_add, Finset.sum_range_one, Δ_zero h₀ h₁]
      rw [show sgn j.val * (π - η / 2 - η) - sgn j.val * (π - η / 2) = sgn j.val * (-η) from by
          ring, sgn_mul_cos, Real.cos_neg]
      exact hcosη
    | brn i' k' b' =>
      rw [adj_brn_brn] at huv
      obtain ⟨_, (⟨rfl, hkk, _⟩ | ⟨rfl, hkk, _⟩)⟩ := huv
      · simp only [phase_brn, hkk]
        rw [show (k : ℕ) + 1 + 1 = (k : ℕ) + 2 from rfl,
          show ∑ j ∈ Finset.range ((k : ℕ) + 2), Δ η j
              = (∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j) + Δ η ((k : ℕ) + 1) from
            Finset.sum_range_succ _ _]
        rw [show sgn i.val * (π - η / 2 - ∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j)
              - sgn i.val * (π - η / 2
                  - ((∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j) + Δ η ((k : ℕ) + 1)))
            = sgn i.val * Δ η ((k : ℕ) + 1) from by ring, sgn_mul_cos]
        exact cos_Δ_pos h₀ h₁ _
      · simp only [phase_brn, hkk]
        rw [show (k' : ℕ) + 1 + 1 = (k' : ℕ) + 2 from rfl,
          show ∑ j ∈ Finset.range ((k' : ℕ) + 2), Δ η j
              = (∑ j ∈ Finset.range ((k' : ℕ) + 1), Δ η j) + Δ η ((k' : ℕ) + 1) from
            Finset.sum_range_succ _ _]
        rw [show sgn i'.val * (π - η / 2
                  - ((∑ j ∈ Finset.range ((k' : ℕ) + 1), Δ η j) + Δ η ((k' : ℕ) + 1)))
              - sgn i'.val * (π - η / 2 - ∑ j ∈ Finset.range ((k' : ℕ) + 1), Δ η j)
            = sgn i'.val * (-Δ η ((k' : ℕ) + 1)) from by ring, sgn_mul_cos, Real.cos_neg]
        exact cos_Δ_pos h₀ h₁ _

theorem abs_sgn_mul (i : ℕ) (x : ℝ) : |sgn i * x| = |x| := by
  rcases sgn_eq_one_or i with h | h <;> rw [h] <;> simp

theorem Δ_nonneg {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) (k : ℕ) : 0 ≤ Δ η k :=
  Real.arcsin_nonneg.mpr (mul_nonneg (by positivity)
    (Real.sin_nonneg_of_nonneg_of_le_pi h₀.le (by linarith [Real.pi_pos])))

theorem Δ_le {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) (k : ℕ) : Δ η k ≤ η := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Δ_zero h₀ h₁]
  · have := Δ_strictAnti h₀ h₁ hk
    rw [Δ_zero h₀ h₁] at this
    exact this.le

/-- **Proposition 2.1 (ii), with the representative made explicit.** Every edge of `Q_{ℓ,R}`
carries a phase difference within `η` of `2πℤ`: this is `max_e |Δ_e| = η`, with `Δ_e` the
representative in `(-π, π]` as in the paper.

The distinction matters. On a cycle edge with opposite signs the *real* difference is
`±2t = ±(2π − η)`, not `±η`; only its representative is `∓η`. -/
theorem phase_diff_near [NeZero ℓ] (hℓ : ℓ % 4 = 0) {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2)
    {u v : Vtx ℓ R} (huv : (Q ℓ R).Adj u v) :
    ∃ k : ℤ, |phase ℓ R η u - phase ℓ R η v - 2 * π * k| ≤ η := by
  have hpi := Real.pi_pos
  -- the two kinds of cycle edge: same sign (difference `0`), opposite (`±(2π − η)`)
  have key : ∀ (i : ℕ) (sj : ℝ), sj = sgn i ∨ sj = -sgn i →
      ∃ k : ℤ, |sgn i * (π - η / 2) - sj * (π - η / 2) - 2 * π * k| ≤ η := by
    rintro i sj (rfl | rfl)
    · exact ⟨0, by simp [h₀.le]⟩
    · rcases sgn_eq_one_or i with h | h <;> rw [h]
      · exact ⟨1, abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
      · exact ⟨-1, abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
  cases u with
  | cyc i =>
    cases v with
    | cyc j =>
      rw [adj_cyc_cyc] at huv
      obtain ⟨_, hj⟩ := huv
      simp only [phase_cyc]
      rcases hj with rfl | hj
      · rcases sgn_neighbors ℓ hℓ i with ⟨ha, _⟩ | ⟨ha, _⟩
        · exact key _ _ (Or.inl ha)
        · exact key _ _ (Or.inr ha)
      · have hji : j = i - 1 := by rw [hj]; ring
        subst hji
        rcases sgn_neighbors ℓ hℓ i with ⟨_, hb⟩ | ⟨_, hb⟩
        · exact key _ _ (Or.inr hb)
        · exact key _ _ (Or.inl hb)
    | brn i' k b =>
      rw [adj_cyc_brn] at huv
      obtain ⟨rfl, hk, hb⟩ := huv
      refine ⟨0, ?_⟩
      simp only [phase_cyc, phase_brn, hk, Nat.zero_add, Finset.sum_range_one, Δ_zero h₀ h₁,
        Int.cast_zero, mul_zero, sub_zero]
      rw [show sgn i.val * (π - η / 2) - sgn i.val * (π - η / 2 - η) = sgn i.val * η from by ring,
        abs_sgn_mul, abs_of_pos h₀]
  | brn i k b =>
    cases v with
    | cyc j =>
      rw [adj_brn_cyc] at huv
      obtain ⟨rfl, hk, hb⟩ := huv
      refine ⟨0, ?_⟩
      simp only [phase_cyc, phase_brn, hk, Nat.zero_add, Finset.sum_range_one, Δ_zero h₀ h₁,
        Int.cast_zero, mul_zero, sub_zero]
      rw [show sgn j.val * (π - η / 2 - η) - sgn j.val * (π - η / 2) = sgn j.val * (-η) from by
          ring, abs_sgn_mul, abs_neg, abs_of_pos h₀]
    | brn i' k' b' =>
      rw [adj_brn_brn] at huv
      refine ⟨0, ?_⟩
      simp only [Int.cast_zero, mul_zero, sub_zero]
      obtain ⟨_, (⟨rfl, hkk, _⟩ | ⟨rfl, hkk, _⟩)⟩ := huv
      · simp only [phase_brn, hkk]
        rw [show (k : ℕ) + 1 + 1 = (k : ℕ) + 2 from rfl,
          show ∑ j ∈ Finset.range ((k : ℕ) + 2), Δ η j
              = (∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j) + Δ η ((k : ℕ) + 1) from
            Finset.sum_range_succ _ _]
        rw [show sgn i.val * (π - η / 2 - ∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j)
              - sgn i.val * (π - η / 2
                  - ((∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j) + Δ η ((k : ℕ) + 1)))
            = sgn i.val * Δ η ((k : ℕ) + 1) from by ring, abs_sgn_mul,
          abs_of_nonneg (Δ_nonneg h₀ h₁ _)]
        exact Δ_le h₀ h₁ _
      · simp only [phase_brn, hkk]
        rw [show (k' : ℕ) + 1 + 1 = (k' : ℕ) + 2 from rfl,
          show ∑ j ∈ Finset.range ((k' : ℕ) + 2), Δ η j
              = (∑ j ∈ Finset.range ((k' : ℕ) + 1), Δ η j) + Δ η ((k' : ℕ) + 1) from
            Finset.sum_range_succ _ _]
        rw [show sgn i'.val * (π - η / 2
                  - ((∑ j ∈ Finset.range ((k' : ℕ) + 1), Δ η j) + Δ η ((k' : ℕ) + 1)))
              - sgn i'.val * (π - η / 2 - ∑ j ∈ Finset.range ((k' : ℕ) + 1), Δ η j)
            = sgn i'.val * (-Δ η ((k' : ℕ) + 1)) from by ring, abs_sgn_mul, abs_neg,
          abs_of_nonneg (Δ_nonneg h₀ h₁ _)]
        exact Δ_le h₀ h₁ _

/-- **Proposition 2.1 (ii), as stated in the paper**: `max_e |Δ_e| ≤ η` on `Q_{ℓ,R}`, with
`Δ_e` the representative of §1.3 (`Kuramoto.phaseDiff`). The bound is attained on
the pendant edges, so this is `max_e |Δ_e| = η`. -/
theorem abs_phaseDiff_phase_le [NeZero ℓ] (hℓ : ℓ % 4 = 0) {η : ℝ} (h₀ : 0 < η)
    (h₁ : η < π / 2) {u v : Vtx ℓ R} (huv : (Q ℓ R).Adj u v) :
    |Kuramoto.phaseDiff (phase ℓ R η) u v| ≤ η :=
  (Kuramoto.abs_phaseDiff_le_iff _ u v (by linarith [Real.pi_pos])).mpr
    (phase_diff_near ℓ R hℓ h₀ h₁ huv)

/-- **Proposition 2.1 (ii), second half.** A branch edge joining depth `k` to depth `k + 1`
carries `|Δ_e| = Δ_k ≤ (π/2) 2^{-k}`; for `k = 0` this is the pendant edge, carrying `η`. -/
theorem absDelta_branch {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) (k : ℕ) :
    Δ η k ≤ (π / 2) * (1 / 2 : ℝ) ^ k := by
  set t : ℝ := (1 / 2 : ℝ) ^ k with ht
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  -- `t * sin η ≤ t ≤ sin (π/2 * t)` (Jordan), then apply the monotone `arcsin`
  have hstep : t * sin η ≤ sin (π / 2 * t) :=
    le_trans (by nlinarith [Real.sin_le_one η]) (Real.le_sin_mul ht0 ht1)
  calc Δ η k = arcsin (t * sin η) := rfl
    _ ≤ arcsin (sin (π / 2 * t)) := Real.arcsin_le_arcsin hstep
    _ = π / 2 * t := Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-! ## The boundary equation and its root -/

/-- `G_R(η) = π - (3/2) η - ∑_{k=1}^{R-1} arcsin (2^{-k} sin η)`, eq. (8).

The leaves carry phase `ε_i (t - ∑_{j<R} Δ_j)`, which vanishes exactly when `G_R η = 0`. -/
noncomputable def GG (R : ℕ) (η : ℝ) : ℝ :=
  π - (3 / 2) * η - ∑ k ∈ Ico 1 R, arcsin ((1 / 2 : ℝ) ^ k * sin η)

/-- The total drop along a branch down to depth `R`, split off its `k = 0` term. -/
theorem sum_Δ_range {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2) {R : ℕ} (hR : 0 < R) :
    ∑ j ∈ Finset.range R, Δ η j = η + ∑ j ∈ Finset.Ico 1 R, arcsin ((1 / 2 : ℝ) ^ j * sin η) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hR, Δ_zero h₀ h₁]
  rfl

theorem leaf_phase_eq_zero_iff [NeZero ℓ] {η : ℝ} (h₀ : 0 < η) (h₁ : η < π / 2)
    (v : Vtx ℓ R) (hv : Vtx.IsLeaf ℓ R v) :
    phase ℓ R η v = 0 ↔ GG R η = 0 := by
  have hpi := Real.pi_pos
  cases v with
  | cyc i =>
    -- a cycle vertex is a leaf only in the degenerate case `R = 0`, where both sides are false
    simp only [Vtx.IsLeaf] at hv
    subst hv
    constructor
    · intro h
      exfalso
      simp only [phase] at h
      rcases (mul_eq_zero.mp h) with hs | hs
      · exact sgn_ne_zero i.val hs
      · nlinarith
    · intro h
      exfalso
      unfold GG at h
      rw [show Finset.Ico 1 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty, sub_zero] at h
      nlinarith
  | brn i k b =>
    simp only [Vtx.IsLeaf] at hv
    have hR0 : 0 < R := by omega
    have hexp : π - η / 2 - ∑ j ∈ Finset.range ((k : ℕ) + 1), Δ η j = GG R η := by
      rw [hv, sum_Δ_range h₀ h₁ hR0]
      unfold GG
      ring
    simp only [phase, hexp]
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_left (sgn_ne_zero i.val)
    · intro h; rw [h, mul_zero]

theorem GG_strictAnti (R : ℕ) : StrictAntiOn (GG R) (Set.Icc 0 (π / 2)) := by
  intro a ha b hb hab
  unfold GG
  have hsin : sin a ≤ sin b :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ha.1, Real.pi_pos]) hb.2 hab.le
  have hterms : ∀ k ∈ Finset.Ico 1 R,
      arcsin ((1 / 2 : ℝ) ^ k * sin a) ≤ arcsin ((1 / 2 : ℝ) ^ k * sin b) := by
    intro k _
    exact Real.arcsin_le_arcsin (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) k])
  have hsum : ∑ k ∈ Finset.Ico 1 R, arcsin ((1 / 2 : ℝ) ^ k * sin a)
      ≤ ∑ k ∈ Finset.Ico 1 R, arcsin ((1 / 2 : ℝ) ^ k * sin b) :=
    Finset.sum_le_sum hterms
  linarith

theorem GG_zero (R : ℕ) : GG R 0 = π := by
  unfold GG
  simp

theorem geom_Ico_succ (n : ℕ) : ∑ k ∈ Finset.Ico 1 (n + 1), (1 / 2 : ℝ) ^ k = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_Ico_succ_top (by omega), ih]; ring

theorem geom_Ico_le_one (R : ℕ) : ∑ k ∈ Finset.Ico 1 R, (1 / 2 : ℝ) ^ k ≤ 1 := by
  cases R with
  | zero => simp
  | succ n =>
    rw [geom_Ico_succ n]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith

/-- `x ≤ arcsin x` on `[0, 1]`, since `sin y < y` for `y > 0`. -/
theorem self_le_arcsin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ arcsin x := by
  rcases eq_or_lt_of_le hx0 with h | h
  · simp [← h]
  · have hpos : 0 < arcsin x := Real.arcsin_pos.mpr h
    have hlt := Real.sin_lt hpos
    rw [Real.sin_arcsin (by linarith) hx1] at hlt
    linarith

theorem arcsin_one_half : arcsin (1 / 2) = π / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- `G_R(π/2) ≤ G_4(π/2) = π/4 − π/6 − arcsin ¼ − arcsin ⅛ < 0` for `R ≥ 4`, using
`arcsin x ≥ x`: `π/6 + 1/4 + 1/8 > π/4` holds because `π < 4`. For `R = 3` the sum
falls below `π/4`, which is exactly why `R ≥ 4` is needed. -/
theorem GG_pi_div_two_neg {R : ℕ} (hR : 4 ≤ R) : GG R (π / 2) < 0 := by
  unfold GG
  rw [Real.sin_pi_div_two]
  simp only [mul_one]
  have hnn : ∀ k ∈ Finset.Ico 1 R, (0 : ℝ) ≤ arcsin ((1 / 2 : ℝ) ^ k) := fun k _ =>
    Real.arcsin_nonneg.mpr (by positivity)
  have hsub : Finset.Ico 1 4 ⊆ Finset.Ico 1 R := Finset.Ico_subset_Ico (le_refl 1) hR
  have hle : ∑ k ∈ Finset.Ico 1 4, arcsin ((1 / 2 : ℝ) ^ k)
      ≤ ∑ k ∈ Finset.Ico 1 R, arcsin ((1 / 2 : ℝ) ^ k) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnn k hk
  have hset : Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) := by decide
  have hexp : ∑ k ∈ Finset.Ico 1 4, arcsin ((1 / 2 : ℝ) ^ k)
      = arcsin (1 / 2) + arcsin (1 / 4) + arcsin (1 / 8) := by
    rw [hset]
    norm_num
    ring
  have h2 : (1 / 4 : ℝ) ≤ arcsin (1 / 4) := self_le_arcsin (by norm_num) (by norm_num)
  have h3 : (1 / 8 : ℝ) ≤ arcsin (1 / 8) := self_le_arcsin (by norm_num) (by norm_num)
  rw [hexp, arcsin_one_half] at hle
  linarith [Real.pi_le_four]

/-- `G_R` is continuous: it is a constant minus a linear term minus a finite sum of
compositions of `arcsin` with continuous functions. -/
theorem GG_continuous (R : ℕ) : Continuous (GG R) := by
  unfold GG
  exact (continuous_const.sub (continuous_const.mul continuous_id)).sub
    (continuous_finsetSum _ fun k _ =>
      Real.continuous_arcsin.comp (continuous_const.mul Real.continuous_sin))

/-- **Proposition 2.1 (iii), existence and uniqueness.** -/
theorem exists_unique_root {R : ℕ} (hR : 4 ≤ R) :
    ∃! η : ℝ, η ∈ Set.Ioo 0 (π / 2) ∧ GG R η = 0 := by
  have hpi : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  -- existence, by the intermediate value theorem between `G_R 0 = π > 0` and `G_R (π/2) < 0`
  have hmem : (0 : ℝ) ∈ Set.Icc (GG R (π / 2)) (GG R 0) := by
    constructor
    · exact le_of_lt (GG_pi_div_two_neg hR)
    · rw [GG_zero]; linarith [Real.pi_pos]
  obtain ⟨η, hη, hη0⟩ :=
    intermediate_value_Icc' hpi.le (GG_continuous R).continuousOn hmem
  -- the root is interior, since `G_R` does not vanish at either endpoint
  have hne0 : η ≠ 0 := by
    intro h; rw [h, GG_zero] at hη0; linarith [Real.pi_pos]
  have hne1 : η ≠ π / 2 := by
    intro h; rw [h] at hη0; linarith [GG_pi_div_two_neg hR]
  have hmemIoo : η ∈ Set.Ioo 0 (π / 2) :=
    ⟨lt_of_le_of_ne hη.1 (Ne.symm hne0), lt_of_le_of_ne hη.2 hne1⟩
  -- uniqueness, from strict antitonicity on `[0, π/2]`
  refine ⟨η, ⟨hmemIoo, hη0⟩, fun y hy => ?_⟩
  by_contra hne
  have hyIcc : y ∈ Set.Icc 0 (π / 2) := ⟨hy.1.1.le, hy.1.2.le⟩
  have hηIcc : η ∈ Set.Icc 0 (π / 2) := ⟨hmemIoo.1.le, hmemIoo.2.le⟩
  rcases lt_or_gt_of_ne hne with h | h
  · have := GG_strictAnti R hyIcc hηIcc h
    rw [hy.2, hη0] at this; exact lt_irrefl 0 this
  · have := GG_strictAnti R hηIcc hyIcc h
    rw [hy.2, hη0] at this; exact lt_irrefl 0 this

/-- The root `η*(R)`, for `R ≥ 4`; junk value `0` otherwise, so that `root` is total.

Defining it by `Classical.choose` of `exists_unique_root` unconditionally would require a proof
of `4 ≤ R` that does not exist for small `R`. -/
noncomputable def root (R : ℕ) : ℝ :=
  if h : 4 ≤ R then (exists_unique_root h).choose else 0

/-- The defining property of `η*(R)`. -/
theorem root_spec {R : ℕ} (hR : 4 ≤ R) :
    root R ∈ Set.Ioo 0 (π / 2) ∧ GG R (root R) = 0 := by
  rw [root, dite_eq_left hR]
  exact (exists_unique_root hR).choose_spec.1

/-- Enlarging `R` only subtracts more terms from `G_R`. -/
theorem GG_sub_GG {R S : ℕ} (hRS : R ≤ S) (hR : 1 ≤ R) (η : ℝ) :
    GG S η = GG R η - ∑ k ∈ Finset.Ico R S, arcsin ((1 / 2 : ℝ) ^ k * sin η) := by
  unfold GG
  rw [← Finset.sum_Ico_consecutive _ hR hRS]
  ring

theorem root_strictAnti : StrictAntiOn root (Set.Ici 4) := by
  intro R hR S hS hRS
  simp only [Set.mem_Ici] at hR hS
  obtain ⟨hmemR, hzeroR⟩ := root_spec hR
  obtain ⟨hmemS, hzeroS⟩ := root_spec hS
  have hsin : 0 < sin (root R) :=
    Real.sin_pos_of_pos_of_lt_pi hmemR.1 (by linarith [Real.pi_pos, hmemR.2])
  -- `G_S (η*(R)) < 0`, because it is `G_R (η*(R)) = 0` minus strictly positive terms
  have hlt : GG S (root R) < 0 := by
    rw [GG_sub_GG (le_of_lt hRS) (by omega) (root R), hzeroR, zero_sub, neg_neg_iff_pos]
    refine Finset.sum_pos (fun k hk => ?_) ⟨R, Finset.mem_Ico.mpr ⟨le_refl R, hRS⟩⟩
    exact Real.arcsin_pos.mpr (by positivity)
  -- compare with `G_S (η*(S)) = 0` using strict antitonicity
  have hRIcc : root R ∈ Set.Icc 0 (π / 2) := ⟨hmemR.1.le, hmemR.2.le⟩
  have hSIcc : root S ∈ Set.Icc 0 (π / 2) := ⟨hmemS.1.le, hmemS.2.le⟩
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with h | h
  · rw [← h] at hzeroS; linarith
  · have := GG_strictAnti S hRIcc hSIcc h
    rw [hzeroS] at this; linarith

/-- The constant `δ₀ := π/2 − η*(4)` of Proposition 2.1 (iii). -/
noncomputable def δ₀ : ℝ := π / 2 - root 4

theorem δ₀_pos : 0 < δ₀ := by
  have := (root_spec (le_refl 4)).1.2
  unfold δ₀; linarith

/-- **Proposition 2.1 (iii), upper bound.** `η*(R) ≤ η*(4) = π/2 − δ₀` for every `R ≥ 4`,
because `η*` is strictly decreasing in `R`. -/
theorem root_le {R : ℕ} (hR : 4 ≤ R) : root R ≤ π / 2 - δ₀ := by
  unfold δ₀
  rw [sub_sub_cancel]
  rcases eq_or_lt_of_le hR with h | h
  · rw [← h]
  · exact (root_strictAnti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hR) h).le

/-- Concavity of `sin` on `[0, π]` gives the chord bound `(3/π) t ≤ sin t` on `[0, π/6]`,
sharper than Jordan's inequality on the shorter interval. -/
theorem three_div_pi_mul_le_sin {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 6) :
    (3 / π) * t ≤ sin t := by
  have hpi := Real.pi_pos
  set lam : ℝ := 6 * t / π with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hpi]; linarith
  have hconv := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_refl 0, hpi.le⟩)
    (show π / 6 ∈ Set.Icc 0 π from ⟨by positivity, by linarith⟩)
    (by linarith : (0 : ℝ) ≤ 1 - lam) hlam0 (by ring)
  rw [Real.sin_zero, Real.sin_pi_div_six] at hconv
  have harg : (1 - lam) • (0 : ℝ) + lam • (π / 6) = t := by
    simp only [smul_eq_mul, mul_zero, zero_add, hlam]
    field_simp
  rw [harg] at hconv
  simp only [smul_eq_mul, mul_zero, zero_add] at hconv
  have : lam * (1 / 2) = 3 / π * t := by rw [hlam]; field_simp; ring
  linarith [this ▸ hconv]

/-- **The bound the paper uses**: `arcsin x ≤ (π/3) x` on `[0, ½]`, the chord of the convex
function `arcsin` between `0` and `½`. -/
theorem arcsin_le_pi_div_three_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    arcsin x ≤ π / 3 * x := by
  have hpi := Real.pi_pos
  have ht0 : (0 : ℝ) ≤ π / 3 * x := by positivity
  have ht6 : π / 3 * x ≤ π / 6 := by nlinarith
  have hsin := three_div_pi_mul_le_sin ht0 ht6
  have heq : 3 / π * (π / 3 * x) = x := by field_simp
  rw [heq] at hsin
  calc arcsin x ≤ arcsin (sin (π / 3 * x)) := Real.arcsin_le_arcsin hsin
    _ = π / 3 * x := Real.arcsin_sin (by nlinarith) (by nlinarith)

/-- `G_R(4π/9) > 0` for every `R`, which is what pins the root above `4π/9`.

Using `arcsin x ≤ (π/3) x` on `[0, ½]` (valid since `2^{-k} sin η ≤ ½` for `k ≥ 1`) and
`∑_{k≥1} 2^{-k} ≤ 1`, one gets `G_R(η) ≥ π - (3/2)η - (π/3) sin η`, which at `η = 4π/9`
equals `(π/3)(1 - sin (4π/9)) > 0`. -/
theorem GG_pos_four_ninths_pi (R : ℕ) : 0 < GG R ((4 / 9) * π) := by
  have hpi := Real.pi_pos
  set η : ℝ := (4 / 9) * π with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηlt : η < π / 2 := by rw [hη]; nlinarith
  have hsin0 : 0 < sin η := Real.sin_pos_of_pos_of_lt_pi hη0 (by nlinarith)
  -- `sin η < 1` because `η < π/2` and `sin` is strictly monotone there
  have hsin1 : sin η < 1 := by
    have := Real.strictMonoOn_sin (a := η) ⟨by linarith, hηlt.le⟩
      ⟨by linarith, le_refl (π / 2)⟩ hηlt
    rwa [Real.sin_pi_div_two] at this
  -- bound each term of the sum by the chord
  have hterm : ∀ k ∈ Finset.Ico 1 R,
      arcsin ((1 / 2 : ℝ) ^ k * sin η) ≤ π / 3 * ((1 / 2 : ℝ) ^ k * sin η) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpow : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hb : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
      rw [pow_succ]; nlinarith
    refine arcsin_le_pi_div_three_mul (by positivity) ?_
    nlinarith [Real.sin_le_one η, pow_pos (by norm_num : (0:ℝ) < 1 / 2) k]
  have hsum : ∑ k ∈ Finset.Ico 1 R, arcsin ((1 / 2 : ℝ) ^ k * sin η)
      ≤ π / 3 * sin η := by
    calc ∑ k ∈ Finset.Ico 1 R, arcsin ((1 / 2 : ℝ) ^ k * sin η)
        ≤ ∑ k ∈ Finset.Ico 1 R, π / 3 * ((1 / 2 : ℝ) ^ k * sin η) :=
          Finset.sum_le_sum hterm
      _ = π / 3 * sin η * ∑ k ∈ Finset.Ico 1 R, (1 / 2 : ℝ) ^ k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ π / 3 * sin η * 1 := by
          have : (0 : ℝ) ≤ π / 3 * sin η := by positivity
          exact mul_le_mul_of_nonneg_left (geom_Ico_le_one R) this
      _ = π / 3 * sin η := mul_one _
  unfold GG
  have harith : π - 3 / 2 * η = π / 3 := by rw [hη]; ring
  nlinarith

/-- **Proposition 2.1 (iii), lower bound.** `η*(R) > 4π/9` for every `R`, using
`arcsin x ≤ (π/3) x` on `[0, ½]` and `∑_{k≥1} 2^{-k} = 1`. -/
theorem root_gt {R : ℕ} (hR : 4 ≤ R) : (4 / 9) * π < root R := by
  obtain ⟨hmem, hzero⟩ := root_spec hR
  -- `G_R` is strictly decreasing, so it suffices that `G_R (4π/9) > 0 = G_R (η*)`
  by_contra hcon
  push Not at hcon
  have hpi := Real.pi_pos
  have h49 : (4 / 9 : ℝ) * π ∈ Set.Icc 0 (π / 2) := by
    constructor <;> nlinarith
  have hroot : root R ∈ Set.Icc 0 (π / 2) := ⟨hmem.1.le, hmem.2.le⟩
  -- lower bound `G_R (η) ≥ π - (3/2)η - (π/3) sin η`, from `arcsin x ≤ (π/3) x` on `[0,½]`
  have hlb : 0 < GG R ((4 / 9) * π) := GG_pos_four_ninths_pi R
  rcases eq_or_lt_of_le hcon with h | h
  · rw [h] at hzero; linarith
  · have := GG_strictAnti R hroot h49 h
    rw [hzero] at this; linarith

/-- **Proposition 2.1 (iii), eq. `eq:etabounds`.** `4π/9 < η*(R) ≤ π/2 − δ₀` for all `R ≥ 4`. -/
theorem etabounds {R : ℕ} (hR : 4 ≤ R) : (4 / 9) * π < root R ∧ root R ≤ π / 2 - δ₀ :=
  ⟨root_gt hR, root_le hR⟩

/-- `δ₀ < π/18`, so for `δ ∈ (0, δ₀]` the margin `η*(R) − δ` stays positive (`> 7π/18`). -/
theorem δ₀_lt : δ₀ < π / 18 := by
  have := root_gt (le_refl 4)
  unfold δ₀; linarith

end Kuramoto.Gadget
