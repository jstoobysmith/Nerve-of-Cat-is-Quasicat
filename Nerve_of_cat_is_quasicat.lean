

import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Nerve
import LeanCopilot
import Mathlib.Tactic.FinCases

universe v u
open CategoryTheory CategoryTheory.Limits Opposite SSet
open Simplicial
open Nat
namespace Sequance_of_Arrows



structure SequenceArrows  (C : Type) [Category.{0,0} C] (n : ℕ) where
  maps : Fin (n+1) → (ComposableArrows C 1)
  object_lemm : (ComposableArrows.left ∘ maps ∘ Fin.succ) = (ComposableArrows.right ∘ maps ∘ Fin.castSucc):= by aesop

def SequenceArrows.obj {C : Type} [Category.{0,0} C] {n : ℕ} (S : SequenceArrows C n) : Fin (succ n+1)→ C
  | zero =>  (S.maps 0).left
  | (@Fin.mk (succ n+1) (succ x) h) => (S.maps (@Fin.mk (n+1) (x) (by linarith))).right

structure ComposibleArrowsWithSource  (C : Type) [Category.{0,0} C] (n : ℕ) (source : C) where
  val : ComposableArrows C n
  equal : source = val.left  := by aesop

def ComposibleArrowsWithSource.precomp  {C : Type} [Category.{0,0} C] {n : ℕ} {X Y : C} (S : ComposibleArrowsWithSource C n X) (f: Y⟶X) : ComposibleArrowsWithSource C (n+1) Y where
  val := S.val.precomp (f ≫ eqToHom (S.equal))


def reverse {n:ℕ} (i : Fin (n+1)) : Fin (n+1):= Fin.mk (n-i.val) (by {
  cases i
  simp_all only [ge_iff_le]
  apply Nat.sub_lt_succ
})

def toComposibleArrowsSource₀ {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) : (ComposibleArrowsWithSource C (0+1) (S.maps (reverse 0)).left) where
 val:=ComposableArrows.mk₁ (S.maps (Fin.last n)).hom
 equal := by {
  simp_all only [Functor.id_obj, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
  congr
 }


lemma arrowFromSequence_source {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i: Fin (n+1))  (hsucc: succ i.val < n+1): (S.maps (reverse (Fin.mk (succ i.val) hsucc))).left=(𝟭 C).obj (SequenceArrows.maps S (reverse (Fin.mk (succ i.val) hsucc))).left := by
  simp_all only [Functor.id_obj]

lemma arrowFromSequence_target {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i: Fin (n+1)) (hsucc: succ i.val < n+1):(𝟭 C).obj (SequenceArrows.maps S (reverse (Fin.mk (succ i.val) hsucc))).right=(S.maps (reverse i)).left  := by
  let h:=S.object_lemm

  let x:Fin (n+1):=(reverse (Fin.mk (succ i.val) hsucc))
  let y:Fin (n+1):= reverse i
  have hx: x= (reverse (Fin.mk (succ i.val) hsucc)):=by
    aesop
  have hy: y= reverse i:=by
    aesop
  rw [← hy]
  rw [← hx]
  let xv: ℕ := x.val
  have hxlt : xv < n:= by
    simp
    have hxlt1 : (reverse (Fin.mk (succ i.val) hsucc)).val= n - (i.val +1) := by
      unfold reverse
      simp
    rw [hxlt1]
    simp_all only [mod_succ, ge_iff_le, gt_iff_lt]
    apply tsub_lt_self
    · linarith
    · simp_all only [ge_iff_le, add_pos_iff, zero_lt_one, or_true]
  let xt: Fin (n) := Fin.mk xv hxlt
  have hxxt : Fin.castSucc xt= x := by
     rw [Fin.eq_iff_veq]
     dsimp
  rw [← hxxt]
  have hn : (SequenceArrows.maps S (Fin.castSucc xt)).right= (ComposableArrows.right ∘ S.maps ∘ Fin.castSucc) xt:=by
    aesop
  rw [hn]
  rw [← h]
  rw [Functor.id_obj]
  have hyt : Fin.succ xt= y := by
    simp
    rw [Fin.eq_iff_veq]
    simp
    unfold reverse
    simp
    rw [Nat.sub_succ]
    rw [← succ_eq_add_one]
    rw [succ_pred]
    intro hds
    rw [Nat.sub_eq_zero_iff_le] at hds
    linarith
  rw [← hyt]
  simp



def arrowFromSequence  {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i: Fin (n+1))  (h: succ i.val < n+1) : (S.maps (reverse (Fin.mk (succ i.val) h))).left ⟶ (S.maps (reverse i)).left:= (eqToHom (arrowFromSequence_source S i h)) ≫ (S.maps (reverse (Fin.mk (succ i.val) h))).hom  ≫ (eqToHom (arrowFromSequence_target S i h))



def toComposableArrowsWithSource  {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) : (i: Fin (n+1)) → (ComposibleArrowsWithSource C (i+1) (S.maps (reverse i)).left)
| zero => toComposibleArrowsSource₀ S
| Fin.mk (succ x) h =>  (toComposableArrowsWithSource S (Fin.mk (x) (by linarith))).precomp (arrowFromSequence S (Fin.mk (x) (by linarith)) h)


def toComposableArrows {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) : ComposableArrows C (succ n) := (toComposableArrowsWithSource S (Fin.last n)).val

-- We now want to look at some properties of this function.
def toComposableArrowsSub {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i : Fin (n+1)) : ComposableArrows C (succ i.val) := (toComposableArrowsWithSource S (i)).val

lemma zeroth_object {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i : Fin (n+1)) : (toComposableArrowsSub S i).obj 0 = (S.maps (reverse i)).left := by
  let h:= (toComposableArrowsWithSource S (i)).equal
  rw [h]
  aesop

lemma face_of {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i : Fin (n+1))  (hsucc: succ i.val < n+1):  (toComposableArrowsSub S i) = ComposableArrows.δ₀ (toComposableArrowsSub S (Fin.mk (succ i.val) hsucc)) := by
  rfl




lemma nth_object_reduce  {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i : Fin (n+1))  (hsucc: succ i.val < n+1) (j : Fin (succ i.val+1)):  (toComposableArrowsSub S i).obj j = (toComposableArrowsSub S (Fin.mk (succ i.val) hsucc)).obj (Fin.succ j)  := by
  rw [face_of]
  aesop
-- There is most likely a better way to write this





--Some stuff from previous committs:
open Finset Opposite SimplexCategory
def standardSimplex.edge (n : ℕ) (a b : Fin (n+1)) (hab : a ≤ b) : Δ[n] _[1] := by
  refine Hom.mk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab


def standardSimplex.edge01 {n: ℕ } (h : 0<n): ([1]:SimplexCategory)⟶  [n] := by
  refine standardSimplex.edge n ⟨0,?_⟩ ⟨1,?_⟩ (?_)
  · simp only [add_pos_iff, zero_lt_one, or_true]
  · simp
    exact h
  · simp

-- We now come up with the corresponding statement for composiblearrows without using eqToHom

lemma ext_succ_new {C : Type} [Category.{0,0} C] {F G : ComposableArrows C (n+1)} (hc: 0<(n+1))
    (h : F.δ₀ = G.δ₀) (wn : (nerve C).map (standardSimplex.edge01 hc).op F  = (nerve C).map (standardSimplex.edge01 hc).op G): F = G := by
    rename_i inst
    have hF0:  F.obj' 0 = ((nerve C).map (standardSimplex.edge01 hc).op F).obj 0 := by
        rfl
    have hF1:  F.obj' 1 = ((nerve C).map (standardSimplex.edge01 hc).op F).obj 1 := by
        rfl
    have h01 : (0: Fin (1+1))≤ (1 :Fin (1+1)):=by
      simp
    have hFt:  F.map' 0 1 = eqToHom hF0 ≫ ((nerve C).map (standardSimplex.edge01 hc).op F).map (homOfLE h01)≫ eqToHom hF1.symm := by
        simp only [nerve_obj, unop_op, len_mk, nerve_map, Quiver.Hom.unop_op, toCat_map,
          Int.Nat.cast_ofNat_Int, Int.rawCast, Int.cast_id, rawCast, cast_id, Int.ofNat_one,
          Int.ofNat_eq_coe, Int.ofNat_zero, eq_mp_eq_cast, id_eq, cast_eq, Fin.zero_eta, Fin.mk_one,
          ComposableArrows.map', ComposableArrows.obj', ComposableArrows.whiskerLeft_obj,
          eqToHom_refl, ComposableArrows.whiskerLeft_map, Category.comp_id, Category.id_comp]
        apply Eq.refl
    have hG0:  G.obj' 0 = ((nerve C).map (standardSimplex.edge01 hc).op G).obj 0 := by
        rfl
    have hG1:  G.obj' 1 = ((nerve C).map (standardSimplex.edge01 hc).op G).obj 1 := by
        rfl

    have hGt:  G.map' 0 1 = eqToHom hG0 ≫ ((nerve C).map (standardSimplex.edge01 hc).op G).map (homOfLE h01)≫ eqToHom hG1.symm := by
        simp only [nerve_obj, unop_op, len_mk, nerve_map, Quiver.Hom.unop_op, toCat_map,
          Int.Nat.cast_ofNat_Int, Int.rawCast, Int.cast_id, rawCast, cast_id, Int.ofNat_one,
          Int.ofNat_eq_coe, Int.ofNat_zero, eq_mp_eq_cast, id_eq, cast_eq, Fin.zero_eta, Fin.mk_one,
          ComposableArrows.map', ComposableArrows.obj', ComposableArrows.whiskerLeft_obj,
          eqToHom_refl, ComposableArrows.whiskerLeft_map, Category.comp_id, Category.id_comp]
        apply Eq.refl

    have h₀ : ( F.obj' 0 = G.obj' 0) :=  by
      rw [hF0,hG0]
      rw [wn]
    have  equate  {F1 G1 : ComposableArrows C (1)} (hx: F1=G1)  : F1.map (homOfLE h01)=  (by
     refine eqToHom (?_) ≫ G1.map (homOfLE h01) ≫ eqToHom (?_)
     · rw [hx]
     · rw [hx]
     ):= by
       aesop_subst hx
       simp_all only [eqToHom_refl, Category.comp_id, Category.id_comp]
    have w : ( F.map' 0 1 = eqToHom h₀ ≫ G.map' 0 1 ≫
      eqToHom (Functor.congr_obj h.symm 0)) := by
       rw [hFt,hGt]
       rw [Category.assoc]
       rw [Category.assoc]
       rw [eqToHom_trans]
       rw [← Category.assoc]
       rw [← Category.assoc]
       rw [← Category.assoc]
       rw [eqToHom_trans]
       rw [comp_eqToHom_iff]
       rw [Category.assoc]
       rw [Category.assoc]
       rw [eqToHom_trans]
       rw [eqToHom_comp_iff]
       rw [← Category.assoc]
       rw [← Category.assoc]
       rw [eqToHom_trans]
       rw [Category.assoc, (equate wn)]
    exact (ComposableArrows.ext_succ h₀ h w)


def edge (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : Finset.card {i, a, b} ≤ n) :
    Λ[n, i] _[1] := by
  refine ⟨standardSimplex.edge n a b hab, ?range⟩
  case range =>
    suffices ∃ x, ¬i = x ∧ ¬a = x ∧ ¬b = x by
      simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
        Set.mem_insert_iff, @eq_comm _ _ i, Set.mem_range, forall_true_left, not_forall, not_or,
        not_exists, Fin.forall_fin_two]
    contrapose! H
    replace H : univ ⊆ {i, a, b} :=
      fun x _ ↦ by simpa [or_iff_not_imp_left, eq_comm] using H x
    replace H := card_le_card H
    rwa [card_fin] at H

def vertex (n : ℕ) (i a : Fin (n+1))  (H : Finset.card {i, a} ≤ n) :
    Λ[n, i] _[0] := by
  refine ⟨const [n] a , ?range⟩
  case range =>
    suffices ∃ x, ¬i = x ∧ ¬a = x  by
      simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
        Set.mem_insert_iff, @eq_comm _ _ i, Set.mem_range, forall_true_left, not_forall, not_or,
        not_exists, Fin.forall_fin_one]
    contrapose! H
    replace H : univ ⊆ {i, a} :=
      fun x _ ↦ by simpa [or_iff_not_imp_left, eq_comm] using H x
    replace H := card_le_card H
    rwa [card_fin] at H
def vertexMk {n: ℕ} {i : Fin (n+1)} (α : Λ[n,i] _[0]) := by
 refine vertex n i  (α.val.toOrderHom 0) (?_)
 · have h:= α.prop
   have h1 : Set.range ⇑(asOrderHom α.val)  = {((asOrderHom α.val)  0)} := by
     unfold Set.range
     rw [Set.ext_iff]
     intro z
     simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
     apply Iff.intro
     · intro h2
       cases h2 with
        | intro w h => {
          fin_cases w; simp
          simp_all only [unop_op, len_mk, ne_eq, Set.union_singleton, Fin.zero_eta, true_or]
        }
     · intro a
       aesop_subst a
       simp_all only [unop_op, len_mk, ne_eq, Set.union_singleton, exists_apply_eq_apply]
   rw [h1] at h
   simp at h
   have h3 : ¬({i, (asOrderHom α.val) 0} = univ):= by
      rw [Finset.eq_univ_iff_forall]
      rw [Set.eq_univ_iff_forall] at h
      simp_all only [unop_op, len_mk, ne_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_forall, mem_insert, mem_singleton]
   rw [← card_eq_iff_eq_univ] at h3
   have h4 :{i, (asOrderHom α.val) 0}  ⊆ univ := by
      apply subset_univ
   apply card_le_card at h4
   simp at h4
   simp at h3
   have simp {x n :ℕ} (b1: x≤ n+1) (b2: ¬(x=n+1) ): x≤n :=by
      by_contra s
      have sx : x=n+1:= by
        linarith
      apply b2 sx
   apply (simp h4 h3)


def edgeMk {n: ℕ} {i : Fin (n+1)} (α : Λ[n,i] _[1]) := by
 refine edge n i (α.val.toOrderHom 0) (α.val.toOrderHom 1) (?_) (?_)
 · apply (α.val.toOrderHom).monotone'
   apply Fin.zero_le
 ·  have h:=α.prop
    have h1 : Set.range ⇑(asOrderHom α.val)  = {((asOrderHom α.val)  0), ((asOrderHom α.val) 1)} := by
      unfold Set.range
      rw [Set.ext_iff]
      intro z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      apply Iff.intro
      · intro h2
        cases h2 with
        | intro w h => {
          fin_cases w; simp
          simp_all only [unop_op, len_mk, ne_eq, Set.union_singleton, Fin.zero_eta, true_or]
          simp_all only [unop_op, len_mk, ne_eq, Set.union_singleton, Fin.zero_eta, true_or]
          aesop
        }
      · intro a
        simp_all only [unop_op, len_mk, ne_eq, Set.union_singleton]
        unhygienic aesop_cases a
        · aesop_subst h_1
          simp_all only [exists_apply_eq_apply]
        · aesop_subst h_1
          simp_all only [exists_apply_eq_apply]
    rw [h1] at h
    simp at h
    have h3 : ¬({i, (asOrderHom α.val) 0, (asOrderHom α.val) 1} = univ):= by
      rw [Finset.eq_univ_iff_forall]
      rw [Set.eq_univ_iff_forall] at h
      simp_all only [unop_op, len_mk, ne_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_forall, mem_insert, mem_singleton]
    rw [← card_eq_iff_eq_univ] at h3
    have h4 :{i, (asOrderHom α.val) 0, (asOrderHom α.val) 1}  ⊆ univ := by
      apply subset_univ
    apply card_le_card at h4
    simp at h4
    simp at h3
    have simp {x n :ℕ} (b1: x≤ n+1) (b2: ¬(x=n+1) ): x≤n :=by
      by_contra s
      have sx : x=n+1:= by
        linarith
      apply b2 sx
    apply (simp h4 h3)

lemma vertex_surjective {n: ℕ} {i : Fin (n+1)}  (α : Λ[n,i] _[0]): α = vertexMk α  := by
  rw [Subtype.ext_iff_val]
  apply Hom.ext'
  have x : ![(α.val.toOrderHom 0)]= Hom.toOrderHom (@Subtype.val (Δ[n].obj (op [0])) (fun x => Set.range ⇑(asOrderHom x) ∪ {i} ≠ Set.univ) (vertexMk α)):= by
    aesop
  have xt  : (Hom.toOrderHom α.val).toFun= (![(α.val.toOrderHom 0)]:Fin ( (succ 0)) → Fin (n + 1)):= by
     funext xp
     fin_cases xp
     rfl
  rw [← xt] at x
  rw [OrderHom.toFun_eq_coe] at x
  rw [FunLike.coe_fn_eq] at x
  exact x


lemma edge_surjective {n: ℕ} {i : Fin (n+1)}  (α : Λ[n,i] _[1]): α = edgeMk α  := by
  rw [Subtype.ext_iff_val]
  apply Hom.ext'
  have x : ![(α.val.toOrderHom 0), (α.val.toOrderHom 1)]= Hom.toOrderHom (@Subtype.val (Δ[n].obj (op [1])) (fun x => Set.range ⇑(asOrderHom x) ∪ {i} ≠ Set.univ) (edgeMk α)):= by
    rfl
  have xt  : (Hom.toOrderHom α.val).toFun= (![(α.val.toOrderHom 0), (α.val.toOrderHom 1)]:Fin (succ (succ 0)) → Fin (n + 1)):= by
    unhygienic ext
    fin_cases x_1 <;> simp
  rw [← xt] at x
  rw [OrderHom.toFun_eq_coe] at x
  rw [FunLike.coe_fn_eq] at x
  exact x


theorem card_le_three (a b c : Fin (n+1)) : card {a, b, c} ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)

theorem card_le_four (a b c d : Fin (n+1)) : card {a, b, c, d} ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ (card_le_three b c d))

def primitiveEdge {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    Λ[n, i] _[1] := by
  refine edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.coe_castSucc, Fin.val_succ, le_add_iff_nonneg_right, Nat.zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl|hn : n = 2 ∨ 2 < n := by
    rw [eq_comm, or_comm, ← le_iff_lt_or_eq]; omega
  · revert i j; decide
  · exact le_trans (card_le_three i _ _) hn



def standardSimplex.triangle {n : ℕ} (a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b ≤ c) : Δ[n] _[2] := by
  refine Hom.mk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, Matrix.tail_cons, Matrix.head_cons, true_and]





def triangle (n : ℕ) (i a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b≤ c) (H : Finset.card {i, a, b, c} ≤ n) :
    Λ[n, i] _[2] := by
  refine ⟨standardSimplex.triangle a b c hab hbc, ?range⟩
  case range =>
    suffices ∃ x, ¬i = x ∧ ¬a = x ∧ ¬b = x ∧ ¬c=x by
       rw [Set.union_singleton]
       simp [← Set.univ_subset_iff]
       simp [Set.subset_def]
       simp [not_or]
       have forall_fin_three {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 :=by
          apply Iff.intro
          · intro a
            simp_all only [and_self]
          · intro a i
            fin_cases i
            · tauto
            · tauto
            · tauto
       simp [forall_fin_three]
       simpa only [@eq_comm _ _ i]
    contrapose! H
    replace H : univ ⊆ {i, a, b, c} :=
      fun x _ ↦ by simpa [or_iff_not_imp_left, eq_comm] using H x
    replace H := card_le_card H
    rwa [card_fin] at H
--Lemmas relating the edges of triangles to specific edges.
lemma triangle_δ₂ (n : ℕ) (i a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b≤ c) (H : Finset.card {i, a, b, c} ≤ n) : Λ[n,i].map (SimplexCategory.δ 2).op (triangle n i a b c hab hbc H) = (by
refine edge n i a b hab (?_)
· have ht : ({i,a,b}: Finset (Fin (n + 1)))⊆ {i,a,b,c}:= by
    rw [subset_iff]
    intro x h
    rw [mem_insert] at h
    rw [mem_insert] at h
    rw [mem_singleton] at h
    rw [mem_insert]
    rw [mem_insert]
    rw [mem_insert]
    rw [mem_singleton]
    tauto
  apply card_le_card at ht
  exact le_trans ht H
)
:= by
  rw [Subtype.ext_iff_val]
  unfold edge
  simp
  have hv : (Λ[n,i].map (SimplexCategory.δ 2).op (triangle n i a b c hab hbc H)).val = Δ[n].map (SimplexCategory.δ 2).op (triangle n i a b c hab hbc H).val := by
    apply Eq.refl
  rw [hv]
  unfold triangle
  simp
  have B1 : Δ[n].map (δ 2).op (standardSimplex.triangle a b c hab hbc) =(δ 2) ≫ (standardSimplex.triangle a b c hab hbc) := by
    simp only [unop_op, len_mk, ne_eq, smallCategory_comp, Hom.comp]
    rfl
  rw [B1]
  apply Hom.ext'
  rw [← FunLike.coe_fn_eq]
  rw [← OrderHom.toFun_eq_coe]
  rw [← OrderHom.toFun_eq_coe]
  have B2 : (Hom.toOrderHom (standardSimplex.edge n a b hab)).toFun = ![a,b]:= by
    rfl
  rw [B2]
  unfold δ
  simp only [len_mk, mkHom, smallCategory_comp, Hom.comp, Hom.toOrderHom_mk, OrderHom.toFun_eq_coe, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe]
  unfold standardSimplex.triangle
  simp
  ext x
  fin_cases x
  · rfl
  · rfl

lemma triangle_δ₀ (n : ℕ) (i a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b≤ c) (H : Finset.card {i, a, b, c} ≤ n) : Λ[n,i].map (SimplexCategory.δ 0).op (triangle n i a b c hab hbc H) = (by
refine edge n i b c hbc (?_)
· have ht : ({i,b,c}: Finset (Fin (n + 1)))⊆ {i,a,b,c}:= by
    rw [subset_iff]
    intro x h
    rw [mem_insert] at h
    rw [mem_insert] at h
    rw [mem_singleton] at h
    rw [mem_insert]
    rw [mem_insert]
    rw [mem_insert]
    rw [mem_singleton]
    tauto
  apply card_le_card at ht
  exact le_trans ht H
)
:= by
  rw [Subtype.ext_iff_val]
  unfold edge
  simp
  have hv : (Λ[n,i].map (SimplexCategory.δ 0).op (triangle n i a b c hab hbc H)).val = Δ[n].map (SimplexCategory.δ 0).op (triangle n i a b c hab hbc H).val := by
    apply Eq.refl
  rw [hv]
  unfold triangle
  simp
  have B1 : Δ[n].map (δ 0).op (standardSimplex.triangle a b c hab hbc) =(δ 0) ≫ (standardSimplex.triangle a b c hab hbc) := by
    simp only [unop_op, len_mk, ne_eq, smallCategory_comp, Hom.comp]
    rfl
  rw [B1]
  apply Hom.ext'
  rw [← FunLike.coe_fn_eq]
  rw [← OrderHom.toFun_eq_coe]
  rw [← OrderHom.toFun_eq_coe]
  have B2 : (Hom.toOrderHom (standardSimplex.edge n b c hbc)).toFun = ![b,c]:= by
    rfl
  rw [B2]
  unfold δ
  simp only [len_mk, mkHom, smallCategory_comp, Hom.comp, Hom.toOrderHom_mk, OrderHom.toFun_eq_coe, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe]
  unfold standardSimplex.triangle
  simp
  ext x
  fin_cases x
  · rfl
  · rfl

lemma triangle_δ₁ (n : ℕ) (i a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b≤ c) (H : Finset.card {i, a, b, c} ≤ n) : Λ[n,i].map (SimplexCategory.δ 1).op (triangle n i a b c hab hbc H) = (by
refine edge n i a c (le_trans hab hbc) (?_)
· have ht : ({i,a,c}: Finset (Fin (n + 1)))⊆ {i,a,b,c}:= by
    rw [subset_iff]
    intro x h
    rw [mem_insert] at h
    rw [mem_insert] at h
    rw [mem_singleton] at h
    rw [mem_insert]
    rw [mem_insert]
    rw [mem_insert]
    rw [mem_singleton]
    tauto
  apply card_le_card at ht
  exact le_trans ht H
)
:= by
  rw [Subtype.ext_iff_val]
  unfold edge
  simp
  have hv : (Λ[n,i].map (SimplexCategory.δ 1).op (triangle n i a b c hab hbc H)).val = Δ[n].map (SimplexCategory.δ 1).op (triangle n i a b c hab hbc H).val := by
    apply Eq.refl
  rw [hv]
  unfold triangle
  simp
  have B1 : Δ[n].map (δ 1).op (standardSimplex.triangle a b c hab hbc) =(δ 1) ≫ (standardSimplex.triangle a b c hab hbc) := by
    simp only [unop_op, len_mk, ne_eq, smallCategory_comp, Hom.comp]
    rfl
  rw [B1]
  apply Hom.ext'
  rw [← FunLike.coe_fn_eq]
  rw [← OrderHom.toFun_eq_coe]
  rw [← OrderHom.toFun_eq_coe]
  have B2 : (Hom.toOrderHom (standardSimplex.edge n a c (le_trans hab hbc))).toFun = ![a,c]:= by
    rfl
  rw [B2]
  unfold δ
  simp only [len_mk, mkHom, smallCategory_comp, Hom.comp, Hom.toOrderHom_mk, OrderHom.toFun_eq_coe, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe]
  unfold standardSimplex.triangle
  simp
  ext x
  fin_cases x
  · rfl
  · rfl


set_option maxHeartbeats 300000

def triangleWithPrimitive {n:ℕ} (i k : Fin (n+1)) (γ : ℕ) (B1 : k.val + succ (succ γ) < n+1) (B3 : Finset.card {i, k, (Fin.mk (k.val + succ (succ γ)) B1)} ≤ n)  (h₀ : 0 < i) (hₙ : i < Fin.last (n))  (exp : ¬ (n=3∧ i=1 ∧ k=0 ∧ γ=1)):  Λ[n, i] _[2]:=by
refine (triangle n i k ⟨k.val + succ γ,?_⟩ ⟨k.val + succ (succ γ),B1⟩ (?_) (?_) (?_))
· linarith
· rw [Fin.le_iff_val_le_val]
  simp_all only [le_add_iff_nonneg_right, _root_.zero_le]
. simp_all only [Fin.mk_le_mk, add_le_add_iff_left]
  exact le_succ _
· by_cases h: 4≤n
  · exact le_trans (card_le_four i _ _ _) h
  ·
    match n with
    | zero => aesop
    | succ zero  => {
      simp_all only [zero_eq, not_le, one_lt_succ_succ, ge_iff_le]
      convert B3
      simp_all only [zero_eq, insert_eq_self, mem_singleton, Fin.mk.injEq, add_right_inj, succ.injEq, self_eq_add_right]
      linarith
    }
    | succ (succ zero) => {

      simp_all
      have hkv:  k.val =0 := by
        linarith
      have hk : k= 0 := by
        aesop
      rw [hkv] at B1
      simp at B1
      have hγ : γ =0 := by
        linarith
      have hiv : i.val = 1 := by
        rw [Fin.lt_def]  at h₀ hₙ
        simp at hₙ
        linarith
      have hi : i=1:=by
        aesop
      have h2 : Fin.mk (1+1) (by linarith)= (2 : Fin (succ (succ zero)+1)):= by
        aesop
      simp [hk,hkv,hγ,hi,succ_eq_add_one,h2 ] at B3
      aesop_subst [hi, hk, hγ]
      simp_all only [zero_eq, Fin.val_one, Fin.val_zero, lt_add_iff_pos_right, zero_lt_one, zero_add, Fin.mk_one,
        mem_insert, one_ne_zero, mem_singleton, true_or, or_true, insert_eq_of_mem, ge_iff_le]
      simp_all only [zero_eq, Fin.val_zero, zero_add, lt_add_iff_pos_right, zero_lt_one]
      exact B3
    }
    | succ (succ (succ zero)) => {
      match γ with
      | zero => {
         fin_cases k
         · simp_all
           fin_cases i
           · simp_all only [zero_eq, Fin.zero_eta, lt_self_iff_false]
           · simp
             apply card_le_three
           · simp
             apply card_le_three
           · simp [Fin.lt_def] at hₙ
         · simp_all
           fin_cases i
           · simp_all only [zero_eq, Fin.zero_eta, lt_self_iff_false]
           · simp
             apply card_le_three
           · simp
             apply card_le_three
           · simp [Fin.lt_def] at hₙ
         · simp at B1
         · simp at B1

      }
      | succ (zero) => {
        have hkv : k.val=0 := by
          linarith
        have hk : k=0 := by
          aesop
        simp_all [hkv,hk,succ_eq_add_one]
        fin_cases i
        · aesop
        · --n=3, i=1, k=0, γ=1
          simp at exp
        · simp
          apply card_le_three
        · simp [Fin.lt_def] at hₙ
      }
      | succ (succ _) => {
        simp [add_succ] at B1
        apply lt_of_succ_lt_succ at B1
        apply lt_of_succ_lt_succ at B1
        apply lt_of_succ_lt_succ at B1
        apply lt_of_succ_lt_succ at B1
        apply not_lt_zero' at B1
        tauto
      }
    }
    | succ (succ (succ (succ _))) => {
      simp [succ_eq_add_one, add_assoc] at h
    }

lemma triangleWithPrimitive_δ₁ {n:ℕ} (i k : Fin (n+1)) (γ : ℕ) (B1 : k.val + succ (succ γ) < n+1) (B3 : Finset.card {i, k, (Fin.mk (k.val + succ (succ γ)) B1)} ≤ n)  (h₀ : 0 < i) (hₙ : i < Fin.last (n))  (exp : ¬ (n=3∧ i=1 ∧ k=0∧ γ=1)) :   Λ[n,i].map (SimplexCategory.δ 1).op (triangleWithPrimitive i k γ B1 B3 h₀ hₙ exp) =  (by
refine edge n i k ⟨k.val + succ (succ γ), B1⟩  (?_) B3
· rw [Fin.le_def]
  simp
):= by
  unfold triangleWithPrimitive
  rw [triangle_δ₁]







---------------------------------
---------------------------------
---------------------------------
---------------------------------
---------------------------------

---------------------------------
---------------------------------
---------------------------------
---------------------------------
---------------------------------


---------------------------------
---------------------------------
---------------------------------
---------------------------------
---------------------------------


 lemma  horn_to_nerve_eq₁A {C : Type} [Category.{0,0} C]  (a b :Λ[3,1] ⟶ nerve C) (h₀ : 0 < 1) (hₙ : 1< Fin.last 3) (w: ∀ j: Fin (3), a.app (op [1]) (primitiveEdge h₀ hₙ j) = b.app (op [1]) (primitiveEdge h₀ hₙ j) ) : a.app (op [2]) (triangle 3 1 0 1 3 (by apply Fin.zero_le)  (by {
  rw [Fin.le_def]
  have h3 : (3:Fin (3+1)).val =3 := by
    rfl
  rw [h3]
  simp
  linarith
}) (by rfl)) = b.app (op [2]) (triangle 3 1 0 1 3 (by apply Fin.zero_le)   (by {
  rw [Fin.le_def]
  have h3 : (3:Fin (3+1)).val =3 := by
    rfl
  rw [h3]
  simp
  linarith
}) (by rfl)) := by


  have h1le3 : (1:Fin (3+1))≤ (3:Fin (3+1)) := by
      rw [Fin.le_def]
      have h3 : (3:Fin (3+1)).val =3 := by
        rfl
      rw [h3]
      simp
      linarith
  have h1le2 : (1:Fin (3+1))≤ (2:Fin (3+1)) := by
      rw [Fin.le_def]
      have h3 : (2:Fin (3+1)).val =2 := by
        rfl
      rw [h3]
      simp
      linarith
  have h2le3 : (2:Fin (3+1))≤ (3:Fin (3+1)) := by
      rw [Fin.le_def]
      have h3 : (3:Fin (3+1)).val =3 := by
        rfl
      rw [h3]
      simp
      linarith
  let tri := (triangle 3 1 0 1 3 (by apply Fin.zero_le)   (h1le3) (by rfl))
  have htri : tri = (triangle 3 1 0 1 3 (by apply Fin.zero_le)   (h1le3) (by rfl)) := by
    rfl

  rw [← htri]
  have hc2 : 0 < 1 + 1 := by
        simp

  have hedge : standardSimplex.edge01 hc2= δ 2 := by
                unfold standardSimplex.edge01
                apply Hom.ext'
                rw [← FunLike.coe_fn_eq]
                rw [← OrderHom.toFun_eq_coe]
                rw [← OrderHom.toFun_eq_coe]
                funext xp
                fin_cases xp
                · rfl
                · rfl

  apply (ext_succ_new hc2)
  · have D1 :  (a.app (op [2]) tri).δ₀ = (a.app (op [2]) ≫ (nerve C).map (δ 0).op ) tri := by
               rfl
    have D2 :  (b.app (op [2]) tri).δ₀ = (b.app (op [2]) ≫ (nerve C).map (δ 0).op ) tri := by
      rfl
    rw [D1, D2]
    rw [← a.naturality, ← b.naturality]
    rw [types_comp_apply]
    rw [types_comp_apply]
    have hCard₀ : Finset.card {(1:Fin (3+1)),(1:Fin (3+1)),(3:Fin (3+1))}≤ 3 := by
      aesop
    have hval₀ : (Λ[3, 1].map (δ 0).op tri)=edge 3 1 1 3 (h1le3) (hCard₀):= by
      rfl
    rw [hval₀]
    let tri2 := triangle 3 1 1 2 3 h1le2 h2le3 (by rfl)
    have tri2δ₁ :(Λ[3, 1].map (δ 1).op tri2) =edge 3 1 1 3 (h1le3) (hCard₀) := by
      simp
      rw [triangle_δ₁]
    rw [← tri2δ₁]
    rw [← (types_comp_apply (Λ[3, 1].map (δ 1).op) (a.app (op [1])))]
    rw [← (types_comp_apply (Λ[3, 1].map (δ 1).op) (b.app (op [1])))]
    rw [a.naturality, b.naturality]
    rw [types_comp_apply]
    rw [types_comp_apply]
    have CaseForTri2 : a.app (op [2]) tri2=b.app (op [2]) tri2:= by

      apply (ext_succ_new hc2)
      · have D1' :  (a.app (op [2]) tri2).δ₀ = (a.app (op [2]) ≫ (nerve C).map (δ 0).op ) tri2:= by
               rfl
        have D2' :  (b.app (op [2]) tri2).δ₀ = (b.app (op [2]) ≫ (nerve C).map (δ 0).op ) tri2 := by
          rfl
        rw [D1', D2']
        rw [← a.naturality, ← b.naturality]
        rw [types_comp_apply]
        rw [types_comp_apply]
        have tri2_δ₀ : Λ[3, 1].map (δ 0).op tri2 = primitiveEdge h₀ hₙ 2 := by
          rfl
        rw [tri2_δ₀]
        apply w
      · rw [← (types_comp_apply (a.app (op [2])) ((nerve C).map (standardSimplex.edge01 hc2).op ))]
        rw [← (types_comp_apply (b.app (op [2])) ((nerve C).map (standardSimplex.edge01 hc2).op ))]
        rw [← a.naturality, ← b.naturality]
        rw [types_comp_apply]
        rw [types_comp_apply]
        rw [hedge]
        have tri2_δ₂ : Λ[3, 1].map (δ 2).op tri2 = primitiveEdge h₀ hₙ 1 := by
          rw [triangle_δ₂]
          rfl
        rw [tri2_δ₂]
        apply w



    rw [CaseForTri2]
  · rw [← (types_comp_apply (a.app (op [2])) ((nerve C).map (standardSimplex.edge01 hc2).op ))]
    rw [← (types_comp_apply (b.app (op [2])) ((nerve C).map (standardSimplex.edge01 hc2).op ))]
    rw [← a.naturality, ← b.naturality]
    rw [types_comp_apply]
    rw [types_comp_apply]
    rw [hedge]
    have tri_δ₂ : Λ[3, 1].map (δ 2).op tri = primitiveEdge h₀ hₙ 0 := by
          rw [triangle_δ₂]
          rfl
    rw [tri_δ₂]
    apply w

lemma identity_edge (n:ℕ ) (k: Fin (n+1)) : standardSimplex.edge n k k (by rfl) = Δ[n].map (SimplexCategory.σ (0: Fin (1))).op (const [n] k ):= by
      have h1 :  Δ[n].map (SimplexCategory.σ (0: Fin (1))).op (const [n] k )=  (SimplexCategory.σ (0: Fin (1))) ≫ (const [n] k )  := by
          rfl
      rw [h1]
      unfold standardSimplex.edge
      apply Hom.ext'
      rw [← FunLike.coe_fn_eq]
      rw [← OrderHom.toFun_eq_coe]
      simp
      funext x
      fin_cases x
      · rfl
      · rfl

lemma  horn_to_nerve_eq₀  {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (n+1)} (a b :Λ[n,i] ⟶ nerve C) (h₀ : 0 < i) (hₙ : i < Fin.last n) (w: ∀ j: Fin (n), a.app (op [1]) (primitiveEdge h₀ hₙ j) = b.app (op [1]) (primitiveEdge h₀ hₙ j) ) :  ∀ α :Λ[n, i].obj (op [0]) , a.app (op [0]) α = b.app (op [0]) α := by

  have case_of_k : ∀ (k : Fin (n+1)) (hki : card {i,k} ≤ n) , a.app (op [0]) (vertex n i k hki)= b.app (op [0]) (vertex n i k hki):= by
    intro k
    match k with
    | zero => {
      intro hki
      have hnt : 0< n := by
        rw [Fin.lt_def] at hₙ
        simp at hₙ
        linarith
      have hv : (vertex n i 0 hki) = Λ[n,i].map (δ 1).op (primitiveEdge h₀ hₙ  (Fin.mk 0 hnt)):= by
        rw [Subtype.ext_iff_val]
        apply Hom.ext'
        rw [← FunLike.coe_fn_eq]
        rw [← OrderHom.toFun_eq_coe]
        rw [← OrderHom.toFun_eq_coe]
        funext xt
        fin_cases xt
        rfl
      simp [hv]
      rw [← (types_comp_apply (Λ[n,i ].map (δ 1).op) (a.app (op [0])))]
      rw [← (types_comp_apply (Λ[n,i].map (δ 1).op) (b.app (op [0])))]
      rw [a.naturality, b.naturality]
      rw [types_comp_apply]
      rw [types_comp_apply]
      rw [w]
    }
    | Fin.mk (succ x)  h => {
      intro hki
      have hnt : x< n := by
        linarith
      have hv : (vertex n i (Fin.mk (succ x)  h) hki) = Λ[n,i].map (δ 0).op (primitiveEdge h₀ hₙ  (Fin.mk x hnt)):= by
        rw [Subtype.ext_iff_val]
        apply Hom.ext'
        rw [← FunLike.coe_fn_eq]
        rw [← OrderHom.toFun_eq_coe]
        rw [← OrderHom.toFun_eq_coe]
        funext xt
        fin_cases xt
        rfl
      rw [hv]
      rw [← (types_comp_apply (Λ[n,i ].map (δ 0).op) (a.app (op [0])))]
      rw [← (types_comp_apply (Λ[n,i].map (δ 0).op) (b.app (op [0])))]
      rw [a.naturality, b.naturality]
      rw [types_comp_apply]
      rw [types_comp_apply]
      rw [w]
    }

  intro α
  let αv := vertex_surjective α
  unfold vertexMk at αv
  rw [αv]
  apply case_of_k
lemma  horn_to_nerve_eq₁ {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (n+1)} (a b :Λ[n,i] ⟶ nerve C) (h₀ : 0 < i) (hₙ : i < Fin.last n) (w: ∀ j: Fin (n), a.app (op [1]) (primitiveEdge h₀ hₙ j) = b.app (op [1]) (primitiveEdge h₀ hₙ j) ) :  ∀ α :Λ[n, i].obj (op [1]) , a.app (op [1]) α = b.app (op [1]) α := by
  intro α
  rw [edge_surjective α]
  -- Since α can be written as an edge, we just need to prove the result for edges.
  have N3 : ∀ (k: Fin (n+1)) (l: Fin (n+1)), (hab :k ≤ l) →   (Hab :Finset.card {i, k, l} ≤ n) → (a.app (op [1]) (edge n i k l hab Hab) =b.app (op [1]) (edge n i k l hab Hab)):= by
    intro k l hab Hab
    let γ := l.val -k.val
    -- We come up with a series of lemmas regarding α
    -- A1: l.val =k.val +α
    -- B1: k.val +α < n+1
    -- A2: l = Fin.mk (k.val+α) B1
    -- B2 : k≤Fin.mk (k.val+α) B1
    -- B3 : card {i, k, Fin.mk (k.val+α) B1} ≤ n

    have A1: l.val =k.val +γ := by
      simp
      nth_rewrite 1 [← Nat.sub_add_cancel hab]
      rw [add_comm]
    have B1 : k.val +γ < n+1 := by
      rw [← A1]
      simp
    have A2 : l = Fin.mk (k.val+γ) B1 := by
        aesop
    have B2 : k≤Fin.mk (k.val+γ) B1 := by
      rw [← A2]
      exact hab
    have B3 : card {i, k, Fin.mk (k.val+γ) B1} ≤ n := by
      rw [← A2]
      exact Hab

    have A3 : (edge n i k l hab Hab) = (edge n i k (Fin.mk (k.val+γ) B1) B2 B3):= by
      rw [Subtype.ext_iff_val]
      unfold edge
      simp
      apply Hom.ext'
      rw [← FunLike.coe_fn_eq]
      rw [← OrderHom.toFun_eq_coe]
      rw [← OrderHom.toFun_eq_coe]
      unfold standardSimplex.edge
      simp
      rw [← A2]

    rw [A3]
    have N4 : ∀ (γ': ℕ), (B1' : k.val +γ' < n+1) → (B2': k≤Fin.mk (k.val+γ') B1' ) → (B3' : card {i, k, Fin.mk (k.val+γ') B1'} ≤ n ) → (a.app (op [1]) (edge n i k { val := ↑k + γ', isLt := B1' } B2' B3') =b.app (op [1]) (edge n i k { val := ↑k + γ', isLt := B1' } B2' B3')):= by
      intro γ'
      induction γ' with
      | zero =>  {
        --This will need the 0 case
        intro B1' B2' B3'

        have hcard :   card {i, k} ≤ n := by
          have hsub : ({i,k} :Finset (Fin (n + 1))) ⊆ {i, k, Fin.mk (k.val +γ ) B1} := by
              rw [subset_iff]
              intro x
              intro h
              rw [Finset.mem_insert] at h
              rw [Finset.mem_singleton] at h
              rw [Finset.mem_insert]
              rw [Finset.mem_insert]
              rw [Finset.mem_singleton]
              tauto
          apply Finset.card_le_card at hsub
          exact (le_trans hsub B3)



        have hed : edge n i k { val := ↑k + zero, isLt := B1' } = edge n i k k := by
          rfl
        rw [hed]

        have hed : (edge n i k k B2' B3') = Λ[n,i].map  (σ 0).op (vertex n i k hcard):= by
          unfold edge
          rw [Subtype.ext_iff]
          simp
          rw [identity_edge]
          rfl
        rw [hed]
        rw [← (types_comp_apply (Λ[n, i].map (σ 0).op) (a.app (op [1])) )]
        rw [← (types_comp_apply (Λ[n, i].map (σ 0).op) (b.app (op [1])) )]
        rw [a.naturality, b.naturality]
        rw [types_comp_apply]
        rw [types_comp_apply]
        have HT : (a.app (op [0]) (vertex n i k hcard))=(b.app (op [0]) (vertex n i k hcard)):= by
          apply horn_to_nerve_eq₀
          exact w
        rw [HT]

      }
      | succ γ'' ih => {
        induction γ'' with
        | zero => {
          --primative case.
          intro B1' B2' B3'
          have hp1: k.val < n := by
            linarith
          have hP : edge n i k ⟨k.val + succ zero, B1'⟩ B2' B3'=  primitiveEdge h₀ hₙ ⟨k.val,hp1⟩ := by
              rfl
          rw [hP]
          apply w
        }
        | succ γ''' ih' => {
          --Compositions of
          -- We define the triangle
          intro B1''' B2''' B3'''
          by_cases exp : ¬ (n=3∧ i=1 ∧ k=0∧ γ'''=1)
          · let tri := triangleWithPrimitive i k γ''' B1''' B3''' h₀ hₙ exp
            have tri_δ₀ : (a.app (op [2]) (tri)).δ₀ = (b.app (op [2]) (tri)).δ₀ := by
              have D1 :  (a.app (op [2]) tri).δ₀ = (a.app (op [2]) ≫ (nerve C).map (δ 0).op ) tri := by
               rfl
              have D2 :  (b.app (op [2]) tri).δ₀ = (b.app (op [2]) ≫ (nerve C).map (δ 0).op ) tri := by
               rfl
              rw [D1, D2]
              rw [← a.naturality, ← b.naturality]
              rw [types_comp_apply]
              rw [types_comp_apply]
              simp
              -- This is where we need to introduce primiative edges
              have hγn : k.val +succ γ''' < n := by
                linarith
              have hTri : (Λ[n, i].map (δ 0).op (triangleWithPrimitive i k γ''' B1''' B3''' h₀ hₙ exp)) =  primitiveEdge h₀ hₙ ⟨ k.val +succ γ''',hγn⟩ := by
                rfl
              rw [hTri]
              apply w
            have hcc : 0 < 1+ 1:= by
              simp
            have tri_δ₂ : (nerve C).map (standardSimplex.edge01 hcc).op (a.app (op [2]) (tri))=(nerve C).map (standardSimplex.edge01 hcc).op (b.app (op [2]) (tri)):= by
              have D1 :  (nerve C).map (standardSimplex.edge01 hcc).op (a.app (op [2]) (tri)) = (a.app (op [2]) ≫ (nerve C).map (standardSimplex.edge01 hcc).op  ) (tri) := by
                rfl
              have D2 :  (nerve C).map (standardSimplex.edge01 hcc).op (b.app (op [2]) tri) = (b.app (op [2]) ≫ (nerve C).map (standardSimplex.edge01 hcc).op  ) (tri) := by
                rfl
              rw [D1, D2]
              rw [← a.naturality,←  b.naturality]
              rw [types_comp_apply]
              rw [types_comp_apply]
              have hedge : standardSimplex.edge01 hcc= δ 2 := by
                unfold standardSimplex.edge01
                apply Hom.ext'
                rw [← FunLike.coe_fn_eq]
                rw [← OrderHom.toFun_eq_coe]
                rw [← OrderHom.toFun_eq_coe]
                funext xp
                fin_cases xp
                · rfl
                · rfl

              rw [hedge]
              simp
              unfold triangleWithPrimitive
              rw [triangle_δ₂]
              apply ih
            have tri_eq :a.app (op [2]) (tri) = b.app (op [2]) (tri):= by
              -- ext_succ_new
              apply (ext_succ_new)
              · exact tri_δ₀
              case hc => simp
              case wn => exact tri_δ₂
            rw [← (triangleWithPrimitive_δ₁ i k γ''' B1''' B3''' h₀ hₙ exp)]
            have ha : a.app (op [1]) (Λ[n, i].map (δ 1).op (triangleWithPrimitive i k γ''' B1''' B3''' h₀ hₙ exp)) = (Λ[n, i].map (δ 1).op ≫ a.app (op [1])) ((triangleWithPrimitive i k γ''' B1''' B3''' h₀ hₙ exp)) := by
                rw [types_comp_apply]
            have hb : b.app (op [1]) (Λ[n, i].map (δ 1).op (triangleWithPrimitive i k γ''' B1''' B3''' h₀ hₙ exp)) = (Λ[n, i].map (δ 1).op ≫ b.app (op [1])) ((triangleWithPrimitive i k γ''' B1''' B3''' h₀ hₙ exp)) := by
                rw [types_comp_apply]

            rw [ha]
            rw [a.naturality]
            rw [types_comp_apply]
            rw [tri_eq]
            rw [hb]
            rw [b.naturality]
            rfl
          · simp at exp
            simp  [exp]
            have C1 : (0: Fin (3+1)) ≤ 1 := by
              apply Fin.zero_le

            have C2 : (1 : Fin (3+1))≤ 3 := by
              rw [Fin.le_def]
              have h3 : (3:Fin (3+1)).val =3 := by
                rfl
              rw [h3]
              simp
              linarith

            let C3 := triangle_δ₁ 3 1 0 1 3 C1 C2 (by rfl)
            match n with
            | 3 => {
              match i with
              | 1 => {
                have edge_eq : edge 3 1 0 { val := succ (succ 1), isLt := (_ : succ (succ 1) < 3 + 1) } =edge 3 1 0 3 := by
                  rfl
                rw [edge_eq]
                rw [← C3]
                have Na : a.app (op [1]) (Λ[3, 1].map (δ 1).op (triangle 3 1 0 1 3 C1 C2 (by rfl))) = ((Λ[3, 1].map (δ 1).op)≫(a.app (op [1]))) (triangle 3 1 0 1 3 C1 C2 (by rfl)) := by
                  rfl
                rw [Na]
                have Nb : b.app (op [1]) (Λ[3, 1].map (δ 1).op (triangle 3 1 0 1 3 C1 C2 (by rfl))) = ((Λ[3, 1].map (δ 1).op)≫(b.app (op [1]))) (triangle 3 1 0 1 3 C1 C2 (by rfl)) := by
                  rfl
                rw [Nb]
                rw [a.naturality]
                rw [b.naturality]
                rw [types_comp_apply]
                rw [types_comp_apply]
                rw [horn_to_nerve_eq₁A]
                · exact h₀
                · exact hₙ
                · exact w

              }


            }







        }
      }
    apply (N4 γ B1 B2 B3)


  simp_all only [nerve_obj, unop_op, len_mk, zero_eq]
  apply N3



theorem horn_to_nerve_eq {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (n+1)} (a b :Λ[n,i] ⟶ nerve C) (h₀ : 0 < i) (hₙ : i < Fin.last n) (w: ∀ j: Fin (n), a.app (op [1]) (primitiveEdge h₀ hₙ j) = b.app (op [1]) (primitiveEdge h₀ hₙ j) ) : a=b :=by
  --We introduce a new goal.
  have N1 : ∀ (mO : SimplexCategoryᵒᵖ) (α : Λ[n,i].obj mO) , a.app mO α = b.app mO α:= by
    --We introduce a new goal.
    have N2 :  ∀ (m : ℕ ) (α : Λ[n,i].obj (op [m])) , a.app (op [m]) α = b.app (op [m]) α:=by
      -- we do induction on m
      intro m
      induction' m with mp hp
      · --m=0 case
        intro α
        apply horn_to_nerve_eq₀
        · exact w


      · induction' mp with mpp
        · --m=1 case
          rw [← Nat.one_eq_succ_zero]
          apply (horn_to_nerve_eq₁)
          exact w


        · --General case
          intro α
          have hcc : 0 < succ (succ mpp):= by
                    simp
          have case_δ₀ : (a.app (op [succ (succ mpp)]) α).δ₀ = (b.app (op [succ (succ mpp)]) α).δ₀ := by
            have D1 :  (a.app (op [succ (succ mpp)]) α).δ₀ = (a.app (op [succ (succ mpp)]) ≫ (nerve C).map (δ 0).op ) α := by
              rfl
            have D2 :  (b.app (op [succ (succ mpp)]) α).δ₀ = (b.app (op [succ (succ mpp)]) ≫ (nerve C).map (δ 0).op ) α := by
              rfl
            rw [D1, D2]
            rw [← a.naturality,←  b.naturality]
            rw [types_comp_apply]
            rw [types_comp_apply]
            apply hp
          have case_first_edge : (nerve C).map (standardSimplex.edge01 hcc).op (a.app (op [succ (succ mpp)]) α) = (nerve C).map (standardSimplex.edge01 hcc).op (b.app (op [succ (succ mpp)]) α) := by
            have D1 :  (nerve C).map (standardSimplex.edge01 hcc).op (a.app (op [succ (succ mpp)]) α) = (a.app (op [succ (succ mpp)]) ≫ (nerve C).map (standardSimplex.edge01 hcc).op  ) α := by
              rfl
            have D2 :  (nerve C).map (standardSimplex.edge01 hcc).op (b.app (op [succ (succ mpp)]) α) = (b.app (op [succ (succ mpp)]) ≫ (nerve C).map (standardSimplex.edge01 hcc).op  ) α := by
              rfl
            rw [D1, D2]
            rw [← a.naturality,←  b.naturality]
            rw [types_comp_apply]
            rw [types_comp_apply]
            apply (horn_to_nerve_eq₁)
            exact w

          apply (ext_succ_new hcc case_δ₀ case_first_edge)



    --Solving the goal N1 given N2
    intro mO
    let m0i:ℕ  := (unop mO).len
    have R1 : (op ([m0i]:SimplexCategory)) = mO := by
      simp_all only [ unop_op, len_mk, mk_len, op_unop]
    have R2 : ∀ (α : Λ[n,i].obj (op [m0i])) , a.app (op [m0i]) α = b.app (op [m0i]) α:= by
      exact N2 m0i
    rw [R1] at R2
    exact R2


  --Solving the original goal given N1
  unhygienic ext
  rw [N1]


---------------------------------
---------------------------------
---------------------------------
---------------------------------
---------------------------------
--We construct sequence arrows from a map of horns


def hornMapToSequenceArrows_maps {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (succ n+1)} (a : Λ[succ n,i] ⟶ nerve C)  (h₀ : 0 < i) (hₙ : i < Fin.last (succ n))  (j : Fin (n+1) ): ComposableArrows C 1 := (a.app (op [1]) (primitiveEdge h₀ hₙ j))

lemma hornMapToSequenceArrows_lemma {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (succ n+1)} (a : Λ[succ n,i] ⟶ nerve C)  (h₀ : 0 < i) (hₙ : i < Fin.last (succ n))  : ComposableArrows.left ∘ hornMapToSequenceArrows_maps a h₀ hₙ ∘ Fin.succ = ComposableArrows.right ∘ hornMapToSequenceArrows_maps a h₀ hₙ ∘ Fin.castSucc := by
  funext j
  simp
  -- This will follow by some naturality argument.
  unfold hornMapToSequenceArrows_maps
  rename_i inst
  have h1 : @ComposableArrows.right C inst 1 (a.app (op [1]) (primitiveEdge h₀ hₙ (Fin.castSucc j))) = ((a.app (op [1])  ≫ (nerve C).map (δ 0).op) ((primitiveEdge h₀ hₙ (Fin.castSucc j)))).obj 0 := by
    rfl
  have h0 : (a.app (op [1]) (primitiveEdge h₀ hₙ (Fin.succ j))).left= ((a.app (op [1])≫ (nerve C).map (δ 1).op) ( (primitiveEdge h₀ hₙ (Fin.succ j)))).obj 0 := by
    rfl
  rw [h0,h1]
  rw [← a.naturality]
  rw [← a.naturality]
  rw [types_comp_apply]
  rw [types_comp_apply]
  have R1 :( Λ[succ n, i].map (δ 1).op (primitiveEdge h₀ hₙ (Fin.succ j))).val = Δ[succ n].map (δ 1).op (primitiveEdge h₀ hₙ (Fin.succ j)).val:= by
    rfl
  have R0 :( Λ[succ n, i].map (δ 0).op (primitiveEdge h₀ hₙ (Fin.castSucc j))).val = Δ[succ n].map (δ 0).op (primitiveEdge h₀ hₙ (Fin.castSucc j)).val:= by
    rfl
  have R11 : Δ[succ n].map (δ 1).op (primitiveEdge h₀ hₙ (Fin.succ j)).val =    SimplexCategory.const [succ n] (Fin.castSucc (Fin.succ j)):= by
    unfold  primitiveEdge
    simp
    unfold edge
    simp
    apply Hom.ext
    simp
    rw [← FunLike.coe_fn_eq]
    funext xt
    fin_cases xt
    rfl
  have R01 : Δ[succ n].map (δ 0).op (primitiveEdge h₀ hₙ (Fin.castSucc j)).val=    SimplexCategory.const [succ n] (Fin.castSucc (Fin.succ j)):= by
    unfold  primitiveEdge
    simp
    unfold edge
    simp
    apply Hom.ext
    simp
    rw [← FunLike.coe_fn_eq]
    funext xt
    fin_cases xt
    rfl
  have N1 : Λ[succ n, i].map (δ 1).op (primitiveEdge h₀ hₙ (Fin.succ j))= Λ[succ n, i].map (δ 0).op (primitiveEdge h₀ hₙ (Fin.castSucc j)):= by
    rw [Subtype.ext_iff]
    rw [R1]
    rw [R0]
    rw [R11]
    rw [R01]
  rw [N1]



def hornMapToSequenceArrows {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (succ n+1)} (a : Λ[succ n,i] ⟶ nerve C)  (h₀ : 0 < i) (hₙ : i < Fin.last (succ n)):  SequenceArrows C n where
  maps := hornMapToSequenceArrows_maps a h₀ hₙ
  object_lemm := hornMapToSequenceArrows_lemma a h₀ hₙ

def toFunctor (n  :ℕ  ) (m:SimplexCategoryᵒᵖ ) (f: Δ[n].obj (m)) : Fin ((unop m).len+1) ⥤ Fin (n+1):= toCat.map f

def σ  {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (succ n+1)} (a : Λ[succ n,i] ⟶ nerve C)  (h₀ : 0 < i) (hₙ : i < Fin.last (succ n)) : Δ[succ n] ⟶ (nerve C) where
  app m f := ComposableArrows.whiskerLeft (toComposableArrows (hornMapToSequenceArrows a h₀ hₙ)) (toFunctor (succ n) m f)

lemma castSucc_le_succ {n:ℕ } (j :Fin (succ n)) : (Fin.castSucc j)≤ (Fin.succ j) := by
    rw [Fin.le_def]
    simp
lemma Succ_le_succ {n:ℕ } (j :Fin (succ n)) : (Fin.succ j)≤ (Fin.succ j) := by
    rw [Fin.le_def]
lemma castSucc_le_Castsucc {n:ℕ } (j :Fin (succ n)) : (Fin.castSucc j)≤ (Fin.castSucc j) := by
    rw [Fin.le_def]

def jth_edge_old {n: ℕ } (j :Fin (succ n))  :  Fin (1+ 1) ⥤ Fin (succ n + 1) := toFunctor (succ n) (op [1]) (standardSimplex.edge (succ n) (Fin.castSucc j) (Fin.succ j) (castSucc_le_succ j))


def jth_edge_new_obj {n: ℕ } (j :Fin (succ n)) : Fin (1+1)→ Fin (succ n+1)
| 0 => Fin.castSucc j
| 1 => Fin.succ j

lemma  jth_edge_new_LE {n: ℕ } (j :Fin (succ n)) (l m :Fin (1+1)) (hlm : l≤ m) : jth_edge_new_obj j l ≤ jth_edge_new_obj j m := by
  match l, m with
  | 0, 0 => rw [Fin.le_def]
  | 1, 1 => rw [Fin.le_def]
  | 0, 1 => {unfold jth_edge_new_obj
             simp_all only [Fin.zero_le, ge_iff_le]
             split
             · simp_all only [Fin.zero_eta]
               split
               · simp_all only [Fin.zero_eta, one_ne_zero]
               · simp_all only [Fin.mk_one]
                 simp [Fin.le_iff_val_le_val]
             · simp_all only [Fin.mk_one, zero_ne_one]
            }


def jth_edge {n: ℕ } (j :Fin (succ n))  :  Fin (1+ 1) ⥤ Fin (succ n + 1) where
 obj k := jth_edge_new_obj j k
 map {l m} hlm := homOfLE (jth_edge_new_LE j l m (leOfHom hlm))



 lemma castSucc_le_succ_0 {n:ℕ } (j :Fin ( n)) : (Fin.castSucc j)≤ (Fin.succ j) := by
    rw [Fin.le_def]
    simp
def jth_edge_0 {n: ℕ } (j :Fin ( n))  :  Fin (1+ 1) ⥤ Fin ( n + 1) := toFunctor ( n) (op [1]) (standardSimplex.edge ( n) (Fin.castSucc j) (Fin.succ j) (castSucc_le_succ_0 j))


lemma jth_edge_Precomp {C : Type} [Category.{0,0} C] {n:ℕ} {X: C} (S : ComposableArrows C n) (f : X⟶ S.left ): jth_edge 0 ⋙(S.precomp f)= ComposableArrows.mk₁ f:= by
    have hobj : ∀ Y : Fin (1+1) , (jth_edge 0 ⋙(S.precomp f)).obj Y = (ComposableArrows.mk₁ f).obj Y := by
        intro Y
        fin_cases Y
        · rfl
        · rfl
    have hmap : ∀ (Y Z : Fin (1+1)) (h : Y⟶ Z), (jth_edge 0 ⋙(S.precomp f)).map h = eqToHom (hobj Y) ≫(ComposableArrows.mk₁ f).map h≫ eqToHom (hobj Z).symm := by
      intro Y Z
      fin_cases Y
      · fin_cases Z
        · simp
          aesop
        · simp
          aesop
      simp
      fin_cases Z
      · intro h
        simp at h
        let l := leOfHom h
        simp at l

      ·
        intro h
        simp_all only [Fin.mk_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, Functor.comp_obj,
          ComposableArrows.precomp_obj, eqToHom_refl, Category.comp_id]
        simp_all only [Functor.comp_obj, ComposableArrows.precomp_obj, ComposableArrows.mk₁_obj,
          ComposableArrows.Mk₁.obj, Fin.mk_one]
        dsimp
        apply ComposableArrows.Precomp.map_id

    apply (CategoryTheory.Functor.ext hobj hmap)

lemma mk₁_eqToHom {C : Type} [Category.{0,0} C]  {X Y Z: C} (f : X⟶ Y) (eq : Y=Z) : ComposableArrows.mk₁ (f ≫ eqToHom eq)= ComposableArrows.mk₁ f := by
  aesop_subst eq
  simp_all only [eqToHom_refl, Category.comp_id]

lemma mk₁_invs {C : Type} [Category.{0,0} C] ( S: ComposableArrows C 1) : ComposableArrows.mk₁ (S.hom)= S := by
  have hobj : ∀ Y : Fin (1+1) , (ComposableArrows.mk₁ (S.hom)).obj Y = S.obj Y := by
        intro Y
        fin_cases Y
        · rfl
        · rfl
  have hmap : ∀ (Y Z : Fin (1+1)) (h : Y⟶ Z), (ComposableArrows.mk₁ (S.hom)).map h = eqToHom (hobj Y) ≫(S).map h≫ eqToHom (hobj Z).symm := by
      intro Y Z
      fin_cases Y
      · fin_cases Z
        ·
          intro h
          simp_all only [Fin.zero_eta, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, ComposableArrows.mk₁_map,
            ComposableArrows.Mk₁.map, eqToHom_refl, Category.comp_id, Category.id_comp]
          simp_all only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
          symm
          apply S.map_id
        · simp
          aesop
      simp
      fin_cases Z
      · intro h
        simp at h
        let l := leOfHom h
        simp at l

      ·
        intro h
        simp_all only [Fin.mk_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, eqToHom_refl, Category.comp_id]
        simp_all only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
        symm
        apply S.map_id

  apply (CategoryTheory.Functor.ext hobj hmap)

lemma jth_edge_zero_id : @jth_edge 0 0= Functor.id (Fin (1+1)):= by
  have hobj : ∀ Y : Fin (1+1) , ( @jth_edge 0 0).obj Y = (Functor.id (Fin (1+1))).obj Y := by
        intro Y
        fin_cases Y
        · rfl
        · rfl
  apply (CategoryTheory.Functor.ext hobj)

lemma N2 {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) :∀ i : Fin (n+1) , jth_edge 0 ⋙ toComposableArrowsSub S i = (S.maps (reverse i)) := by
     intro i
     unfold toComposableArrowsSub
     unfold toComposableArrowsWithSource
     split
     · simp
       unfold  toComposibleArrowsSource₀
       simp
       rw [mk₁_invs]
       have hr : reverse (0: Fin (n+1)) = Fin.last n := by
        rfl
       rw [hr]
       rw [jth_edge_zero_id]
       aesop

     · unfold ComposibleArrowsWithSource.precomp
       simp
       rw [jth_edge_Precomp]
       simp only [arrowFromSequence]
       simp
       rw [mk₁_eqToHom]
       apply mk₁_invs


lemma jth_edge_is {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n)   : ∀ (j : Fin (succ n)),  (jth_edge j ⋙ toComposableArrows S ) = SequenceArrows.maps S j := by

  have N1 (k:ℕ) :∀  (i : Fin (n+1)) (hki: k < i.val +1) (hk : i.val-k < n+1), jth_edge ⟨k, hki ⟩   ⋙ (toComposableArrowsSub S i)=jth_edge ⟨ 0, by aesop ⟩ ⋙ (toComposableArrowsSub S (Fin.mk (i.val - k) hk)) := by

      induction k with
      | zero => simp
      | succ t ih => {
        intro i
        match (i : Fin (n+1)) with
       | (zero: Fin (n+1)) => simp
       | Fin.mk (succ im1) A4 => {
         simp
         intro hki A3
         have B1 : im1< n+1 :=  by
            linarith
         have A5 : t< im1+1 :=  by
            linarith
         have A3 : (im1-t) < n+1 := by
             linarith
         simp [succ_eq_add_one]
         let ihs := ih ⟨im1, B1⟩ A5 A3
         rw [face_of S ⟨im1, B1⟩ A4] at ihs
         simp at ihs
         simp [succ_eq_add_one] at ihs
         symm at ihs
         unfold ComposableArrows.δ₀ at ihs
         unfold ComposableArrows.δ₀Functor at ihs
         unfold ComposableArrows.whiskerLeftFunctor  at ihs
         simp at ihs
         unfold ComposableArrows.whiskerLeft  at ihs
         have R1 : jth_edge { val := t, isLt := A5 } ⋙ Fin.succFunctor (im1 + 1 + 1) ⋙ toComposableArrowsSub S { val := im1 + 1, isLt := A4 } = (jth_edge { val := t, isLt := A5 } ⋙ Fin.succFunctor (im1 + 1 + 1) )⋙ toComposableArrowsSub S { val := im1 + 1, isLt := A4 }:= by
            apply Eq.refl
         rw [R1] at ihs
         have R2: (jth_edge { val := t, isLt := A5 } ⋙ Fin.succFunctor (im1 + 1 + 1)) =  jth_edge { val := t + 1, isLt := hki } := by
           rw [Functor.comp]
           have h_object : ∀ X : Fin (1+1), (jth_edge { val := t, isLt := A5 } ⋙ Fin.succFunctor (im1 + 1 + 1)).obj X =  (jth_edge { val := t + 1, isLt := hki }).obj X := by
              intro X
              rw [Functor.comp]
              simp
              fin_cases X
              · simp
                unfold jth_edge
                simp
                unfold jth_edge_new_obj
                simp
              · simp
                unfold jth_edge
                simp
                unfold jth_edge_new_obj
                simp
           apply (CategoryTheory.Functor.ext h_object)

         rw [R2] at ihs
         rw [← ihs]
         have R3 : im1 + 1 - (t + 1) = im1 - t := by
            rw [succ_sub_succ_eq_sub]
         let A6 := @Eq.substr Prop (fun x => x) (im1 - t < n + 1) (im1 + 1 - (t + 1) < n + 1)  (congrFun (congrArg LT.lt (succ_sub_succ_eq_sub im1 t)) (n + 1)) A3




         have R7 : HEq  (toComposableArrowsSub S (Fin.mk ( im1 -  t) A3))  (toComposableArrowsSub S (Fin.mk (succ im1 - succ t) A6))  := by
            simp_all only [Fin.zero_eta, succ_sub_succ_eq_sub, cast_eq]
            congr 1
            simp_all only [succ_sub_succ_eq_sub]

         congr 1
         · simp
         · rw [R3]
         congr 1
         · simp
         have R8 : (im1 - t) = (im1 + 1 - (t + 1)) := by
            simp
         simp [succ_eq_add_one]
         have intsub {a b : ℕ } (eq : a= b)  :@HEq (Fin (a+1)) 0 (Fin (b+1)) 0 := by
             congr
         have R9: @HEq (Fin (im1 - t + 1)) 0 (Fin (im1 + 1 - (t + 1) + 1)) 0 := by
           exact  (intsub R8)

         exact R9




       }


       }



  simp [N2] at N1
  intro j
  change jth_edge j ⋙toComposableArrowsSub S (Fin.last n) = SequenceArrows.maps S j
  have hkj : j.val <  (Fin.last n).val +1 := by
    aesop
  have hjval : j = Fin.mk j.val hkj := by
    aesop
  have E4 : (Fin.last n).val - j.val < n + 1 := by
    simp
    have fs (a4 b4 : ℕ ) : a4-b4 < a4+1 := by
        cases a4
        · simp_all only [zero_eq, ge_iff_le, _root_.zero_le, tsub_eq_zero_of_le, zero_add, zero_lt_one]
        · apply Nat.sub_lt_succ
    exact (fs n j.val)
  rw [hjval]
  let N1S := N1 j.val (Fin.last n) hkj E4
  rw [N1S]
  have hr : reverse { val := ↑(Fin.last n) - ↑j, isLt := E4 } = j := by
    unfold reverse
    simp
    rw [Fin.eq_mk_iff_val_eq]
    simp
    rw [tsub_tsub_cancel_of_le]
    linarith

  rw [hr]
  simp












lemma zeroth_object_2 {C : Type} [Category.{0,0} C] {n:ℕ} (S : SequenceArrows C n) (i : Fin (n+1)) : (toComposableArrowsSub S i).obj 0 = (S.maps (reverse i)).left := by
  let h:= (toComposableArrowsWithSource S (i)).equal
  rw [h]
  aesop
lemma equiv_def {n: ℕ } (j :Fin (succ n))  :jth_edge j =jth_edge_old j := by
    have hobj : ∀ X : Fin (1+1) ,(jth_edge j).obj X=(jth_edge_old (j : Fin (succ n))).obj X:= by
        intro X
        fin_cases X
        · simp
          unfold jth_edge
          simp
          unfold jth_edge_new_obj
          simp
          rfl
        · simp
          unfold jth_edge
          simp
          unfold jth_edge_new_obj
          simp
          rfl
    apply (CategoryTheory.Functor.ext hobj)

theorem primiative_case {C : Type} [Category.{0,0} C] {n:ℕ} {i:Fin (succ n+1)} (a : Λ[succ n,i] ⟶ nerve C)  (h₀ : 0 < i) (hₙ : i < Fin.last (succ n)) : ∀ j: Fin (succ n), a.app (op [1]) (primitiveEdge h₀ hₙ j) = ((hornInclusion (succ n) i)≫ (σ a h₀ hₙ) ).app (op [1]) (primitiveEdge h₀ hₙ j) := by
    intro j

    let e := standardSimplex.edge (succ n) (Fin.castSucc j) (Fin.succ j) (castSucc_le_succ j)
    have R1 : (hornInclusion (succ n) i ≫ σ a h₀ hₙ).app (op [1]) (primitiveEdge h₀ hₙ j) = (σ a h₀ hₙ).app (op [1]) e := by
      rfl
    rw [R1]
    have R2 : (σ a h₀ hₙ).app (op [1]) e= (hornMapToSequenceArrows a h₀ hₙ).maps j:= by
      unfold σ
      simp
      unfold  ComposableArrows.whiskerLeft

      change (jth_edge_old j ⋙ toComposableArrows (hornMapToSequenceArrows a h₀ hₙ) ) = SequenceArrows.maps (hornMapToSequenceArrows a h₀ hₙ) j
      rw [← equiv_def]
      rw [(jth_edge_is (hornMapToSequenceArrows a h₀ hₙ) j)]
    rw [R2]
    rfl





theorem lift {C : Type } [Category.{0,0} C] {n:ℕ} {i:Fin (succ n+1)} (a : Λ[succ n,i] ⟶ nerve C)  (h₀ : 0 < i) (hₙ : i < Fin.last (succ n)) : a = (hornInclusion (succ n) i)≫ (σ a h₀ hₙ) := by
  apply (horn_to_nerve_eq a ((hornInclusion (succ n) i)≫ (σ a h₀ hₙ)) h₀ hₙ (primiative_case  a h₀ hₙ ) )
