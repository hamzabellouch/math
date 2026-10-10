import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NervePrismPatch
import OAI.Topology.ArtinGroups.Harmonic.PredAboveSuccSucc

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismPrefix_mono {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) {k l:Fin (n+1)} (hkl:k≤l) :
    prismPrefix z k≤prismPrefix z l :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iio_subset_Iio hkl) (fun index _ _=>z.weights_nonneg index)

lemma prismRight_mono {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) {k l:Fin (n+1)} (hkl:k≤l) :
    prismPrefix z k+z.weights k≤prismPrefix z l+z.weights l := by
  rw [prismPrefix_add,prismPrefix_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hkl) (fun index _ _=>z.weights_nonneg index)

lemma prismCell_between {n:ℕ} (p:Convexity.StdSimplex ℝ (Fin (n+1))×I) {k j l:Fin (n+1)}
    (hk:p∈PrismCell k) (hl:p∈PrismCell l) (hkj:k≤j) (hjl:j≤l) : p∈PrismCell j :=
  ⟨(prismPrefix_mono p.1 hjl).trans hl.1,hk.2.trans (prismRight_mono p.1 hkj)⟩

lemma nervePrismPatch_adjacent {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k l:Fin (n.len+1)) (hkl:l.val=k.val+1)
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hk:p∈PrismCell k) (hl:p∈PrismCell l) :
    nervePrismPatch f g h x k p=nervePrismPatch f g h x l p := by
  have hp:p.2.val=prismPrefix p.1 k+p.1.weights k:=by
    have hh:=hl.1
    rw [prismPrefix_step p.1 k l hkl] at hh
    exact le_antisymm hk.2 hh
  change realizeSimplex _ (nervePrism f g h x k) (prismSimplex k p)=
    realizeSimplex _ (nervePrism f g h x l) (prismSimplex l p)
  rw [prismSimplex_face_right k p hp,prismSimplex_face_adjacent k l hkl p hp]
  have h₁:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ k.succ) (nervePrism f g h x k) p.1
  have h₂:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ k.succ) (nervePrism f g h x l) p.1
  rw [nervePrism_face_adjacent f g h x k l hkl] at h₂
  exact h₁.symm.trans h₂

lemma nervePrismPatch_agree {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k l:Fin (n.len+1)) (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I)
    (hk:p∈PrismCell k) (hl:p∈PrismCell l) :
    nervePrismPatch f g h x k p=nervePrismPatch f g h x l p := by
  have aux:∀l:Fin (n.len+1),∀k≤l,p∈PrismCell k→p∈PrismCell l→
      nervePrismPatch f g h x k p=nervePrismPatch f g h x l p:=by
    intro l
    induction l using Fin.induction with
    | zero =>
      intro k hkl _ _
      have he:k=0:=le_antisymm hkl (Fin.zero_le _)
      rw [he]
    | succ j ih =>
      intro k hkl hk hl
      by_cases hh:k≤j.castSucc
      · have hc:p∈PrismCell j.castSucc:=prismCell_between p hk hl hh (by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]; omega)
        exact (ih k hh hk hc).trans (nervePrismPatch_adjacent f g h x j.castSucc j.succ
          (by simp only [Fin.val_succ,Fin.val_castSucc]) p hc hl)
      · have he:k=j.succ:=by
          apply Fin.ext
          simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hh hkl ⊢
          omega
        rw [he]
  rcases le_total k l with hkl|hlk
  · exact aux l k hkl hk hl
  · exact (aux k l hlk hl hk).symm

noncomputable def nervePrismValue {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) : |nerve Q| :=
  nervePrismPatch f g h x (prismCell_cover p).choose p

lemma nervePrismValue_eq {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k:Fin (n.len+1)) (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    nervePrismValue f g h x p=nervePrismPatch f g h x k p :=
  nervePrismPatch_agree f g h x _ _ p (prismCell_cover p).choose_spec hp

noncomputable def nervePrismSimplex {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len+1)),C(I,|nerve Q|)) :=
  (⟨nervePrismValue f g h x,by
    apply (locallyFinite_of_finite (fun k:Fin (n.len+1)=>PrismCell k)).continuous
    · exact Set.iUnion_eq_univ_iff.mpr prismCell_cover
    · exact prismCell_closed
    · intro k
      apply (nervePrismPatch f g h x k).continuous.continuousOn.congr
      intro p hp
      exact nervePrismValue_eq f g h x k p hp⟩ : C(Convexity.StdSimplex ℝ (Fin (n.len+1))×I,|nerve Q|)).curry

lemma nervePrismSimplex_natural {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n m:SimplexCategory} (u:n⟶m)
    (x:(nerve P).obj (op m)) (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) (t:I) :
    nervePrismSimplex f g h ((nerve P).map u.op x) z t=
      nervePrismSimplex f g h x (Convexity.StdSimplex.map u.toOrderHom z) t := by
  obtain ⟨k,hk⟩:=prismCell_cover (z,t)
  change nervePrismValue f g h ((nerve P).map u.op x) (z,t)=
    nervePrismValue f g h x (Convexity.StdSimplex.map u.toOrderHom z,t)
  rw [nervePrismValue_eq f g h _ k _ hk,
    nervePrismValue_eq f g h x _ _ (prismCell_natural u k _ hk)]
  exact nervePrismPatch_natural f g h u x k (z,t) hk

end HarmonicArtin

end OAI
