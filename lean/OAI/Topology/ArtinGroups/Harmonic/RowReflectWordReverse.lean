import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TotalVector

namespace OAI

namespace HarmonicArtin
open Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

lemma rowReflectWord_reverse_orthogonal (C:Matrix V V ℝ) (l:List V)
    (hn:l.Nodup) (ho:∀ α∈l,∀ β∈l,α≠β→C α β=0) (x:V→ℝ) :
    rowReflectWord C l.reverse x=rowReflectWord C l x := by
  rw [rowReflectWord_orthogonal C l hn ho,
    rowReflectWord_orthogonal C l.reverse (List.nodup_reverse.mpr hn)
      (by simpa only [List.mem_reverse] using ho)]
  simp only [List.toFinset_reverse]

lemma rowReflect_add (C:Matrix V V ℝ) (α:V) (x y:V→ℝ) :
    rowReflect C α (x+y)=rowReflect C α x+rowReflect C α y := by
  simp only [rowReflect,Matrix.mulVec_add,Pi.add_apply,add_smul]
  module

lemma rowReflectWord_add (C:Matrix V V ℝ) (w:List V) (x y:V→ℝ) :
    rowReflectWord C w (x+y)=rowReflectWord C w x+rowReflectWord C w y := by
  induction w with
  | nil=>rfl
  | cons α w ih=>
    change rowReflect C α (rowReflectWord C w (x+y))=_
    rw [ih,rowReflect_add]
    rfl

lemma rowReflectWord_zero (C:Matrix V V ℝ) (w:List V) : rowReflectWord C w 0=0 := by
  have h:=rowReflectWord_smul C w 0 (0:V→ℝ)
  simpa only [zero_smul] using h

lemma rowReflectWord_sum {F:Type*} (C:Matrix V V ℝ) (w:List V) (t:Finset F) (f:F→V→ℝ) :
    rowReflectWord C w (∑ i∈t,f i)=∑ i∈t,rowReflectWord C w (f i) := by
  induction t using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty,rowReflectWord_zero]
  | @insert i t hi ih=>rw [Finset.sum_insert hi,Finset.sum_insert hi,rowReflectWord_add,ih]

variable {E:Type*} [Fintype E] [DecidableEq E] (m:E→ℕ)

lemma fusion_reverse_reflection_intertwining (hm:∀ e,2 ≤ m e)
    (d:V→V→FusionEdge E) (hdiag:∀ i,d i i=.units 0) (i:V) (p:V→ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d)
      (((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))).reverse)
      (fusionFold m p)=fusionFold m (rowReflect (fusionFoldedCartan m d) i p) := by
  let l:=((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
  have hn:l.Nodup:=List.Nodup.map (fun _ _ h=>Prod.mk.inj h |>.2) (Finset.nodup_toList _)
  have ho:∀ α∈l,∀ β∈l,α≠β→fusionUnfoldedCartan m d α β=0 := by
    rintro α hα β hβ hne
    obtain ⟨L,_,rfl⟩:=List.mem_map.mp hα
    obtain ⟨L',_,rfl⟩:=List.mem_map.mp hβ
    simp [fusionUnfoldedCartan,hne,hdiag,FusionEdge.multiplicity]
  rw [rowReflectWord_reverse_orthogonal _ l hn ho]
  exact fusion_reflection_intertwining m hm d hdiag i p

theorem fusion_reverse_word_intertwining (hm:∀ e,2 ≤ m e)
    (d:V→V→FusionEdge E) (hdiag:∀ i,d i i=.units 0) (w:List V) (p:V→ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d) (fusionExpandedWord m w).reverse (fusionFold m p)=
      fusionFold m (rowReflectWord (fusionFoldedCartan m d) w.reverse p) := by
  induction w generalizing p with
  | nil=>rfl
  | cons i w ih=>
    change rowReflectWord (fusionUnfoldedCartan m d)
      ((((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))) ++
        fusionExpandedWord m w).reverse) (fusionFold m p)=_
    rw [List.reverse_append,rowReflectWord_append,fusion_reverse_reflection_intertwining m hm d hdiag,ih,
      List.reverse_cons,rowReflectWord_append]
    rfl

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma fusionFold_sub (x y:V→ℝ) : fusionFold m (x-y)=fusionFold m x-fusionFold m y := by
  ext α
  simp only [fusionFold,Pi.sub_apply,mul_sub]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma fusionFold_injective (hm:∀ e,2 ≤ m e) : Function.Injective (fusionFold (V:=V) m) := by
  intro x y h
  let L:FusionLabel m:=fun e=>⟨0,by have := hm e; omega⟩
  funext v
  have hh:=congrFun h (v,L)
  exact mul_left_cancel₀ (ne_of_gt (fusionWeight_pos m hm L)) hh

end HarmonicArtin

end OAI
