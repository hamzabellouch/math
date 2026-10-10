import Mathlib
import OAI.Topology.ArtinGroups.Geometry.Cartan
import OAI.Topology.ArtinGroups.Harmonic.FusionFold

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

noncomputable def rowReflect (C:Matrix V V ℝ) (i:V) (x:V → ℝ) : V → ℝ :=
  x-(C *ᵥ x) i • Pi.single i 1

noncomputable def rowReflectWord (C:Matrix V V ℝ) (l:List V) (x:V → ℝ) : V → ℝ :=
  l.foldr (rowReflect C) x

lemma rowReflect_geometric (M:CoxeterMatrix V) (i:V) (x:V → ℝ) :
    rowReflect (Geometric.cartan M) i x=Geometric.simpleReflection M i x :=
  (Geometric.simpleReflection_apply M i x).symm

lemma rowReflectWord_orthogonal (C:Matrix V V ℝ) (l:List V) (hn:l.Nodup)
    (ho:∀ i∈l,∀ j∈l,i≠j → C i j=0) (x:V → ℝ) :
    rowReflectWord C l x=x-∑ i∈l.toFinset,(C *ᵥ x) i • Pi.single i 1 := by
  induction l with
  | nil => simp [rowReflectWord]
  | cons a l ih =>
    obtain ⟨ha,hl⟩:=List.nodup_cons.mp hn
    have ho' : ∀ i∈l,∀ j∈l,i≠j → C i j=0 :=
      fun i hi j hj h=>ho i (by simp [hi]) j (by simp [hj]) h
    have hs : (C *ᵥ (∑ i∈l.toFinset,(C *ᵥ x) i • Pi.single i 1)) a=0 := by
      rw [Matrix.mulVec_sum,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hi':i∈l:=List.mem_toFinset.mp hi
      have hai:a≠i := fun h=>ha (h.symm ▸ hi')
      simp [Matrix.mulVec_smul,Matrix.mulVec_single,Matrix.col,
        ho a (by simp) i (by simp [hi']) hai]
    change rowReflect C a (rowReflectWord C l x)=_
    rw [ih hl ho']
    simp only [rowReflect,Matrix.mulVec_sub,Pi.sub_apply,hs,sub_zero]
    rw [List.toFinset_cons,Finset.sum_insert (by simpa using ha)]
    module

variable {E:Type*} [Fintype E] [DecidableEq E] (m:E → ℕ)

theorem fusion_reflection_intertwining (hm:∀ e,2 ≤ m e)
    (d:V → V → FusionEdge E) (hdiag:∀ i,d i i=.units 0) (i:V) (p:V → ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d)
      ((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
      (fusionFold m p)=fusionFold m (rowReflect (fusionFoldedCartan m d) i p) := by
  let l:=((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
  have hn:l.Nodup := List.Nodup.map (fun _ _ h=>Prod.mk.inj h |>.2) (Finset.nodup_toList _)
  have ho : ∀ α∈l,∀ β∈l,α≠β → fusionUnfoldedCartan m d α β=0 := by
    rintro α hα β hβ hne
    obtain ⟨L,_,rfl⟩:=List.mem_map.mp hα
    obtain ⟨L',_,rfl⟩:=List.mem_map.mp hβ
    simp [fusionUnfoldedCartan,hne,hdiag,FusionEdge.multiplicity]
  rw [rowReflectWord_orthogonal _ l hn ho]
  rw [fusion_intertwining m hm]
  have hs : (∑ α∈l.toFinset, fusionFold m (fusionFoldedCartan m d *ᵥ p) α • Pi.single α 1)=
      fusionFold m ((fusionFoldedCartan m d *ᵥ p) i • Pi.single i 1) := by
    have hl : l.toFinset = Finset.univ.image (fun L:FusionLabel m=>(i,L)) := by
      ext α
      simp [l]
    rw [hl,Finset.sum_image (by intro a _ b _ h; exact Prod.mk.inj h |>.2)]
    ext β
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,fusionFold,Pi.single_apply]
    by_cases hb:β.1=i
    · rcases β with ⟨v,L⟩
      dsimp at hb
      subst v
      simp
    · have hx : ∀ L:FusionLabel m,β≠(i,L) := fun L h=>hb (congrArg Prod.fst h)
      simp [hx,hb]
  rw [hs]
  ext α
  simp only [rowReflect,fusionFold,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

noncomputable def fusionExpandedWord (w:List V) : List (V × FusionLabel m) :=
  w.flatMap (fun i=>(Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))

lemma rowReflectWord_append (C:Matrix V V ℝ) (a b:List V) (x:V → ℝ) :
    rowReflectWord C (a++b) x=rowReflectWord C a (rowReflectWord C b x) := by
  simp [rowReflectWord,List.foldr_append]

theorem fusion_word_intertwining (hm:∀ e,2 ≤ m e)
    (d:V → V → FusionEdge E) (hdiag:∀ i,d i i=.units 0) (w:List V) (p:V → ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d) (fusionExpandedWord m w) (fusionFold m p)=
      fusionFold m (rowReflectWord (fusionFoldedCartan m d) w p) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change rowReflectWord (fusionUnfoldedCartan m d)
      (((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))) ++
        fusionExpandedWord m w) (fusionFold m p)=_
    rw [rowReflectWord_append,ih,fusion_reflection_intertwining m hm d hdiag]
    rfl

end HarmonicArtin

end OAI
