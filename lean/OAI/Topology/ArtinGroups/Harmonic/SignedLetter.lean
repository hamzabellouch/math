import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PacketWord
import OAI.Topology.ArtinGroups.Harmonic.ArtinAction

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "P" => fusionWordPacketPerm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

noncomputable def sourceSignedLetter (a:S×Bool) : Artin M :=
  if a.2 then generator M a.1 else (generator M a.1)⁻¹
noncomputable def sourceSignedWord (w:List (S×Bool)) : Artin M :=
  (w.map (sourceSignedLetter M)).prod

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_cons (a:S×Bool) (w:List (S×Bool)) :
    sourceSignedWord M (a::w)=sourceSignedLetter M a*sourceSignedWord M w := rfl

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_append (u v:List (S×Bool)) :
    sourceSignedWord M (u++v)=sourceSignedWord M u*sourceSignedWord M v := by
  simp only [sourceSignedWord,List.map_append,List.prod_append]

omit [Fintype S] [LinearOrder S] in
lemma artinParabolic_signed_word (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J) :
    ∃ w:List (S×Bool),(∀ a∈w,a.1∈J) ∧ sourceSignedWord M w=g := by
  apply Subgroup.closure_induction_left
    (p:=fun g _=>∃ w:List (S×Bool),(∀ a∈w,a.1∈J) ∧ sourceSignedWord M w=g) ?_ ?_ ?_ hg
  · exact ⟨[],by simp, rfl⟩
  · rintro g ⟨s,hs,rfl⟩ y hy ⟨w,hw,rfl⟩
    refine ⟨(s,true)::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hs
      · exact hw a ha
    · simp only [sourceSignedWord_cons,sourceSignedLetter,ite_true]
  · rintro g ⟨s,hs,rfl⟩ y hy ⟨w,hw,rfl⟩
    refine ⟨(s,false)::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hs
      · exact hw a ha
    · simp only [sourceSignedWord_cons,sourceSignedLetter,Bool.false_eq_true,ite_false]

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_mem (J:Set S) (w:List (S×Bool)) (hw:∀ a∈w,a.1∈J) :
    sourceSignedWord M w∈artinParabolic M J := by
  induction w with
  | nil=>exact (artinParabolic M J).one_mem
  | cons a w ih=>
    apply (artinParabolic M J).mul_mem _ (ih (fun b hb=>hw b (by simp [hb])))
    have h:generator M a.1∈artinParabolic M J:=Subgroup.subset_closure ⟨a.1,hw a (by simp),rfl⟩
    unfold sourceSignedLetter
    split_ifs
    · exact h
    · exact (artinParabolic M J).inv_mem h

lemma sourceArtinAction_signedWord (w:List (S×Bool)) :
    sourceArtinAction M (K:=K) (sourceSignedWord M w)=P (sourcePacketWord w) := by
  induction w with
  | nil=>simp [sourceSignedWord,sourcePacketWord,fusionWordPacketPerm]
  | cons a w ih=>
    rw [sourceSignedWord_cons,map_mul,ih]
    change _=_*P (sourcePacketWord w)
    congr 1
    rcases a with ⟨s,b⟩
    cases b <;> simp [sourceSignedLetter,fusionSignedPacketPerm,sourceArtinAction_generator,map_inv]

lemma sourcePacketOrbit_signedPrepend (w:List (S×Bool))
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (L:FusionLabel m) :
    fusionPacketOrbit m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
      (sourcePacketWord w++z) s L=
    sourceArtinAction M (sourceSignedWord M w)
      (fusionPacketOrbit m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) z s L) := by
  rw [sourceArtinAction_signedWord]
  induction w with
  | nil=>rfl
  | cons a w ih=>
    change fusionSignedPacketPerm m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
      (.inl a.1,a.2) (_)=_
    exact congrArg (fusionSignedPacketPerm m d (coxeterFusionEdge_symm M)
      (coxeterFusionEdge_diag M) (.inl a.1,a.2)) ih

end HarmonicArtin

end OAI
