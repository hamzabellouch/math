import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketPermEnumeration

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀a,Q.source a≠Q.target a)

include hn in
lemma positiveWordAction_orthogonal_comm (α:V) (w:List V)
    (hw:∀β∈w,OrthogonalVertices Q α β) (x:FiniteHomotopyClass Q (K:=K)) :
    classPositiveTwist Q α (positiveWordAction Q w x)=
      positiveWordAction Q w (classPositiveTwist Q α x) := by
  induction w with
  | nil=>rfl
  | cons β w ih=>
    change classPositiveTwist Q α (classPositiveTwist Q β (positiveWordAction Q w x))=_
    have he:=congrArg (fun p:Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>p (positiveWordAction Q w x))
      (classTwistPerm_orthogonal Q hn (hw β (by simp)))
    change classPositiveTwist Q α (classPositiveTwist Q β (positiveWordAction Q w x))=
      classPositiveTwist Q β (classPositiveTwist Q α (positiveWordAction Q w x)) at he
    rw [he,ih (fun γ hγ=>hw γ (List.mem_cons_of_mem _ hγ))]
    rfl

lemma classPacketPerm_testUpper_reflect {J:Type u} [Fintype J]
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (U:Set V) (hU:∀a,v a∈U) (x:FiniteHomotopyClass Q (K:=K)) {t:ℤ}
    (h:ClassTestUpper Q (classPacketPerm Q hn v hv x) U t) : ClassTestUpper Q x U t := by
  rw [← classPacketPerm_toList Q hn v hv] at h
  have he: ((Finset.univ:Finset J).toList.map (fun a=>classTwistPerm Q hn (v a))).prod x=
      positiveWordAction Q ((Finset.univ:Finset J).toList.map v) x := by
    rw [positiveWordAction_eq_prod Q hn,List.map_map]
    rfl
  rw [he] at h
  apply positiveWordAction_testUpper_reflect Q hn _ x U _ h
  intro α hα
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hα
  exact hU a

lemma classPacketPerm_testExact_of_cap {J:Type u} [Fintype J]
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (U:Set V) (hU:∀a,v a∈U) (x:FiniteHomotopyClass Q (K:=K)) {t:ℤ}
    (h:ClassTestUpper Q (classPacketPerm Q hn v hv x) U t) (a:J) (c:ℤ) :
    ClassTestExact Q (v a) t c x := by
  let vr:{b:J // b≠a}→V:=fun b=>v b.val
  have hvr:Pairwise fun b b'=>OrthogonalVertices Q (vr b) (vr b') := by
    intro b b' hbb
    exact hv (fun he=>hbb (Subtype.ext he))
  have he:classPacketPerm Q (K:=K) hn v hv=classTwistPerm Q hn (v a)*classPacketPerm Q hn vr hvr := by
    let vo:Option {b:J // b≠a}→V:=v ∘ Equiv.optionSubtypeNe a
    have hvo:Pairwise fun b b'=>OrthogonalVertices Q (vo b) (vo b') :=
      fun b b' hbb=>hv (fun hh=>hbb ((Equiv.optionSubtypeNe a).injective hh))
    calc
      classPacketPerm Q hn v hv = classPacketPerm Q hn vo hvo :=
        classPacketPerm_reindex Q hn v hv (Equiv.optionSubtypeNe a)
      _ = classTwistPerm Q hn (vo none)*classPacketPerm Q hn (vo ∘ some)
          (fun b b' hbb=>hvo (fun hh=>hbb (Option.some.inj hh))) :=
        classPacketPerm_cons Q hn vo hvo
      _ = _ := rfl
  have hc:classPositiveTwist Q (v a) (classPacketPerm Q hn vr hvr x)=
      classPacketPerm Q hn vr hvr (classPositiveTwist Q (v a) x) := by
    rw [← classPacketPerm_toList Q hn vr hvr]
    have hword (y:FiniteHomotopyClass Q (K:=K)):
        ((Finset.univ:Finset {b:J // b≠a}).toList.map (fun b=>classTwistPerm Q hn (vr b))).prod y=
        positiveWordAction Q ((Finset.univ:Finset {b:J // b≠a}).toList.map vr) y := by
      rw [positiveWordAction_eq_prod Q hn,List.map_map]
      rfl
    rw [hword,hword]
    apply positiveWordAction_orthogonal_comm Q hn
    intro β hβ
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hβ
    exact hv (Ne.symm b.property)
  rw [he] at h
  change ClassTestUpper Q (classPositiveTwist Q (v a) (classPacketPerm Q hn vr hvr x)) U t at h
  rw [hc] at h
  have hs:=classPacketPerm_testUpper_reflect Q hn vr hvr U (fun b=>hU b.val) _ h
  exact (classPositiveTwist_testUpper_iff Q hn x U (v a) (hU a)
    (classPositiveTwist_testUpper_reflect Q hn x U (v a) (hU a) hs)).mp hs c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
