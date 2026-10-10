import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionAppend
import OAI.Topology.ArtinGroups.Complexes.LayerConeEquivalence
import OAI.Topology.ArtinGroups.Complexes.PositiveConeIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassCone (x y z:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∃ E F:FiniteModel Q (K:=K), ∃ f:Map Q E.complex F.complex,
    classOfComplex Q E.complex=x ∧ classOfComplex Q F.complex=y ∧
    classOfComplex Q (f.cone Q)=z

omit [Fintype V] [DecidableEq A] in
lemma ClassCone.ofMap {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J} (f:Map Q E F) :
    ClassCone Q (classOfComplex Q E) (classOfComplex Q F) (classOfComplex Q (f.cone Q)) :=
  ⟨FiniteModel.ofComplex Q E,FiniteModel.ofComplex Q F,f,rfl,rfl,rfl⟩

lemma ClassCone.positive {x y z:FiniteHomotopyClass Q (K:=K)} (h:ClassCone Q x y z) (α:V) :
    ClassCone Q (classPositiveTwist Q α x) (classPositiveTwist Q α y) (classPositiveTwist Q α z) := by
  obtain ⟨E,F,f,rfl,rfl,rfl⟩:=h
  refine ⟨FiniteModel.ofComplex Q (E.complex.positiveTwist Q α),
    FiniteModel.ofComplex Q (F.complex.positiveTwist Q α),f.positiveTwist Q α,rfl,rfl,?_⟩
  have coneIso : ChainIsomorphism Q ((f.cone Q).positiveTwist Q α)
      ((f.positiveTwist Q α).cone Q) := by
    convert positiveTwistCone Q f α using 1
  exact (classOfComplex_eq Q (coneIso.toHomotopyEquivalence Q)).symm

lemma ClassCone.positiveWord {x y z:FiniteHomotopyClass Q (K:=K)}
    (h:ClassCone Q x y z) (w:List V) :
    ClassCone Q (positiveWordAction Q w x) (positiveWordAction Q w y) (positiveWordAction Q w z) := by
  induction w with
  | nil=>exact h
  | cons α w ih=>exact ih.positive Q α

lemma ClassCone.packet {x y z:FiniteHomotopyClass Q (K:=K)}
    (h:ClassCone Q x y z) (hn:∀ a,Q.source a≠Q.target a)
    {P:Type u} [Fintype P] (v:P→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ClassCone Q (classPacketPerm Q hn v hv x) (classPacketPerm Q hn v hv y)
      (classPacketPerm Q hn v hv z) := by
  obtain ⟨w,_,hw⟩:=classPacketPerm_positiveWord Q (K:=K) hn v hv
  simpa only [hw] using h.positiveWord Q w

omit [Fintype V] [DecidableEq A] in
lemma ClassCone.layer_eq {x y z:FiniteHomotopyClass Q (K:=K)}
    (h:ClassCone Q x y z) (q:ℤ)
    (hz:∀ i,((minimalClassModel Q z).complex.placement i).level≠q-1 ∧
      ((minimalClassModel Q z).complex.placement i).level≠q) :
    classLayer Q q x=classLayer Q q y := by
  obtain ⟨E,F,f,hE,hF,hz'⟩:=h
  have he:classOfComplex Q (f.cone Q)=classOfComplex Q (minimalClassModel Q z).complex:=
    hz'.trans (minimalClassModel_class Q z).symm
  obtain ⟨e⟩:=Quotient.exact he
  rw [← hE,← hF]
  exact classLayer_eq_of_cone_equivalence Q f _ e q hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
