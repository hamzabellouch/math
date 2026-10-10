import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem classOfComplex_packet_preserves
    {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I]
    (E:BasedComplex Q (K:=K) I) (P:FiniteHomotopyClass Q (K:=K)→Prop)
    (hE:P (classOfComplex Q E)) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (hstep:∀ a x,P x→P (classPositiveTwist Q (v a) x)) :
    P (classOfComplex Q (E.packetTwist Q v)) := by
  have hs:=hstep
  suffices hh:∀ (J:Type u) [Fintype J] (v:J→V),
      Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b))→
      (∀ a x,P x→P (classPositiveTwist Q (v a) x))→
      P (classOfComplex Q (E.packetTwist Q v)) from hh J v hv hs
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ v:J→V,
    Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b))→
    (∀ a x,P x→P (classPositiveTwist Q (v a) x))→
    P (classOfComplex Q (E.packetTwist Q v))) _ _ _ J
  · intro J L instL e ih
    let:=Fintype.ofEquiv L e.symm
    intro v hv hs
    rw [classOfComplex_packet_reindex Q E v e]
    exact ih (v ∘ e) (fun a b hab=>hv (fun h=>hab (e.injective h))) (fun a=>hs (e a))
  · let : DecidableEq PEmpty := Classical.decEq _
    intro v hv hs
    have he:classOfComplex Q (E.packetTwist Q v)=classOfComplex Q E := by
      convert (classOfComplex_reindex Q _ (packetEmptyEquiv Q E v)).trans
        (congrArg (classOfComplex Q) (packetEmpty_eq Q E v)) using 1
    rw [he]
    exact hE
  · intro J instJ ih
    let : DecidableEq J := Classical.decEq _
    let : DecidableEq (Option J) := Classical.decEq _
    intro v hv hs
    have hv':v=fun z:Option J=>z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    have he:classOfComplex Q (E.packetTwist Q v)=
        classPositiveTwist Q (v none) (classOfComplex Q (E.packetTwist Q (v ∘ some))) := by
      conv_lhs => rw [hv']
      convert classOfComplex_packet_cons Q E (v none) (v ∘ some) (fun a=>hv (by simp)) using 1
      congr 2
      exact Subsingleton.elim _ _
    rw [he]
    exact hs none _ (ih (v ∘ some) (fun a b hab=>hv (fun h=>hab (Option.some.inj h)))
      (fun a=>hs (some a)))

theorem classPacketPerm_preserves
    (hn:∀ a,Q.source a≠Q.target a) {J:Type u} [Fintype J]
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (P:FiniteHomotopyClass Q (K:=K)→Prop)
    (hstep:∀ a x,P x→P (classPositiveTwist Q (v a) x))
    (x:FiniteHomotopyClass Q (K:=K)) (hx:P x) : P (classPacketPerm Q hn v hv x) := by
  have he:classPacketPerm Q hn v hv x=
      classOfComplex Q ((minimalClassModel Q x).complex.packetTwist Q v) := by
    conv_lhs => rw [← minimalClassModel_class Q x,classPacketPerm_apply]
  rw [he]
  have hxx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  exact classOfComplex_packet_preserves Q _ P (by rwa [hxx]) v hv hstep

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
