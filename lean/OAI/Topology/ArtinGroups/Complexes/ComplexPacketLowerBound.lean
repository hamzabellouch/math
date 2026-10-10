import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistLowerBound

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I]

theorem classOfComplex_packet_lower_bound
    (E:BasedComplex Q (K:=K) I) {d:ℤ} (hE:∀ i,d≤(E.placement i).level)
    (v:J→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b)) :
    ClassLowerBound Q d (classOfComplex Q (E.packetTwist Q v)) := by
  suffices hh:∀ (J:Type u) [Fintype J] (v:J→V),
      Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b)) →
      ClassLowerBound Q d (classOfComplex Q (E.packetTwist Q v)) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _=>∀ v:J→V,
    Pairwise (fun a b=>OrthogonalVertices Q (v a) (v b)) →
    ClassLowerBound Q d (classOfComplex Q (E.packetTwist Q v))) _ _ _ J
  · intro J L instL e ih
    let:=Fintype.ofEquiv L e.symm
    intro v hv
    rw [classOfComplex_packet_reindex Q E v e]
    exact ih (v ∘ e) (fun a b hab=>hv (fun h=>hab (e.injective h)))
  · let : DecidableEq PEmpty := Classical.decEq _
    intro v hv
    apply classLowerBound_of_representative Q
    intro j
    rcases j with u|i
    · exact isEmptyElim u.1
    · exact hE i
  · intro J instJ ih
    let : DecidableEq J := Classical.decEq _
    let : DecidableEq (Option J) := Classical.decEq _
    intro v hv
    have hv':v=fun z:Option J=>z.elim (v none) (v ∘ some) := by
      funext z; cases z <;> rfl
    have he:classOfComplex Q (E.packetTwist Q v)=
        classPositiveTwist Q (v none) (classOfComplex Q (E.packetTwist Q (v ∘ some))) := by
      conv_lhs => rw [hv']
      convert classOfComplex_packet_cons Q E (v none) (v ∘ some) (fun a=>hv (by simp)) using 1
      congr 2
      exact Subsingleton.elim _ _
    rw [he]
    exact classPositiveTwist_lower_bound Q (v none) _
      (ih (v ∘ some) (fun a b hab=>hv (fun h=>hab (Option.some.inj h))))

theorem classPacketPerm_lower_bound
    (hn:∀ a,Q.source a≠Q.target a) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) :
    ClassLowerBound Q d (classPacketPerm Q hn v hv x) := by
  have he:classPacketPerm Q hn v hv x=
      classOfComplex Q ((minimalClassModel Q x).complex.packetTwist Q v) := by
    conv_lhs => rw [← minimalClassModel_class Q x,classPacketPerm_apply]
  rw [he]
  exact classOfComplex_packet_lower_bound Q _ hx v hv

theorem classPacketPerm_bottom_socle_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) (a:J) (c:ℤ) :
    classLayerSocleDimension Q d (v a) c (classPacketPerm Q hn v hv x)=0 := by
  let : DecidableEq {b:J // b≠a} := Classical.decEq _
  let E:=minimalClassModel Q x
  let vr:{b:J // b≠a}→V:=fun b=>v b.val
  have hvr:Pairwise fun b b'=>OrthogonalVertices Q (vr b) (vr b') := by
    intro b b' h
    apply hv
    intro he
    exact h (Subtype.ext he)
  have he:classPacketPerm Q hn v hv x=
      classPositiveTwist Q (v a) (classOfComplex Q (E.complex.packetTwist Q vr)) := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply,
      classOfComplex_packet_reindex Q E.complex v (Equiv.optionSubtypeNe a)]
    have hf:v ∘ Equiv.optionSubtypeNe a=fun z:Option {b:J // b≠a}=>z.elim (v a) vr := by
      funext z; cases z <;> rfl
    rw [hf,classOfComplex_packet_cons Q E.complex (v a) vr (fun b=>hv (Ne.symm b.property))]
  rw [he]
  exact classPositiveTwist_bottom_socle_zero Q hn (v a) _
    (classOfComplex_packet_lower_bound Q E.complex hx vr hvr) c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
