import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Complexes.PacketTwistRaisedGenerator
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistLoweredGenerator

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def ClassUpperBound (l:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i, ((minimalClassModel Q x).complex.placement i).level≤l

def ClassLowerBound (l:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i, l≤((minimalClassModel Q x).complex.placement i).level

omit [Fintype V] [DecidableEq A] in
lemma minimal_bound_transport (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q E F) (P:GeneratorPlacement V→Prop)
    (h:∀ i,P (E.placement i)) : ∀ j,P (F.placement j) := by
  intro j
  obtain ⟨x,hx,hs,_⟩ := minimal_generator_dual_cycle Q E F hF e j
  have hex : ∃ i,x i≠0 := not_forall.mp (fun hh=>hx (funext hh))
  obtain ⟨i,hi⟩:=hex
  have hp:E.placement i=F.placement j := Classical.not_not.mp (fun hn=>hi (hs i hn))
  rw [← hp]
  exact h i

omit [Fintype V] [DecidableEq A] in
lemma classUpperBound_of_representative (E:BasedComplex Q (K:=K) I) {l:ℤ}
    (h:∀ i,(E.placement i).level≤l) : ClassUpperBound Q l (classOfComplex Q E) :=
  minimal_bound_transport Q E _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q E).symm (fun p=>p.level≤l) h

omit [Fintype V] [DecidableEq A] in
lemma classLowerBound_of_representative (E:BasedComplex Q (K:=K) I) {l:ℤ}
    (h:∀ i,l≤(E.placement i).level) : ClassLowerBound Q l (classOfComplex Q E) :=
  minimal_bound_transport Q E _ (minimalClassModel_minimal Q _)
    (minimalClassModelEquivalence Q E).symm (fun p=>l≤p.level) h

theorem classPacketPerm_cap_of_top_zero
    (hn:∀ a,Q.source a≠Q.target a) (v:J→V)
    (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (x:FiniteHomotopyClass Q (K:=K)) {l:ℤ} (hcap:ClassUpperBound Q l x)
    (htop:∀ a c,classLayerTopDimension Q l (v a) c x=0) :
    ClassUpperBound Q l (classPacketPerm Q hn v hv x) := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have ht:∀ a c,coefficientTopDual Q (E.complex.pureLayer Q hE l) (v a) c=⊥ := by
    intro a c
    exact Submodule.finrank_eq_zero.mp (htop a c)
  obtain ⟨F,hF,⟨e⟩,hb⟩:=packetTwist_cap_of_top_zero Q E.complex hE hcap v ht
  have hh:=classUpperBound_of_representative Q F.complex hb
  have hx:classPacketPerm Q hn v hv x=classOfComplex Q F.complex := by
    rw [← minimalClassModel_class Q x,classPacketPerm_apply]
    exact classOfComplex_eq Q e
  rw [hx]
  exact hh

theorem classNegativeTwist_floor_of_socle_zero
    (α:V) (x:FiniteHomotopyClass Q (K:=K)) {l:ℤ} (hfloor:ClassLowerBound Q l x)
    (hsoc:∀ c,classLayerSocleDimension Q l α c x=0) :
    ClassLowerBound Q l (classNegativeTwist Q α x) := by
  let E:=minimalClassModel Q x
  have hE:E.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have hs:∀ c,coefficientSocle Q (E.complex.pureLayer Q hE l) α c=⊥ := by
    intro c
    exact Submodule.finrank_eq_zero.mp (hsoc c)
  obtain ⟨F,hF,⟨e⟩,hb⟩:=negativeTwist_floor_of_socle_zero Q E.complex hE hfloor α hs
  have hh:=classLowerBound_of_representative Q F.complex hb
  have hx:classNegativeTwist Q α x=classOfComplex Q F.complex := by
    rw [← minimalClassModel_class Q x]
    apply Quotient.sound
    exact ⟨by convert e using 1 <;> rfl⟩
  rw [hx]
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
