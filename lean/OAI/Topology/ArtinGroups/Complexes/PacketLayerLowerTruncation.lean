import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ComplexPacketLowerBound
import OAI.Topology.ArtinGroups.Complexes.LayerSocleDimensionLayer
import OAI.Topology.ArtinGroups.Complexes.Cone2
import OAI.Topology.ArtinGroups.Complexes.HighConeRetainedPure

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I P:Type u} [Fintype I] [Fintype P] [DecidableEq I] [DecidableEq P]
  (hn:∀ a,Q.source a≠Q.target a) (v:P→V)
  (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
local notation "T" => classPacketPerm Q hn v hv

omit [DecidableEq P] in
lemma packetLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    classLayer Q q (T (classOfComplex Q (lowerTruncation Q E hE q)))=
      classLayer Q q (T (classOfComplex Q E)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  have hc:=ClassCone.ofMap Q f
  have he:classOfComplex Q (f.cone Q)=classOfComplex Q R:=
    classOfComplex_eq Q (lowConeReduction Q E _ (levelDownClosed Q E hE q))
  rw [he] at hc
  have hr:ClassLowerBound Q (q+1) (classOfComplex Q R):=by
    apply classLowerBound_of_representative Q
    intro i
    have hi:=i.property
    change ¬(E.placement i).level≤q at hi
    change q+1≤(E.placement i).level
    omega
  have hb:=classPacketPerm_lower_bound Q hn v hv (classOfComplex Q R) hr
  exact (hc.packet Q hn v hv).layer_eq Q q (fun i=>by have hi:=hb i; constructor <;> omega)

lemma packetLayer_top (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q)
    (ht:∀ a c,coefficientTopDual Q (E.pureLayer Q hE (q-1)) (v a) c=⊥) :
    classLayer Q q (T (classOfComplex Q E))=
      classLayer Q q (T (classLayer Q q (classOfComplex Q E))) := by
  let f:=highProjection Q E _ (levelDownClosed Q E hE (q-1))
  let D:=(highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q
  have hD:D.IsMinimal Q:=highConeRetained_minimal Q E hE _ _
  have hd:ClassUpperBound Q (q-2) (classOfComplex Q D) := by
    apply classUpperBound_of_representative Q
    intro i
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i).level≤q-1 at hi
    omega
  have htop:∀ a c,classLayerTopDimension Q (q-2) (v a) c (classOfComplex Q D)=0 := by
    intro a c
    rw [classLayerTopDimension_minimal Q D hD]
    rw [highConeRetained_top_zero Q E hE q (v a) (ht a),finrank_bot]
  have hb:=classPacketPerm_cap_of_top_zero Q hn v hv (classOfComplex Q D) hd htop
  have hc:=ClassCone.ofMap Q f
  have he:classOfComplex Q (f.cone Q)=classOfComplex Q D:=
    classOfComplex_eq Q (highConeReduction Q E _ (levelDownClosed Q E hE (q-1)))
  rw [he] at hc
  have hh:classLayer Q q (T (classOfComplex Q E))=
      classLayer Q q (T (classOfComplex Q (upperTruncation Q E hE (q-1)))):=
    (hc.packet Q hn v hv).layer_eq Q q (fun i=>by have hi:=hb i; constructor <;> omega)
  rwa [highRestriction_top_eq_layer Q E hE q hhi] at hh

theorem classPacketPerm_unshifted_layer (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (ht:∀ a c,classLayerTopDimension Q (q-1) (v a) c x=0) :
    classLayer Q q (T x)=classLayer Q q (T (classLayer Q q x)) := by
  let E:=(minimalClassModel Q x).complex
  have hE:E.IsMinimal Q:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E=x:=minimalClassModel_class Q x
  let L:=lowerTruncation Q E hE q
  have hL:L.IsMinimal Q:=lowerTruncation_minimal Q E hE q
  have hl:classLayer Q (q-1) (classOfComplex Q L)=classLayer Q (q-1) x := by
    exact (classLayer_lowerTruncation_le Q E hE (q-1) q (by omega)).trans
      (congrArg (classLayer Q (q-1)) hx)
  have htL:∀ a c,coefficientTopDual Q (L.pureLayer Q hL (q-1)) (v a) c=⊥ := by
    intro a c
    apply Submodule.finrank_eq_zero.mp
    rw [← classLayerTopDimension_minimal Q L hL]
    rw [classLayerTopDimension_congr_layer Q (q-1) hl (v a) c,ht a c]
  have hh:=packetLayer_top Q hn v hv L hL q (fun i=>i.property) htL
  have hp:=packetLayer_lowerTruncation Q hn v hv E hE q
  rw [classLayer_lowerTruncation_le Q E hE q q le_rfl,hx] at hh
  rw [hx] at hp
  exact hp.symm.trans hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
