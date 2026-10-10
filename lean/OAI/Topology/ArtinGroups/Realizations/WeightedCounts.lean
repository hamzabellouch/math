import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketPermPreservesOpen
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketLayerExterior
import OAI.Topology.ArtinGroups.Harmonic.IsolatedIterationData
import OAI.Topology.ArtinGroups.Harmonic.IntegerUpward

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {M:CoxeterMatrix S}
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "T" => fusionPacketPerm m d hd hdiag (K:=ℂ)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

lemma weighted_counts (z:List ((S⊕Unit)×Bool)) (k:ℤ) :
    (∑ H,fusionWeight m H • classTotalVector Q (classLayer Q k (O z D.s H)))=
      fusionFold m (μ z D.s k) := by
  rw [← fusionOrbitWeightedVector_class]
  exact fusionOrbitWeightedVector_eq m d hd hdiag hm z D.s k

lemma unshifted (z:List ((S⊕Unit)×Bool)) (j:D.J) (k:ℤ)
    (ht:∀ H L c,classLayerTopDimension Q (k-1) (.inl j,L) c (O z D.s H)=0) :
    ∀ H,classLayer Q k (O ((.inl j,true)::z) D.s H)=
      classLayer Q k (T (.inl j) (classLayer Q k (O z D.s H))) := by
  intro H
  exact classPacketPerm_unshifted_layer Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) (O z D.s H) k (ht H)

lemma openSocle_unshifted (z:List ((S⊕Unit)×Bool)) (j:D.J) (k:ℤ)
    (ht:∀ H L c,classLayerTopDimension Q (k-1) (.inl j,L) c (O z D.s H)=0)
    (hs:D.openSocle z k) : D.openSocle ((.inl j,true)::z) k := by
  intro H α hα c
  rw [classLayerSocleDimension_congr_layer Q k (D.unshifted z j k ht H) α c]
  apply classPacketPerm_preserves_open_socle Q hn (fun L=>(Sum.inl (j:S),L))
    (fusionColor_orthogonal m d hd hdiag (.inl j)) D.operated
    (fun L=>⟨j,j.property,rfl⟩) (classLayer Q k (O z D.s H))
    (classLayer_lowerBound Q (O z D.s H) k) _ α hα c
  intro β hβ r
  rw [classLayerSocleDimension_layer]
  exact hs H β hβ r

theorem upward (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (j:D.J) (b t:ℤ) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k) (hc':D.capped ((.inl j,true)::z)) :
    (∀ k,k<t→D.openSocle ((.inl j,true)::z) k) ∧
    (∀ k,k<t→∀ H L c,classLayerTopDimension Q k (.inl j,L) c (O z D.s H)=0) ∧
    (∀ H,classLayer Q t (O ((.inl j,true)::z) D.s H)=
      classLayer Q t (T (.inl j) (classLayer Q t (O z D.s H)))) := by
  let z':=((Sum.inl (j:S),true)::z)
  have hz':D.valid z':=D.move z hz j
  have hb':∀ H,ClassLowerBound Q b (O z' D.s H):=D.lower_bound_move z j b hb
  let P:ℤ→Prop:=fun k=>
    (∀ H L c,classLayerTopDimension Q k (.inl j,L) c (O z D.s H)=0) ∧ D.openSocle z' k
  have hP:∀ k,k<t→P k := by
    refine integer_upward (P:=P) b t ?_ ?_
    · intro k hk
      exact ⟨fun H L c=>classLayerTopDimension_below Q (O z D.s H) b k (hb H) hk _ c,
        D.socle_below z' b k hb' hk⟩
    · intro k _ hkt hprev
      have hs':D.openSocle z' k:=D.openSocle_unshifted z j k hprev.1 (hp k hkt)
      have hr:=(D.separation z hz hc k (hp k hkt)).2.1
      have hr':=(D.separation z' hz' hc' k hs').2.1
      have htop:=fusionPacket_zero_rows_force_top m d hd hdiag hm (.inl j) k
        (O z D.s) hprev.1 (μ z D.s k) (μ z' D.s k)
        (D.weighted_counts z k) (D.weighted_counts z' k)
        (hr (.inl j) ⟨j,j.property,rfl⟩) (hr' (.inl j) ⟨j,j.property,rfl⟩)
      exact ⟨htop.2,hs'⟩
  exact ⟨fun k hk=>(hP k hk).2,fun k hk=>(hP k hk).1,
    D.unshifted z j t (hP (t-1) (by omega)).1⟩

theorem stage_move (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (j:D.J) (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k)
    (hs:∃ H L c,0<classLayerSocleDimension Q t (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) ∧
    (∀ H,ClassLowerBound Q b (O ((.inl j,true)::z) D.s H)) ∧
    (∀ k,k<t→D.openSocle ((.inl j,true)::z) k) ∧
    (∀ H,classLayer Q t (O ((.inl j,true)::z) D.s H)=
      classLayer Q t (T (.inl j) (classLayer Q t (O z D.s H)))) := by
  have hc':=D.cap_move z hz hc t ht (hp (t-1) (by omega)) j hs
  have hup:=D.upward z hz hc j b t hb hp hc'
  exact ⟨hc',D.lower_bound_move z j b hb,hup.1,hup.2.2⟩

end IsolatedIterationData
end HarmonicArtin

end OAI
