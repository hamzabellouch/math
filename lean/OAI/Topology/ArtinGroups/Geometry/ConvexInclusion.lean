import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureLayerSelf
import OAI.Topology.ArtinGroups.Harmonic.FusionColorRegion
import OAI.Topology.ArtinGroups.Geometry.ConvexWord

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d

noncomputable def sourceConvexActualInclusion (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    TermwiseSplitInjection Q (sourceConvexModel M J z s q w L).complex (Y z s L q) := by
  let a:=Classical.choice (sourceConvexModel_inclusion M J hJ z s q w L)
  let e:HomotopyEquivalence Q (minimalClassModel Q (classLayer Q q (O z s L))).complex
      (Y z s L q):=minimalClassModelEquivalence Q (Y z s L q)
  have lower : ClassLowerBound Q q (classLayer Q q (O z s L)) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q (O z s L)) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  have he:∀ i,((minimalClassModel Q (classLayer Q q (O z s L))).complex.placement i).level=q :=
    fun index=>le_antisymm (upper index) (lower index)
  exact a.trans Q ((e.ofPure Q he (fun i=>i.property)).termwiseSplit Q)

noncomputable def sourceConvexRegionInclusion (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hb:∀ L i,((Y z s L q).placement i).color∉colorBoundary Q (fusionColorRegion m (Sum.inl '' I)))
    (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    TermwiseSplitInjection Q (sourceConvexModel M J z s q w L).complex
      (fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L) := by
  apply (sourceConvexActualInclusion M J hJ z s q w L).colorTarget Q
    (sourceConvexModel_pure M J hJ z s q w L) (fun i=>i.property)
    (fusionColorRegion m (Sum.inl '' I)) _ (hb L)
  intro i
  obtain ⟨v,hv⟩:=sourceConvexModel_support M J z s q w L i
  change ((sourceConvexModel M J z s q w L).complex.placement i).color.1∈Sum.inl '' I
  rw [← hv]
  exact ⟨v.1.val,hJI v.1.property,rfl⟩

end HarmonicArtin

end OAI
