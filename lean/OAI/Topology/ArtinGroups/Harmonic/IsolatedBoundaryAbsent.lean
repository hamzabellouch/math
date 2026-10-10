import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.DimensionPosMultiplicityPos
import OAI.Topology.ArtinGroups.Geometry.ConvexInclusion
import OAI.Topology.ArtinGroups.Geometry.InteriorConvexHullReindex
import OAI.Topology.ArtinGroups.Harmonic.NullPatch
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitColorSubobject

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
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "a" => fusionOrbitColorMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

lemma source_isolated_boundary_absent (I J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v) :
    ∀ L i,((Y z s L q).placement i).color∉colorBoundary Q (fusionColorRegion m (Sum.inl '' I)) := by
  apply fusionOrbit_boundary_absent m d hd hdiag hm z s q (Sum.inl '' I)
  intro v hv ha
  exact (hdata v (Or.inr ⟨hv,ha⟩)).trans (hcSupp v hv)

theorem source_isolated_interior (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    (fun j:(Sum.inl '' J:Set (S⊕Unit))=>a z s q (Sum.inl '' I) j-c j)∈
      interior (convexHull ℝ (Set.range fun w:(restrictedMatrix M J).Group=>
        (fun j:(Sum.inl '' J:Set (S⊕Unit))=>sourceConvexVector M J z s q w j))) := by
  let p:S⊕Unit→ℝ:=fun v=>if v∈Sum.inl '' J then c v else μ z s q v
  have hi:(Sum.inl '' J:Set (S⊕Unit))⊆Sum.inl '' I := Set.image_mono hJI
  have hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0 := by
    intro j
    apply null_patch (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
      (Sum.inl '' I) (Sum.inl '' J) hi c (μ z s q) hcNull hdata
    exact ⟨j,j.property,rfl⟩
  have hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v := by
    intro v hv
    exact (ite_eq_right hv).symm
  have hpj (j:J):p (.inl (j:S))=c (.inl (j:S)):=ite_eq_left ⟨j,j.property,rfl⟩
  have hh:=source_convex_subobjects_interior M J hJ z s q p hcap hp hext
    (fun g hg hgc j=>by rw [hpj]; exact huniv g hg hgc j)
  let e:J≃(Sum.inl '' J:Set (S⊕Unit)):=Equiv.Set.image Sum.inl J Sum.inl_injective
  have hv : (fun j:(Sum.inl '' J:Set (S⊕Unit))=>a z s q (Sum.inl '' I) j-c j)∘e =
      (μ z s q-p)∘sourceRootInclusion J := by
    funext j
    change (if Sum.inl (j:S)∈Sum.inl '' I then μ z s q (.inl (j:S)) else 0)-c (.inl (j:S))=
      μ z s q (.inl (j:S))-p (.inl (j:S))
    rw [ite_eq_left ⟨j,hJI j.property,rfl⟩,hpj]
  apply interior_convexHull_reindex e
  rw [hv]
  exact hh

theorem source_isolated_separation (I J:Set S) (hJI:J⊆I) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q k:ℤ) (c:S⊕Unit→ℝ)
    (hc:∀ v,0≤c v) (hcSupp:∀ v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀ v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀ v,v∈Sum.inl '' I→(C *ᵥ c) v=0)
    (hdata:∀ v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' J) ∨
      (v∉Sum.inl '' I ∧ ∃ u∈Sum.inl '' I,C v u<0)→μ z s q v=c v)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,c (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S)))
    (hsoc:∀ H α,α.1∈Sum.inl '' J→∀ r,coefficientSocle Q (Y z s H k) α r=⊥) :
    let hb:=source_isolated_boundary_absent M I J z s q c hcSupp hdata
    (∀ v∉Sum.inl '' I,(∃ u∈Sum.inl '' I,C v u<0)→μ z s k v=0) ∧
    (∀ j∈Sum.inl '' J,(C *ᵥ μ z s k) j=0) ∧
    fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L)
      (fun H=>Y z s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z s H k)
      (fun L=>fusionOrbitColorLayer m d hd hdiag z s q (Sum.inl '' I) hb L) (q-k)=0 := by
  dsimp only
  apply fusionOrbitColor_subobject_separation m d hd hdiag hm z s q k
    (Sum.inl '' I) (Sum.inl '' J) (source_isolated_boundary_absent M I J z s q c hcSupp hdata)
    (fun w L=>(sourceConvexModel M J z s q w L).complex)
    (sourceConvexModel_pure M J hJ z s q)
    (fun w L=>by
      convert sourceConvexRegionInclusion M I J hJI hJ z s q
        (source_isolated_boundary_absent M I J z s q c hcSupp hdata) w L using 1)
    c (sourceConvexVector M J z s q)
    (sourceConvexModel_counts M J hJ z s q)
  · intro w L i
    obtain ⟨v,hv⟩:=sourceConvexModel_support M J z s q w L i
    rw [← hv]
    exact ⟨v.1,v.1.property,rfl⟩
  · exact sourceConvexVector_support M J hJ z s q
  · exact hc
  · exact hcSupp
  · exact hcPos
  · exact hcNull
  · exact color_region_exterior (Sum.inl '' I) (Sum.inl '' J) c (μ z s q)
      hcSupp (fun v hv hj=>hdata v (Or.inl ⟨hv,hj⟩))
  · exact source_isolated_interior M I J hJI hJ z s q c hcNull hdata hcap huniv
  · exact hsoc

end HarmonicArtin

end OAI
