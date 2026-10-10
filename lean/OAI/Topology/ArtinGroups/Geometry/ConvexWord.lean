import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ChamberInequalitiesConvexHull
import OAI.Topology.ArtinGroups.Harmonic.FusionZeroLabel
import OAI.Topology.ArtinGroups.Harmonic.RootInclusionRange

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
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

noncomputable def sourceConvexWord (J:Set S) (w:(restrictedMatrix M J).Group) : List J :=
  reducedExpression (restrictedMatrix M J) w⁻¹

omit [Fintype S] [LinearOrder S] in
lemma sourceConvexWord_reduced (J:Set S) (w:(restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.IsReduced (sourceConvexWord M J w) :=
  reducedExpression_reduced _ _

omit [Fintype S] [LinearOrder S] in
lemma sourceConvexWord_reverse (J:Set S) (w:(restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.wordProd (sourceConvexWord M J w).reverse=w := by
  rw [CoxeterSystem.wordProd_reverse]
  have h:(restrictedMatrix M J).toCoxeterSystem.wordProd (sourceConvexWord M J w)=w⁻¹:=
    wordCoxeter_reducedExpression _ _
  rw [h,inv_inv]

noncomputable def sourceConvexVector (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) : S⊕Unit→ℝ :=
  σ ((sourceConvexWord M J w).map (sourceRootInclusion J)) z s q

noncomputable def sourceConvexModel (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) : FiniteModel Q (K:=ℂ) :=
  minimalClassModel Q (canonicalFusionLow m d hd hdiag
    ((sourceConvexWord M J w).map (sourceRootInclusion J)) q (classLayer Q q (O z s L)))

lemma sourceConvexModel_pure (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    ∀ i,((sourceConvexModel M J z s q w L).complex.placement i).level=q := by
  have h:=sourceCanonicalLow_pure M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q (classLayer Q q (O z s L))
    (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)
  exact fun i=>le_antisymm (h.2 i) (h.1 i)

lemma sourceConvexModel_inclusion (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    Nonempty (TermwiseSplitInjection Q (sourceConvexModel M J z s q w L).complex
      (minimalClassModel Q (classLayer Q q (O z s L))).complex) :=
  sourceCanonicalLow_termwiseSplit M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)

lemma sourceConvexModel_support (J:Set S) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) (L:FusionLabel m) :
    ∀ i,((sourceConvexModel M J z s q w L).complex.placement i).color∈Set.range (unfoldedInclusion M J) :=
  sourceCanonicalLow_support M J (sourceConvexWord M J w) z s q L

lemma sourceConvexModel_counts (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) :
    (∑ L,fusionWeight m L • generatorVector Q (sourceConvexModel M J z s q w L).complex)=
      fusionFold m (sourceConvexVector M J z s q w) := by
  apply canonicalFusionMultiplicity_fold
  intro L
  exact sourceCanonicalLow_pure M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)

lemma sourceConvexVector_support (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (w:(restrictedMatrix M J).Group) :
    ∀ v,v∉Sum.inl '' J→sourceConvexVector M J z s q w v=0 :=
  sourceCanonicalMultiplicity_support M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) z s q

lemma sourceConvex_representative (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v) (w:(restrictedMatrix M J).Group) :
    ∃ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) ∧
      (∀ j:J,fusionFamilyMultiplicity m d hd hm (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))-
        p (.inl (j:S))=representation (restrictedMatrix M J).toCoxeterSystem w
          ((μ z s q-p)∘sourceRootInclusion J-(sourceConvexVector M J z s q w)∘sourceRootInclusion J) j) := by
  obtain ⟨g,hg,he,hc⟩:=source_negative_representative M J (sourceConvexWord M J w) z s q hcap
  have he':(fun L=>sourceArtinAction M g (O z s L))=
      O (negativePrepend ((sourceConvexWord M J w).map (sourceRootInclusion J)) z) s :=
    funext (fun L=>(he L).symm)
  refine ⟨g,hg,fun L=>he L ▸ hc L,?_⟩
  intro j
  rw [he',fusionFamilyMultiplicity_orbit]
  have h:=source_chamber_identity M J hJ (sourceConvexWord M J w)
    (sourceConvexWord_reduced M J w) z s q p hcap hp hext j
  rw [sourceConvexWord_reverse] at h
  exact h

theorem source_convex_subobjects (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))≤fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    ((μ z s q-p)∘sourceRootInclusion J)∈convexHull ℝ
      (Set.range fun w=>(sourceConvexVector M J z s q w)∘sourceRootInclusion J) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let := Fintype.ofFinite (restrictedMatrix M J).Group
  apply chamber_inequalities_convexHull (restrictedMatrix M J).toCoxeterSystem
  intro w j
  obtain ⟨g,hg,hc,he⟩:=sourceConvex_representative M J hJ z s q p hcap hp hext w
  rw [← he j]
  exact sub_nonneg.mpr (huniv g hg hc j)

theorem source_convex_subobjects_interior (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))<fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    ((μ z s q-p)∘sourceRootInclusion J)∈interior (convexHull ℝ
      (Set.range fun w=>(sourceConvexVector M J z s q w)∘sourceRootInclusion J)) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let := Fintype.ofFinite (restrictedMatrix M J).Group
  apply chamber_inequalities_interior (restrictedMatrix M J).toCoxeterSystem
  intro w j
  obtain ⟨g,hg,hc,he⟩:=sourceConvex_representative M J hJ z s q p hcap hp hext w
  rw [← he j]
  exact sub_pos.mpr (huniv g hg hc j)

end HarmonicArtin

end OAI
