import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ArtinActionWordArtin
import OAI.Topology.ArtinGroups.Realizations.WeightedReflectedHigh
import OAI.Topology.ArtinGroups.Harmonic.RootExtension
import OAI.Topology.ArtinGroups.Harmonic.CanonicalLowSupport

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

omit [Fintype S] [LinearOrder S] in
lemma sourceRootInclusion_range (J:Set S) : Set.range (sourceRootInclusion J)=Sum.inl '' J := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩; exact ⟨j,j.property,rfl⟩
  · rintro ⟨j,hj,rfl⟩; exact ⟨⟨j,hj⟩,rfl⟩

theorem source_chamber_identity (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v) (j:J) :
    μ (negativePrepend (u.map (sourceRootInclusion J)) z) s q (.inl (j:S))-p (.inl (j:S))=
      representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd u.reverse)
        ((μ z s q-p)∘sourceRootInclusion J-
          (σ (u.map (sourceRootInclusion J)) z s q)∘sourceRootInclusion J) j := by
  let f:=sourceRootInclusion J
  let a:=μ z s q
  let b:=σ (u.map f) z s q
  have hs:∀ v,v∉Sum.inl '' J→b v=0:=sourceCanonicalMultiplicity_support M J hJ u hu z s q
  have hv:∀ v,v∉Set.range f→((a-b)-p) v=0 := by
    intro v hv
    have hn:v∉Sum.inl '' J:=by simpa only [f,sourceRootInclusion_range] using hv
    simp only [Pi.sub_apply,a,hext v hn,hs v hn,sub_zero,sub_self]
  have hfix:rowReflectWord C (u.map f).reverse p=p := by
    apply rowReflectWord_harmonic
    intro v hv
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hv)
    exact hp i
  have href:μ (negativePrepend (u.map f) z) s q=rowReflectWord C (u.map f).reverse (a-b) := by
    convert source_weighted_reflected_high M J hJ u hu z s q hcap using 1 <;>
      congr 9
  have hvec:μ (negativePrepend (u.map f) z) s q-p=
      rootExtension f (representation (restrictedMatrix M J).toCoxeterSystem
        ((restrictedMatrix M J).toCoxeterSystem.wordProd u.reverse)
        ((a-p)∘f-b∘f)) := by
    conv_lhs => rw [href,← hfix,← rowReflectWord_sub]
    rw [← rootExtension_restrict f (sourceRootInclusion_injective J) ((a-b)-p) hv]
    have he:(((a-b)-p)∘f)=((a-p)∘f-b∘f) := by ext i; simp only [Function.comp_apply,Pi.sub_apply]; ring
    rw [he,← List.map_reverse]
    exact sourceRoot_word_representation M J u.reverse _
  have hval:=congrFun hvec (f j)
  rw [rootExtension_apply f (sourceRootInclusion_injective J)] at hval
  exact hval

lemma source_negative_representative (J:Set S) (u:List J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    ∃ g∈artinParabolic M J,
      (∀ L,O (negativePrepend (u.map (sourceRootInclusion J)) z) s L=
        sourceArtinAction M g (O z s L)) ∧
      (∀ L,ClassCapOn Q (O (negativePrepend (u.map (sourceRootInclusion J)) z) s L)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) := by
  let a:=wordArtin M (u.map Subtype.val)
  have ha:a∈artinParabolic M J:=wordArtin_mem_parabolic M J _
    (by intro i hi;obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi;exact j.property)
  refine ⟨a⁻¹,(artinParabolic M J).inv_mem ha,?_,?_⟩
  · intro L
    rw [fusionPacketOrbit_negativePrepend,sourceArtinAction_negativeWord]
    simp only [List.map_map,Function.comp_def]
    congr 9
    exact Subsingleton.elim _ _
  · intro L
    rw [fusionPacketOrbit_negativePrepend]
    convert inverseWord_capOn Q _ _ _ q (hcap L) (unfolded_full_word_mem M J u) using 1
    congr 9
    exact Subsingleton.elim _ _

end HarmonicArtin

end OAI
