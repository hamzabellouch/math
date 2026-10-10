import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ConvexWord

namespace OAI

namespace HarmonicArtin

lemma convexHull_of_supported_comp {I V B:Type*} (f:I→V)
    (u:V→ℝ) (s:B→V→ℝ)
    (hu:∀v,v∉Set.range f→u v=0)
    (hs:∀b v,v∉Set.range f→s b v=0)
    (h:(u∘f)∈convexHull ℝ (Set.range fun b=>s b∘f)) :
    u∈convexHull ℝ (Set.range s) := by
  classical
  let E:(I→ℝ)→ₗ[ℝ](V→ℝ):=
    { toFun:=fun x v=>if hv:∃i,f i=v then x (Classical.choose hv) else 0
      map_add':=by intros; funext v; dsimp; split <;> simp
      map_smul':=by intros; funext v; dsimp; split <;> simp }
  have he (x:V→ℝ) (hx:∀v,v∉Set.range f→x v=0):E (x∘f)=x := by
    funext v
    dsimp [E]
    split
    · rename_i hv
      rw [Classical.choose_spec hv]
    · rename_i hv
      exact (hx v hv).symm
  have hh:E (u∘f)∈E '' convexHull ℝ (Set.range fun b=>s b∘f):=⟨_,h,rfl⟩
  rw [E.image_convexHull,← Set.range_comp] at hh
  have hr : (fun b=>E (s b∘f))=s := funext (fun b=>he (s b) (hs b))
  change E (u∘f)∈convexHull ℝ (Set.range (fun b=>E (s b∘f))) at hh
  rwa [he u hu,hr] at hh

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
local notation "C" => fusionFoldedCartan m d

lemma source_convex_subobjects_full (J:Set S) (hJ:IsSpherical M J)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) (p:S⊕Unit→ℝ)
    (hcap:∀ L,ClassCapOn Q (O z s L) (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀ j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀ v,v∉Sum.inl '' J→μ z s q v=p v)
    (huniv:∀ g∈artinParabolic M J,
      (∀ L,ClassCapOn Q (sourceArtinAction M g (O z s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀ j:J,p (.inl (j:S))≤fusionFamilyMultiplicity m d hd hm
        (fun L=>sourceArtinAction M g (O z s L)) q (.inl (j:S))) :
    (μ z s q-p)∈convexHull ℝ (Set.range (sourceConvexVector M J z s q)) := by
  have hr:Set.range (sourceRootInclusion J)=Sum.inl '' J := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.property,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
  apply convexHull_of_supported_comp (sourceRootInclusion J) _ _
  · intro v hv
    rw [hr] at hv
    exact sub_eq_zero.mpr (hext v hv)
  · intro w v hv
    rw [hr] at hv
    exact sourceConvexVector_support M J hJ z s q w v hv
  · exact source_convex_subobjects M J hJ z s q p hcap hp hext huniv

end HarmonicArtin

end OAI
