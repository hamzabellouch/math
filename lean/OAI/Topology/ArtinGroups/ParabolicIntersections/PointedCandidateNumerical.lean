import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCandidateCapped
import OAI.Topology.ArtinGroups.Harmonic.FoldedSphericalPos
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CandidateCapped

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "C" => fusionFoldedCartan m d

theorem pointedCandidate_numerical_unique (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' := by
  have hforward:∀s∈T,s∉J'→p (.inl s)≤p' (.inl s):=by
    intro s hs hj
    have hv:(Sum.inl s:S⊕Unit)∉Sum.inl '' J':=by
      rintro ⟨t,ht,he⟩
      exact hj (Sum.inl.inj he ▸ ht)
    rw [←Y.exterior (.inl s) hv]
    exact pointedCandidate_le_capped M f T J z h q p X hh
      (fun H i hi=>Y.cap H i (Or.inl hi)) s hs
  have hreverse:∀s∈T,s∉J→p' (.inl s)≤p (.inl s):=by
    intro s hs hj
    have hv:(Sum.inl s:S⊕Unit)∉Sum.inl '' J:=by
      rintro ⟨t,ht,he⟩
      exact hj (Sum.inl.inj he ▸ ht)
    have hm:=pointedCandidate_le_capped M f T J' (h*z) h⁻¹ q p' Y ((artinParabolic M T).inv_mem hh)
      (by rw [inv_mul_cancel_left]; exact fun H i hi=>X.cap H i (Or.inl hi)) s hs
    simpa only [inv_mul_cancel_left,X.exterior (.inl s) hv] using hm
  have hext:∀v,v∉Sum.inl '' T→p v=p' v := by
    intro v hv
    have hvJ:v∉Sum.inl '' J:=fun ⟨s,hs,he⟩=>hv ⟨s,X.subset hs,he⟩
    have hvJ':v∉Sum.inl '' J':=fun ⟨s,hs,he⟩=>hv ⟨s,Y.subset hs,he⟩
    rw [←X.exterior v hvJ,←Y.exterior v hvJ',pointedMultiplicity_exterior_ordered M f T h hh z v hv q]
  let f:=sourceRootInclusion T
  let a:T→ℝ:=fun i=>-(C *ᵥ p) (f i)
  let a':T→ℝ:=fun i=>-(C *ᵥ p') (f i)
  have hf:Function.Injective f:=sourceRootInclusion_injective T
  have he:rootExtension f ((p'-p)∘f)=p'-p:=rootExtension_restrict f hf (p'-p) (by
    intro v hv
    apply sub_eq_zero.mpr
    apply (hext v ?_).symm
    rintro ⟨s,hs,rfl⟩
    exact hv ⟨⟨s,hs⟩,rfl⟩)
  have hrow:a'-a=-((C).submatrix f f *ᵥ ((p'∘f)-(p∘f))) := by
    funext i
    have hc:=rootExtension_mulVec C f ((p'-p)∘f) i
    rw [he,mulVec_sub] at hc
    change -(C *ᵥ p') (f i) - -(C *ᵥ p) (f i)= -(_)
    change (C *ᵥ p') (f i)-(C *ᵥ p) (f i)=_ at hc
    have hd:(p'∘f)-(p∘f)=(p'-p)∘f:=rfl
    rw [hd,←hc]
    ring
  have hfor:0≤a' ⬝ᵥ ((p'∘f)-(p∘f)) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hj:(i:S)∈J'
    · have hz:=Y.harmonic ⟨i,hj⟩
      change -(C *ᵥ p') (.inl (i:S)) * (p' (.inl (i:S))-p (.inl (i:S)))≥0
      rw [hz,neg_zero,MulZeroClass.zero_mul]
    · exact mul_nonneg (neg_nonneg.mpr (Y.cartan_nonpos i i.property))
        (sub_nonneg.mpr (hforward i i.property hj))
  have hrev:0≤a ⬝ᵥ ((p∘f)-(p'∘f)) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hj:(i:S)∈J
    · have hz:=X.harmonic ⟨i,hj⟩
      change -(C *ᵥ p) (.inl (i:S)) * (p (.inl (i:S))-p' (.inl (i:S)))≥0
      rw [hz,neg_zero,MulZeroClass.zero_mul]
    · exact mul_nonneg (neg_nonneg.mpr (X.cartan_nonpos i i.property))
        (sub_nonneg.mpr (hreverse i i.property hj))
  have hp:=harmonic_two_point_equality ((C).submatrix f f) (source_folded_spherical_posDef M T hT)
    (p∘f) (p'∘f) a a' hrow hfor hrev
  have hep:p=p':=by
    funext v
    by_cases hv:v∈Sum.inl '' T
    · obtain ⟨s,hs,rfl⟩:=hv
      exact congrFun hp.1 ⟨s,hs⟩
    · exact hext v hv
  refine ⟨hep,?_⟩
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hj
    have hn:=Y.negative s (X.subset hs) hj
    rw [←hep,X.harmonic ⟨s,hs⟩] at hn
    exact lt_irrefl _ hn
  · intro s hs
    by_contra hj
    have hn:=X.negative s (Y.subset hs) hj
    rw [hep,Y.harmonic ⟨s,hs⟩] at hn
    exact lt_irrefl _ hn

end HarmonicArtin.ParabolicIntersections

end OAI
