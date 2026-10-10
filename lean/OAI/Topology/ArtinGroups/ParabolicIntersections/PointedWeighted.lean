import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedMultiplicity
import OAI.Topology.ArtinGroups.Harmonic.FrameFamily

namespace OAI

/-! Weighted multiplicities for the family based at any original color. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma pointedFamily_mul (g x : Artin M) (L : FusionLabel m) :
    pointedFamily M f (g*x) L = sourceArtinAction M g (pointedFamily M f x L) := by
  simp only [pointedFamily, pointedAction, map_mul, Equiv.Perm.mul_apply]

lemma pointedMultiplicity_word (w : List (S × Bool)) (k : ℤ) :
    pointedMultiplicity M f (sourceSignedWord M w) k =
      fusionOrbitMultiplicity m d hd diag hm (sourcePacketWord w) (.inl f) k := by
  unfold pointedMultiplicity
  rw [pointedFamily_word, fusionFamilyMultiplicity_orbit]

lemma pointedFamily_weighted_level (z : Artin M) (q : ℤ)
    (α : FusionVertex (V := S ⊕ Unit) m) :
    (∑ H, fusionWeight m H * (classLevelArray Q (pointedFamily M f z H) (α,q) : ℝ)) =
      fusionWeight m α.2 * pointedMultiplicity M f z q α.1 := by
  obtain ⟨w,rfl⟩ := sourceSignedWord_surjective M z
  rw [pointedMultiplicity_word, pointedFamily_word]
  have h := congrFun (fusionOrbitWeightedVector_eq m d hd diag hm (sourcePacketWord w) (.inl f) q) α
  simpa only [fusionOrbitWeightedVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    fusionOrbitLayer_generator, fusionFold] using h

lemma pointedMultiplicity_exterior_ordered (J : Set S) (g : Artin M)
    (hg : g ∈ artinParabolic M J) (x : Artin M) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' J) (k : ℤ) :
    pointedMultiplicity M f (g*x) k v = pointedMultiplicity M f x k v :=
  pointedMultiplicity_exterior M J g hg f x v hv k

end HarmonicArtin.ParabolicIntersections

end OAI
