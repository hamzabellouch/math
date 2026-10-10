import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitMultiplicity
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLowCount
import OAI.Topology.ArtinGroups.Complexes.TotalVectorLayer

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)

lemma fusionOrbitWeightedVector_class (z:List (V×Bool)) (s:V) (q:ℤ) :
    fusionOrbitWeightedVector m d hd hdiag z s q=
      ∑ L,fusionWeight m L • classTotalVector Q (classLayer Q q (O z s L)) := by
  simp only [fusionOrbitWeightedVector,classTotalVector_layer]
  rfl

noncomputable def canonicalFusionMultiplicity (w:List V) (z:List (V×Bool))
    (s:V) (q:ℤ) (v:V) : ℝ :=
  Classical.choose (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)

lemma canonicalFusionMultiplicity_nonneg (w:List V) (z:List (V×Bool))
    (s:V) (q:ℤ) (v:V) : 0≤canonicalFusionMultiplicity m d hd hdiag hm w z s q v :=
  (Classical.choose_spec (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)).1

lemma canonicalFusionMultiplicity_fold (w:List V) (z:List (V×Bool)) (s:V) (q:ℤ)
    (hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L)))) :
    (∑ L,fusionWeight m L • classTotalVector Q (C w q (classLayer Q q (O z s L))))=
      fusionFold m (canonicalFusionMultiplicity m d hd hdiag hm w z s q) := by
  ext ⟨v,L⟩
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [classTotalVector_pure_apply Q _ q (hp _).1 (hp _).2]
  have hc:=(Classical.choose_spec
    (canonicalFusionLow_count_proportional m d hd hdiag hm w z s v q q)).2 L
  simpa only [fusionFold,canonicalFusionMultiplicity,mul_comm] using hc

end HarmonicArtin

end OAI
