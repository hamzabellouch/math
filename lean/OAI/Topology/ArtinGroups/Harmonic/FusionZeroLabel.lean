import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UnfoldedCartanSymm
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionMultiplicity

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd

def fusionZeroLabel : FusionLabel m := fun e=>⟨0,by have:=hm e;omega⟩

noncomputable def fusionFamilyMultiplicity (x:FusionLabel m→FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (v:V) : ℝ :=
  (∑ L,fusionWeight m L * classTotalVector Q (classLayer Q q (x L)) (v,fusionZeroLabel m hm)) /
    fusionWeight m (fusionZeroLabel m hm)

lemma fusionFamilyMultiplicity_nonneg (x:FusionLabel m→FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (v:V) : 0≤fusionFamilyMultiplicity m d hd hm x q v := by
  apply div_nonneg _ (fusionWeight_pos m hm _).le
  exact Finset.sum_nonneg (fun L _=>mul_nonneg (fusionWeight_pos m hm L).le
    (generatorVector_nonneg Q _ _))

lemma fusionFamilyMultiplicity_orbit (hdiag:∀ s,d s s=.units 0)
    (z:List (V×Bool)) (s:V) (q:ℤ) :
    fusionFamilyMultiplicity m d hd hm (fusionPacketOrbit m d hd hdiag z s) q=
      fusionOrbitMultiplicity m d hd hdiag hm z s q := by
  funext v
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm z s q) (v,fusionZeroLabel m hm)
  rw [fusionOrbitWeightedVector_class] at h
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,fusionFold] at h
  unfold fusionFamilyMultiplicity
  rw [h]
  exact mul_div_cancel_left₀ _ (ne_of_gt (fusionWeight_pos m hm _))

end HarmonicArtin

end OAI
