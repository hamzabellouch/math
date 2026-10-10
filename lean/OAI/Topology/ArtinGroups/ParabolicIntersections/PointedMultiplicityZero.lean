import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.MultiplicityZero
import Mathlib
import OAI.Topology.ArtinGroups.Realizations.FrameFamilyWeightedLevel

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedMultiplicity_zero_iff (z:Artin M) (q:ℤ) (v:S⊕Unit) :
    pointedMultiplicity M f z q v=0 ↔
      ∀ H L,classLevelArray Q (pointedFamily M f z H) ((v,L),q)=0 := by
  constructor
  · intro hz H L
    have he:=pointedFamily_weighted_level M f z q (v,L)
    rw [hz,MulZeroClass.mul_zero] at he
    have hnn:∀ H:FusionLabel m,0≤fusionWeight m H *
        (classLevelArray Q (pointedFamily M f z H) ((v,L),q):ℝ) := by
      intro H
      exact mul_nonneg (fusionWeight_pos m (fusionLabelSize_ge_two M) H).le (Nat.cast_nonneg _)
    have hh:= (Finset.sum_eq_zero_iff_of_nonneg (fun H _=>hnn H)).mp he H (Finset.mem_univ H)
    have hz':(classLevelArray Q (pointedFamily M f z H) ((v,L),q):ℝ)=0 :=
      (mul_eq_zero.mp hh).resolve_left (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) H))
    exact_mod_cast hz'
  · intro hz
    let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
    have he:=pointedFamily_weighted_level M f z q (v,L)
    simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left
      (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) L))

lemma pointedNumericCap_iff (z:Artin M) (q:ℤ) (U:Set (S⊕Unit)) :
    (∀v∈U,∀k:ℤ,q<k→pointedMultiplicity M f z k v=0) ↔
      ∀H,ClassCapOn Q (pointedFamily M f z H) (fusionColorRegion m U) q := by
  constructor
  · intro h H
    rw [classCapOn_iff_level_zero]
    intro α hα k hk
    exact (pointedMultiplicity_zero_iff M f z k α.1).mp (h α.1 hα k hk) H α.2
  · intro h v hv k hk
    rw [pointedMultiplicity_zero_iff]
    intro H L
    exact (classCapOn_iff_level_zero Q _ _ _).mp (h H) (v,L) hv k hk

end HarmonicArtin.ParabolicIntersections

end OAI
