import OAI.Topology.ArtinGroups.Harmonic.Coset
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile

namespace OAI

/-! Exact counts and harmonic vectors at the initial pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

@[simp] lemma pointedFamily_one (L : FusionLabel m) :
    pointedFamily M f 1 L = initialClass Q (.inl f,L) := by
  simp only [pointedFamily, pointedAction, map_one, Equiv.Perm.one_apply, pointedInitial]

lemma pointedMultiplicity_one (k : ℤ) (v : S ⊕ Unit) :
    pointedMultiplicity M f 1 k v = if v = .inl f ∧ k = 0 then 1 else 0 := by
  rw [pointedMultiplicity_sum]
  simp only [pointedFamily_one, classLevelArray_initial, Prod.mk.injEq]
  by_cases hv : v = .inl f
  · subst v
    by_cases hk : k = 0
    · subst k
      simp only [true_and, and_true, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite,
        _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact div_self (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) _))
    · simp only [hk, and_false, ite_false, Nat.cast_zero, MulZeroClass.mul_zero,
        Finset.sum_const_zero, zero_div]
  · have hv' : (.inl f : S ⊕ Unit) ≠ v := Ne.symm hv
    simp only [hv, hv', false_and, ite_false, Nat.cast_zero, MulZeroClass.mul_zero,
      Finset.sum_const_zero, zero_div]

lemma pointedHarmonicAt_empty (x : Artin M) (k : ℤ) :
    pointedHarmonicAt M f ∅ x k = pointedMultiplicity M f x k := by
  funext i
  exact pointedHarmonicAt_outside M f ∅ x k i (by simp)

lemma pointedCosetVector_empty (x : Artin M) (k : ℤ) :
    pointedCosetVector M f (sourceCoset M ∅ (spherical_empty M) x) k =
      pointedMultiplicity M f x k := by
  rw [pointedCosetVector_eq M f _ x (rightCoset_self M ∅ x) k]
  exact pointedHarmonicAt_empty M f x k

end HarmonicArtin.ParabolicIntersections

end OAI
