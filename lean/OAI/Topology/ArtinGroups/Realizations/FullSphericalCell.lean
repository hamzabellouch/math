import Mathlib
import OAI.Topology.ArtinGroups.Realizations.PositiveLiftedCell

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

omit [Fintype S] in
lemma right_minimum_of_longest_additive (R : Set S) (q : M.Group)
    (hq : IsParabolicLongest M R q) (w : M.Group)
    (hw : M.toCoxeterSystem.length (w*q) =
      M.toCoxeterSystem.length w + M.toCoxeterSystem.length q) :
    ∀ v : coxeterParabolic M R,
      M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length (w*v) := by
  intro v
  have hv : v.val⁻¹*q ∈ coxeterParabolic M R :=
    (coxeterParabolic M R).mul_mem ((coxeterParabolic M R).inv_mem v.property) hq.1
  have hb := hq.2 _ hv
  have hl := M.toCoxeterSystem.length_mul_le (w*v.val) (v.val⁻¹*q)
  have he : w*v.val*(v.val⁻¹*q) = w*q := by group
  rw [he,hw] at hl
  omega

noncomputable def fullSphericalCell [Finite M.Group] : LiftedCell M :=
  (1,⟨Set.univ,show Finite (coxeterParabolic M Set.univ) from inferInstance⟩)

theorem positiveCell_face_full_of_top_prefix [Finite M.Group]
    (a : PositiveLiftedCell M)
    (h : PositivePrefix M (positiveCellTop M a)
      (positiveSimpleLift M (sphericalLongest M (fullSphericalCell M).2))) :
    LiftedFace M (positiveCellToLifted M a) (fullSphericalCell M) := by
  have ht : positiveCellTop M a = positiveSimpleLift M (positiveToCoxeter M (positiveCellTop M a)) :=
    positivePrefix_of_simple_eq M h rfl
  have ha : a.1 = positiveSimpleLift M (positiveToCoxeter M a.1) :=
    (positive_simple_factors M a.1 (positiveSimpleLift M (sphericalLongest M a.2))
      (positiveToCoxeter M (positiveCellTop M a)) ht).1
  have hlen : M.toCoxeterSystem.length
      (positiveToCoxeter M a.1 * sphericalLongest M a.2) =
        M.toCoxeterSystem.length (positiveToCoxeter M a.1) +
          M.toCoxeterSystem.length (sphericalLongest M a.2) := by
    have hd := congrArg (positiveDegree M) ht
    simp only [positiveCellTop,map_mul,positiveToCoxeter_simpleLift,
      positiveDegree_mul,positiveDegree_simpleLift] at hd
    rw [ha,positiveDegree_simpleLift] at hd
    simpa only [positiveToCoxeter_simpleLift] using hd.symm
  let w := reducedExpression M (positiveToCoxeter M a.1)
  have hr := reducedExpression_reduced M (positiveToCoxeter M a.1)
  have he := wordCoxeter_reducedExpression M (positiveToCoxeter M a.1)
  refine ⟨Set.subset_univ _,w,(by intros; trivial),hr,?_,?_⟩
  · rw [he]
    exact right_minimum_of_longest_additive M a.2.val _ (sphericalLongest_spec M a.2) _ hlen
  · change positiveToArtin M a.1 = 1 * wordArtin M w
    rw [one_mul,ha,positiveToArtin_simpleLift,←he,positiveLift_word M w hr]

end HarmonicArtin

end OAI
