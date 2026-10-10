import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicReadReduced
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom
import OAI.Topology.ArtinGroups.Coxeter.AltListReduced
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRelations

namespace OAI

/-! The parabolic read respects braid relations by the reduced-word theorem. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

/-- Equal reduced galleries have equal positive reads in the parabolic. -/
theorem parabolicRead_word_eq (w : M.Group) (u v : List S)
    (hu : (cs).IsReduced u) (hv : (cs).IsReduced v) (he : (cs).wordProd u=(cs).wordProd v) :
    wordArtin R (parabolicRead cs J w u)=wordArtin R (parabolicRead cs J w v) := by
  suffices h : wordPositive R (parabolicRead cs J w u)=wordPositive R (parabolicRead cs J w v) by
    simpa only [positiveToArtin_word] using congrArg (positiveToArtin R) h
  apply wordPositive_eq_of_reduced R _ _
      ((restriction_reduced_iff M J _).mp (parabolicRead_reduced cs J w u hu))
      ((restriction_reduced_iff M J _).mp (parabolicRead_reduced cs J w v hv))
  apply restrictionHom_injective M J
  change restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.wordProd (parabolicRead cs J w u)) =
    restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.wordProd (parabolicRead cs J w v))
  rw [restriction_wordProd,restriction_wordProd,parabolicRead_product,parabolicRead_product,he]

/-- The precise braid compatibility needed for the parabolic retraction. -/
theorem parabolicRead_braid (w : M.Group) (i j : S) :
    wordArtin R (parabolicRead cs J w (altList i j (M i j))) =
      wordArtin R (parabolicRead cs J w (altList j i (M i j))) := by
  by_cases hij : i=j
  · subst j; rfl
  apply parabolicRead_word_eq M J w
  · exact altList_reduced cs i j hij _ (Or.inr le_rfl)
  · exact altList_reduced cs j i (Ne.symm hij) _ (Or.inr (le_of_eq (M.symmetric i j)))
  · exact altList_braid cs i j

end HarmonicArtin.ParabolicIntersections

end OAI
