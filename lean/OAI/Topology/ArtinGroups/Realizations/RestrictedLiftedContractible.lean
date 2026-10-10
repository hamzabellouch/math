import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.TypedRightCoset
import OAI.Topology.ArtinGroups.Harmonic.PositiveUpperBoundaryRank
import OAI.Topology.ArtinGroups.Realizations.DirectedCoverSequence
import OAI.Topology.ArtinGroups.Harmonic.PositiveRegionDeckIso

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

theorem restricted_lifted_contractible (T : Set S) (hT : IsSpherical M T) :
    ContractibleSpace (OrderWeights (LiftedCell (restrictedMatrix M T))) := by
  let N := restrictedMatrix M T
  let : Finite N.Group := restricted_finite M T hT
  let : Countable (Artin N) :=
    Function.Surjective.countable (PresentedGroup.mk_surjective (braidRelators N))
  obtain ⟨z,hz⟩ := exists_longest N.toCoxeterSystem
  let inj := spherical_positiveToArtin_injective M T hT
  have hpos : ContractibleSpace (OrderWeights (PositiveRegion N 1)) :=
    (weightHomeomorph (positiveCellRegionIso N inj)).contractibleSpace_iff.mp
      (positiveCellPoset_contractible N z hz inj)
  apply orderWeights_contractible_of_countable_directed_cover (PositiveRegion N)
    (spherical_positiveRegions_directed M T hT) (fun a => ⟨a.1,1,by simp⟩)
    (positiveRegion_face_closed N)
    (fun g => (weightHomeomorph (positiveRegionDeckIso N g)).contractibleSpace_iff.mp hpos)
    (fun a => a.2.val.ncard) (Nat.card T) (lifted_rank_bound N) (lifted_rank_strict N)

theorem sphericalLiftedFiber_contractible (T : Set S) (hT : IsSpherical M T) :
    ContractibleSpace (OrderWeights (SphericalLiftedFiber M T)) :=
  (weightHomeomorph (restrictedLiftedFiberIso M T hT)).contractibleSpace_iff.mp
    (restricted_lifted_contractible M T hT)

theorem source_salvetti_cover_contractible : ContractibleSpace (SalvettiCover M) :=
  salvetti_cover_contractible_of_spherical_fibers M (sphericalLiftedFiber_contractible M)

end HarmonicArtin

end OAI
