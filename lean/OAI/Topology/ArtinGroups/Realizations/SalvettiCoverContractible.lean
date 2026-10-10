import Mathlib
import OAI.Topology.ArtinGroups.Realizations.RestrictedLiftedContractible
import OAI.Topology.ArtinGroups.Harmonic.SphericalTypeReindex

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

theorem salvetti_cover_contractible [Finite S] (M : CoxeterMatrix S) : ContractibleSpace (SalvettiCover M) := by
  let := Fintype.ofFinite S
  let e := Fintype.equivFin S
  have hc : ContractibleSpace (OrderWeights (LiftedCell (M.reindex e))) :=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (source_salvetti_cover_contractible (M.reindex e))
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    ((weightHomeomorph (liftedReindex M e)).contractibleSpace_iff.mpr hc)

end HarmonicArtin

end OAI
