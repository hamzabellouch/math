import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBelowExternalPoints

namespace OAI

section

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T U A E K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem indexedCarrierLabels (hT : T ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M T K) (points : GroundBelow M U K) :
    GroundBelow M (Forcing.indexedCarrierLabels T U A) K :=
  (GroundBelow.product pairing unions powers separation hT hU hK ordinal strong indices points).restrict
    separation (M.indexedCarrierLabels_mem pairing unions powers separation hT hU hA) hK
    (indexedCarrierLabels_subset T U A)

theorem indexedCarrierClasses (hT : T ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets)
    (hE : E ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M T K) (points : GroundBelow M U K) :
    GroundBelow M (Forcing.equivalenceClasses (Forcing.indexedCarrierLabels T U A) E) K :=
  GroundBelow.equivalenceClasses pairing unions powers separation
    (M.indexedCarrierLabels_mem pairing unions powers separation hT hU hA) hE hK strong
    (GroundBelow.indexedCarrierLabels pairing unions powers separation hT hU hA hK ordinal strong indices points)

end PartitionPilot.Forcing.GroundBelow

end

end OAI
