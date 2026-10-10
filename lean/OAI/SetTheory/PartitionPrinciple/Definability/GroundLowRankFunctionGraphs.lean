import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInaccessibleOrdinalClosure
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStandardInaccessible

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation collection infinite hK

theorem functionGraphOn_rank_lt {I f : ZFSet.{u}} (hI : I ∈ K) (hf : f ∈ M.sets)
    (function : FunctionGraphOn I f)
    (values : ∀ i ∈ I, ∀ v, ZFSet.pair i v ∈ f → ZFSet.rank v < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  have hIM := M.transitive hK hI
  have smallI := GroundBelow.of_member pairing unions powers separation hK hI
  have smallF := smallI.functionGraphOn pairing unions powers separation hIM hf hK function
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  apply conditions.2.2.1.rank_lt_of_small pairing unions powers separation collection
    hf hK conditions.1 smallF
  intro z hz
  obtain ⟨i, hi, v, rfl⟩ := function.shape z hz
  exact rank_orderedPair_lt limit
    ((ZFSet.rank_lt_of_mem hi).trans (ZFSet.rank_lt_of_mem hI)) (values i hi v hz)

theorem functionGraph_rank_lt_cumulative {I V f : ZFSet.{u}}
    (hI : I ∈ K) (hf : f ∈ M.sets) (function : ZFSet.IsFunc I V f)
    (level : ∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt pairing unions powers separation collection infinite
    hK hI hf ⟨V, function⟩
  intro i _ v entry
  exact ((level v).1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2).2

theorem functionGraph_rank_lt_hierarchy {I V H f : ZFSet.{u}}
    (hI : I ∈ K) (hf : f ∈ M.sets) (function : ZFSet.IsFunc I V f)
    (hierarchy : GroundCumulativeHierarchyCode M (insert K K) H)
    (level : ZFSet.pair K V ∈ H) : ZFSet.rank f < ZFSet.rank K :=
  conditions.functionGraph_rank_lt_cumulative pairing unions powers separation collection infinite
    hK hI hf function (hierarchy.mem_iff_rank_lt (ordinalSetProperty_succ conditions.1)
      (ZFSet.mem_insert K K) level)

end PartitionPilot.Forcing.GroundInaccessibleConditions

end

end OAI
