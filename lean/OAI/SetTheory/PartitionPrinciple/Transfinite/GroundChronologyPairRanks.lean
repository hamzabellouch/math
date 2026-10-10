import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowRelationSpaces
import OAI.SetTheory.PartitionPrinciple.Definability.GroundLowRankFunctionGraphs

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

theorem functionGraphOn_rank_lt_small {I f : ZFSet.{u}}
    (hI : I ∈ M.sets) (small : GroundBelow M I K)
    (inputs : ∀ i ∈ I, ZFSet.rank i < ZFSet.rank K)
    (hf : f ∈ M.sets) (function : FunctionGraphOn I f)
    (values : ∀ i ∈ I, ∀ v, ZFSet.pair i v ∈ f → ZFSet.rank v < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  have smallF := small.functionGraphOn pairing unions powers separation hI hf hK function
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  apply conditions.2.2.1.rank_lt_of_small pairing unions powers separation collection
    hf hK conditions.1 smallF
  intro z hz
  obtain ⟨i, hi, v, rfl⟩ := function.shape z hz
  exact rank_orderedPair_lt limit (inputs i hi) (values i hi v hz)

theorem functionGraph_rank_lt_small_cumulative {I V f : ZFSet.{u}}
    (hI : I ∈ M.sets) (small : GroundBelow M I K)
    (inputs : ∀ i ∈ I, ZFSet.rank i < ZFSet.rank K)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc I V f)
    (level : ∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt_small pairing unions powers separation collection
    infinite hK hI small inputs hf ⟨V, function⟩
  intro i _ v entry
  exact ((level v).1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2).2

theorem functionGraph_rank_lt_small_hierarchy {I V H f : ZFSet.{u}}
    (hI : I ∈ M.sets) (small : GroundBelow M I K)
    (inputs : ∀ i ∈ I, ZFSet.rank i < ZFSet.rank K)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc I V f)
    (hierarchy : GroundCumulativeHierarchyCode M (insert K K) H)
    (level : ZFSet.pair K V ∈ H) : ZFSet.rank f < ZFSet.rank K :=
  conditions.functionGraph_rank_lt_small_cumulative pairing unions powers separation collection
    infinite hK hI small inputs hf function
    (hierarchy.mem_iff_rank_lt (ordinalSetProperty_succ conditions.1)
      (ZFSet.mem_insert K K) level)

end PartitionPilot.Forcing.GroundInaccessibleConditions



namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K T : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets) (hT : T ∈ K)
include conditions pairing unions powers separation hK hT

theorem chronologyPairs_below : GroundBelow M (chronologyPairs T) K := by
  have hTM := M.transitive hK hT
  have smallT := GroundBelow.of_member pairing unions powers separation hK hT
  have smallProduct := smallT.product pairing unions powers separation hTM hTM hK
    conditions.1 conditions.2.2.2 smallT
  exact smallProduct.restrict separation
    (M.chronologyPairs_mem pairing unions powers separation hTM) hK (chronologyPairs_subset T)

theorem chronologyPairs_rank_lt (infinite : Realize M.sets infinity Fin.elim0) :
    ZFSet.rank (chronologyPairs T) < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact (ZFSet.rank_mono (chronologyPairs_subset T)).trans_lt
    (rank_product_lt limit (ZFSet.rank_lt_of_mem hT) (ZFSet.rank_lt_of_mem hT))

theorem chronologyPairs_member_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    {p : ZFSet.{u}} (hp : p ∈ chronologyPairs T) : ZFSet.rank p < ZFSet.rank K :=
  (ZFSet.rank_lt_of_mem hp).trans
    (conditions.chronologyPairs_rank_lt pairing unions powers separation hK hT infinite)

end PartitionPilot.Forcing.GroundInaccessibleConditions

end

end OAI
