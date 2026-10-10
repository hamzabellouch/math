import OAI.SetTheory.PartitionPrinciple.Definability.GroundRegularFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFamilyValueUnions

namespace OAI

section

namespace PartitionPilot.Forcing.GroundRegular
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (regular : GroundRegular M K)
include regular

theorem familyCodeGraph_valueRange_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K)
    {I : Type v} [Small.{u} I] (key value : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets) (whole : familyCodeGraph key value ∈ M.sets)
    (small : GroundBelow M (ZFSet.range key) K)
    (ranks : ∀ i, ZFSet.rank (value i) < ZFSet.rank K) :
    ZFSet.rank (ZFSet.range value) < ZFSet.rank K := by
  let R := ZFSet.range value
  have hR : R ∈ M.sets := M.familyCodeGraph_valueRange_mem unions separation key value domain whole
  have rankGround := M.cumulativeRankGraph_mem pairing unions powers separation collection hR hK
  have rankFunction : ZFSet.IsFunc R K (cumulativeRankGraph R K) := by
    apply cumulativeRankGraph_function ordinal
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ranks i
  let graph := relationCompose (ZFSet.range key) R K (familyCodeGraph key value) (cumulativeRankGraph R K)
  have ground : graph ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    domain hR hK whole rankGround
  have function : ZFSet.IsFunc (ZFSet.range key) K graph :=
    relationCompose_function_of_subset (familyCodeGraph_isFunc key value injective) rankFunction (fun _ h => h)
  obtain ⟨b, hb, bounded⟩ := regular.bound_small_domain pairing unions powers separation domain hK ground small function
  have uniform : ∀ i, ZFSet.rank (value i) < ZFSet.rank b := by
    intro i
    have hi : value i ∈ R := ZFSet.mem_range.2 ⟨i, rfl⟩
    obtain ⟨a, entry, _⟩ := rankFunction.2 (value i) hi
    have rankEntry := (pair_mem_cumulativeRankGraph R K (value i) a).1 entry
    have composite : ZFSet.pair (key i) a ∈ graph :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, rankEntry.2.1, value i, hi,
          (pair_mem_familyCodeGraph key value injective i _).2 rfl, entry⟩
    have rank := ZFSet.rank_lt_of_mem (bounded (key i) a composite)
    simpa only [rankEntry.2.2, rank_ordinalCode] using rank
  apply (ZFSet.rank_le_iff.2 ?_).trans_lt (ZFSet.rank_lt_of_mem hb)
  intro x hx
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
  exact uniform i

end PartitionPilot.Forcing.GroundRegular

end

end OAI
