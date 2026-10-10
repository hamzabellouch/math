import OAI.SetTheory.PartitionPrinciple.Forcing.GroundInaccessibleConditions

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite hK

theorem successor_mem {α : ZFSet.{u}} (hα : α ∈ K) : insert α α ∈ K := by
  have hOne := M.natSetCode_mem separation infinite 1
  have oneBelow := conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega 1)
  have ground := M.constantFamilyGraph_mem pairing unions powers separation hOne (M.transitive hK hα)
  have constant := constantFamilyGraph_function (natSetCode 1) α
  have function : ZFSet.IsFunc (natSetCode 1) K (constantFamilyGraph (natSetCode 1) α) := by
    refine ⟨?_, constant.2⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (constant.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.mem_singleton.1 hy) ▸ hα⟩
  obtain ⟨δ, hδ, bounded⟩ := conditions.2.2.1 (natSetCode 1) oneBelow _ ground function
  have less := bounded (natSetCode 0) α
    ((pair_mem_constantFamilyGraph (natSetCode 1) α _ _).2
      ⟨(natSetCode_mem_iff 0 1).2 (by decide), rfl⟩)
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 (ordinalSetProperty_member conditions.1 hα)
  obtain ⟨d, eqD⟩ := (ordinalSetProperty_iff δ).1 (ordinalSetProperty_member conditions.1 hδ)
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 conditions.1
  rw [eqA, eqD, mem_ordinalCode_iff] at less
  rw [eqD, eqK, mem_ordinalCode_iff] at hδ
  rw [eqA, eqK, ← ordinalCode_succ, mem_ordinalCode_iff]
  exact (Order.succ_le_iff.2 less).trans_lt hδ

theorem rank_isLimit : Order.IsSuccLimit (ZFSet.rank K) := by
  apply Ordinal.isSuccLimit_iff.2
  refine ⟨ne_of_gt (bot_le.trans_lt (ZFSet.rank_lt_of_mem conditions.2.1)), ?_⟩
  rw [Order.isSuccPrelimit_iff_succ_lt]
  intro a ha
  have hα : ordinalCode a ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K conditions.1]
    exact (mem_ordinalCode_iff a (ZFSet.rank K)).2 ha
  have bound := ZFSet.rank_lt_of_mem (conditions.successor_mem pairing unions powers separation infinite hK hα)
  rw [← ordinalCode_succ, rank_ordinalCode] at bound
  exact bound

end PartitionPilot.Forcing.GroundInaccessibleConditions

end

end OAI
