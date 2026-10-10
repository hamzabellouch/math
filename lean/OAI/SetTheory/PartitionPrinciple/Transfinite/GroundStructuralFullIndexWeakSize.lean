import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralFullIndexSize

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation choice

theorem indexed_union_embeds_square {K F : ZFSet.{u}}
    (hK : K ∈ M.sets) (hF : F ∈ M.sets)
    (ordinal : ordinalSetProperty K) (function : FunctionGraphOn K F)
    (fibers : ∀ beta A, ZFSet.pair beta A ∈ F → GroundBelow M A K) :
    M.groundEmbeddable (⋃₀ functionGraphRange K F) (ZFSet.prod K K) := by
  let R := functionGraphRange K F
  have hR : R ∈ M.sets := M.functionGraphRange_mem unions separation hK hF
  apply M.enumerated_union_embeds_product pairing unions powers separation choice
    hR (M.union_mem unions hR) hK hF (functionGraphRange_function function)
  · intro A hA
    exact (mem_functionGraphRange K F A).1 hA
  · intro A hA x hx
    exact ZFSet.mem_sUnion.2 ⟨A, hA, hx⟩
  · intro A hA
    obtain ⟨beta, _, entry⟩ := (mem_functionGraphRange K F A).1 hA
    obtain ⟨delta, hd, embedding⟩ := fibers beta A entry
    exact TransitiveGround.groundEmbeddable_retarget embedding (ordinal.1 delta hd)

theorem refinementDataHistoryIndices_embeds_square {history T K : ZFSet.{u}}
    (hK : K ∈ M.sets) (hHistory : history ∈ M.sets)
    (ordinal : ordinalSetProperty K) (valid : RefinementDataHistory K history T)
    (fibers : ∀ beta (data : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode data) ∈ history → GroundBelow M (data 0) K) :
    M.groundEmbeddable (refinementDataHistoryIndices K history) (ZFSet.prod K K) := by
  apply M.indexed_union_embeds_square pairing unions powers separation choice hK
    (M.refinementDataHistoryField_mem pairing unions powers separation hK hHistory 0)
    ordinal valid.index_function
  intro beta A entry
  obtain ⟨_, data, stored, rfl⟩ := (pair_mem_refinementDataHistoryField K history beta A 0).1 entry
  exact fibers beta data stored

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (collection : CollectionSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hRows : rows ∈ M.sets) (hG : G ∈ M.sets) (hn : nodes ∈ M.sets)
variable (hno : nodeOrder ∈ M.sets) (hb : basis ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (smallRows : GroundBelow M rows K) (smallNodes : GroundBelow M nodes K)
variable (smallT : GroundBelow M T K) (smallT2 : GroundBelow M T2 K)
include pairing unions powers separation infinite collection choice hRows hG hn hno hb hT hT2
  hK conditions smallRows smallNodes smallT smallT2
local notation "step" => fun level prior stage => stage =
  M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 level prior

theorem structuralForcingTrace_indices_embeds_square {history : ZFSet.{u}}
    (hh : history ∈ M.sets) (trace : OrdinalRecursionTrace step K history) :
    M.groundEmbeddable (refinementDataHistoryIndices K
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 K history)) (ZFSet.prod K K) := by
  have prefixes := M.structuralForcingTrace_prefix_below rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 pairing unions powers separation infinite collection choice
    hRows hG hn hno hb hT hT2 hK conditions smallRows smallNodes smallT smallT2 hh trace
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 conditions.1 trace
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, K, history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT (Fin.cases hT2
      (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  apply M.refinementDataHistoryIndices_embeds_square pairing unions powers separation choice
    hK packed conditions.1 run.carriers.data
  intro beta data entry
  have member := run.carriers.data.function.pair_source entry
  have smallCarrier : GroundBelow M (data 7) K :=
    (run.carriers.carrier beta data entry).symm ▸ (prefixes beta member).2
  exact (M.structuralRefinementHistory_indices_below pairing unions powers separation infinite collection
    hK conditions G nodes nodeOrder basis T T2 hG hn hno hb hT hT2 smallNodes smallT smallT2
    hh data entry smallCarrier).2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
