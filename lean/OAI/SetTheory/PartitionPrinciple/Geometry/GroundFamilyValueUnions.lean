import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u v
variable {I : Type v} [Small.{u} I]

theorem familyCodeGraph_valueRange_eq (key value : I → ZFSet.{u}) :
    ZFSet.range value = relationImage (ZFSet.range key)
      (ZFSet.sUnion (ZFSet.sUnion (familyCodeGraph key value))) (familyCodeGraph key value) := by
  apply ZFSet.ext
  intro y
  rw [ZFSet.mem_range, mem_relationImage]
  constructor
  · rintro ⟨i, rfl⟩
    have entry := (mem_familyCodeGraph key value _).2 ⟨i, rfl⟩
    exact ⟨pair_second_mem_doubleUnion entry, key i, ZFSet.mem_range.2 ⟨i, rfl⟩, entry⟩
  · rintro ⟨_, x, _, entry⟩
    obtain ⟨i, equal⟩ := (mem_familyCodeGraph key value _).1 entry
    exact ⟨i, (ZFSet.pair_inj.1 equal).2⟩

theorem TransitiveGround.familyCodeGraph_valueRange_mem (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (key value : I → ZFSet.{u}) (domain : ZFSet.range key ∈ M.sets)
    (whole : familyCodeGraph key value ∈ M.sets) : ZFSet.range value ∈ M.sets := by
  rw [familyCodeGraph_valueRange_eq key value]
  exact M.relationImage_mem separation domain (M.union_mem unions (M.union_mem unions whole)) whole

theorem familyCodeGraph_valueRange_rank_le (key value : I → ZFSet.{u}) :
    ZFSet.rank (ZFSet.range value) ≤ ZFSet.rank (familyCodeGraph key value) := by
  have subset : ZFSet.range value ⊆ ZFSet.sUnion (ZFSet.sUnion (familyCodeGraph key value)) := by
    intro y hy
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hy
    exact pair_second_mem_doubleUnion ((mem_familyCodeGraph key value _).2 ⟨i, rfl⟩)
  exact (ZFSet.rank_mono subset).trans ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

theorem familyCodeGraph_valueUnion_rank_le (key value : I → ZFSet.{u}) :
    ZFSet.rank (ZFSet.sUnion (ZFSet.range value)) ≤ ZFSet.rank (familyCodeGraph key value) :=
  (ZFSet.rank_sUnion_le _).trans (familyCodeGraph_valueRange_rank_le key value)

theorem familyCodeGraph_valueUnion_mem_iff (value : I → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ ZFSet.sUnion (ZFSet.range value) ↔ ∃ i, x ∈ value i := by
  rw [ZFSet.mem_sUnion]
  exact ⟨fun ⟨_, hy, hx⟩ => by obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hy; exact ⟨i, hx⟩,
    fun ⟨i, hx⟩ => ⟨value i, ZFSet.mem_range.2 ⟨i, rfl⟩, hx⟩⟩

theorem familyCodeGraph_value_subset_union (key value : I → ZFSet.{u})
    {i X : ZFSet.{u}} (entry : ZFSet.pair i X ∈ familyCodeGraph key value) :
    X ⊆ ZFSet.sUnion (ZFSet.range value) := by
  obtain ⟨j, equal⟩ := (mem_familyCodeGraph key value _).1 entry
  have values := (ZFSet.pair_inj.1 equal).2
  intro x hx
  exact (familyCodeGraph_valueUnion_mem_iff value x).2 ⟨j, values.symm ▸ hx⟩

end PartitionPilot.Forcing

end

end OAI
