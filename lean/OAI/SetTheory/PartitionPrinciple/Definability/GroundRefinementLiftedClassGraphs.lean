import OAI.SetTheory.PartitionPrinciple.Forcing.RenamedPairNameFamilies

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} [PartialOrder P] [OrderTop P]
variable (lower : Presentation P) (upper : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem exists_refinementLiftedClassGraph
    (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
    (lowerOrder : lower.conditionOrder ∈ M.sets)
    (incl : P → Q) (inclGround : lower.graph upper incl ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName lower z)
    (R : Name lower) (hR : R.val ∈ M.sets) :
    ∃ graph ∈ M.sets, ∀ (v : Name lower) (y : ZFSet.{u}),
      ZFSet.pair v.val y ∈ graph ↔ v.val ∈ T ∧
        y = (Name.rename upper incl (Name.refinementClass T valid R v)).val := by
  let classesGraph := Name.refinementClassGraph T valid R T valid
  have hClassesGraph : classesGraph ∈ M.sets :=
    M.refinementClassGraph_mem lower pairing unions powers separation collection
      lowerGround lowerOrder hT hT valid valid R hR
  let classes := functionGraphRange T classesGraph
  have hClasses : classes ∈ M.sets :=
    M.functionGraphRange_mem unions separation hT hClassesGraph
  have validClasses : ∀ z ∈ classes, IsName lower z := by
    intro z hz
    obtain ⟨v, hv, entry⟩ := (mem_functionGraphRange T classesGraph z).1 hz
    let name : Name lower := ⟨v, valid v hv⟩
    have equal := ((Name.pair_mem_refinementClassGraph T valid R T valid name z).1 entry).2
    exact equal.symm ▸ (Name.refinementClass T valid R name).property
  let renamings := Name.renameFamilyGraph upper incl classes validClasses
  have hRenamings : renamings ∈ M.sets :=
    M.renameFamilyGraph_mem lower upper pairing unions powers separation collection
      lowerGround upperGround incl inclGround classes hClasses validClasses
  let lifted := functionGraphRange classes renamings
  have hLifted : lifted ∈ M.sets :=
    M.functionGraphRange_mem unions separation hClasses hRenamings
  refine ⟨relationCompose T classes lifted classesGraph renamings,
    M.relationCompose_mem pairing unions powers separation hT hClasses hLifted hClassesGraph hRenamings, ?_⟩
  intro v y
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨hv, _hy, z, hz, first, second⟩
    have equal := ((Name.pair_mem_refinementClassGraph T valid R T valid v z).1 first).2
    subst z
    exact ⟨hv, ((Name.pair_mem_renameFamilyGraph upper incl classes validClasses
      (Name.refinementClass T valid R v) y).1 second).2⟩
  · rintro ⟨hv, rfl⟩
    have first : ZFSet.pair v.val (Name.refinementClass T valid R v).val ∈ classesGraph :=
      (Name.pair_mem_refinementClassGraph T valid R T valid v _).2 ⟨hv, rfl⟩
    have member : (Name.refinementClass T valid R v).val ∈ classes :=
      (mem_functionGraphRange T classesGraph _).2 ⟨v.val, hv, first⟩
    have second : ZFSet.pair (Name.refinementClass T valid R v).val
        (Name.rename upper incl (Name.refinementClass T valid R v)).val ∈ renamings :=
      (Name.pair_mem_renameFamilyGraph upper incl classes validClasses
        (Name.refinementClass T valid R v) _).2 ⟨member, rfl⟩
    exact ⟨hv, (mem_functionGraphRange classes renamings _).2
      ⟨_, member, second⟩, _, member, first, second⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
