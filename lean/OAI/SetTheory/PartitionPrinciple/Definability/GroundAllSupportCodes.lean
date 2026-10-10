import OAI.SetTheory.PartitionPrinciple.Forcing.AllSupportFamilies

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G : Type u} [Group G] (t : Presentation G)

theorem allSupportBasisCode_eq_singleton :
    supportBasisCode (natInitialPresentation 1) t (allSupportBasis G) =
      ({ZFSet.pair (natSetCode 0) (t.encode 1)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  rw [supportBasisCode, Presentation.mem_subset, ZFSet.mem_singleton]
  constructor
  · rintro ⟨⟨i, g⟩, member, equal⟩
    have one : g = 1 := Subgroup.mem_bot.1 member
    have index : i = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
    subst i
    subst g
    exact equal.symm
  · rintro rfl
    exact ⟨(⟨0⟩, 1), Subgroup.one_mem _, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

omit [Group G] in
theorem allSupportIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (group : t.carrier ∈ M.sets) : (natInitialPresentation 1).carrier ∈ M.sets := by
  have empty := M.empty_mem ⟨t.carrier, group⟩
  have singleton := M.unorderedPair_mem pairing empty empty
  simp only [natInitialPresentation, natSetCode_succ, natSetCode_zero]
  simp only [ZFSet.pair_eq_singleton] at singleton
  exact singleton

theorem allSupportBasisCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (group : t.carrier ∈ M.sets) :
    supportBasisCode (natInitialPresentation 1) t (allSupportBasis G) ∈ M.sets := by
  rw [allSupportBasisCode_eq_singleton]
  have empty := M.empty_mem ⟨t.carrier, group⟩
  have one := M.transitive group (t.encode_mem 1)
  have pair := M.orderedPair_mem pairing empty one
  simpa only [natSetCode_zero, ZFSet.pair_eq_singleton] using
    M.unorderedPair_mem pairing pair pair

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
