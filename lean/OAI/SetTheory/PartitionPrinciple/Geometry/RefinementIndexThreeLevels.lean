import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageTwoIndexAnchors

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace RefinementIndexLevelCode
variable {I level B : ZFSet.{u}}

theorem level_field_graph (code : RefinementIndexLevelCode I level) (bound : level ∈ B) :
    refinementIndexFieldGraph I B 0 = ZFSet.prod I {level} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ((ZFSet.mem_sep.1 hz).1)
    obtain ⟨hx, _, v, eqv, hy⟩ := (pair_mem_refinementIndexFieldGraph I B x y 0).1 hz
    obtain ⟨w, eqw, hw⟩ := code x hx
    have equal := nonemptyTupleCode_injective 5 (eqv.symm.trans eqw)
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_singleton.2
      (hy.trans ((congrFun equal 0).trans hw))⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    have same := ZFSet.mem_singleton.1 hy
    obtain ⟨v, eqv, hv⟩ := code x hx
    exact (pair_mem_refinementIndexFieldGraph I B x y 0).2
      ⟨hx, same.symm ▸ bound, v, eqv, same.trans hv.symm⟩

theorem level_field_function (code : RefinementIndexLevelCode I level) (bound : level ∈ B) :
    ZFSet.IsFunc I B (refinementIndexFieldGraph I B 0) := by
  apply refinementIndexFieldGraph_function
  intro x hx
  obtain ⟨v, equal, hv⟩ := code x hx
  exact ⟨v, equal, hv.symm ▸ bound⟩

end RefinementIndexLevelCode

theorem refinementIndexFieldGraph_function_union {I J B : ZFSet.{u}} (j : Fin 6)
    (first : ZFSet.IsFunc I B (refinementIndexFieldGraph I B j))
    (second : ZFSet.IsFunc J B (refinementIndexFieldGraph J B j)) :
    ZFSet.IsFunc (I ∪ J) B (refinementIndexFieldGraph (I ∪ J) B j) := by
  apply refinementIndexFieldGraph_function
  intro x hx
  rcases ZFSet.mem_union.1 hx with hi | hj
  · obtain ⟨y, entry, _⟩ := first.2 x hi
    obtain ⟨_, hy, v, ex, ey⟩ := (pair_mem_refinementIndexFieldGraph I B x y j).1 entry
    exact ⟨v, ex, ey ▸ hy⟩
  · obtain ⟨y, entry, _⟩ := second.2 x hj
    obtain ⟨_, hy, v, ex, ey⟩ := (pair_mem_refinementIndexFieldGraph J B x y j).1 entry
    exact ⟨v, ex, ey ▸ hy⟩

namespace RefinementIndexLevelCode
variable {I0 I1 I2 : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
variable (third : RefinementIndexLevelCode I2 (natSetCode 2))
include first second third

theorem three_level_function :
    ZFSet.IsFunc ((I0 ∪ I1) ∪ I2) (natSetCode 3)
      (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0) :=
  refinementIndexFieldGraph_function_union 0
    (refinementIndexFieldGraph_function_union 0
      (first.level_field_function ((natSetCode_mem_iff 0 3).2 (by decide)))
      (second.level_field_function ((natSetCode_mem_iff 1 3).2 (by decide))))
    (third.level_field_function ((natSetCode_mem_iff 2 3).2 (by decide)))

theorem three_level_graph :
    refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 =
      (ZFSet.prod I0 {∅} ∪ ZFSet.prod I1 {natSetCode 1}) ∪
        ZFSet.prod I2 {natSetCode 2} := by
  rw [refinementIndexFieldGraph_union, refinementIndexFieldGraph_union,
    first.level_field_graph ((natSetCode_mem_iff 0 3).2 (by decide)),
    second.level_field_graph ((natSetCode_mem_iff 1 3).2 (by decide)),
    third.level_field_graph ((natSetCode_mem_iff 2 3).2 (by decide))]

theorem three_level_entry (x level : ZFSet.{u}) :
    ZFSet.pair x level ∈ refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 ↔
      (x ∈ I0 ∧ level = ∅) ∨ (x ∈ I1 ∧ level = natSetCode 1) ∨
        (x ∈ I2 ∧ level = natSetCode 2) := by
  rw [first.three_level_graph second third]
  simp only [ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton, or_assoc]

theorem three_levels_disjoint :
    (∀ x, ¬ (x ∈ I0 ∧ x ∈ I1)) ∧ (∀ x, ¬ (x ∈ I0 ∧ x ∈ I2)) ∧
      (∀ x, ¬ (x ∈ I1 ∧ x ∈ I2)) := by
  exact ⟨first.disjoint second (fun h => (by decide : (0 : Nat) ≠ 1) (natSetCode_injective h)),
    first.disjoint third (fun h => (by decide : (0 : Nat) ≠ 2) (natSetCode_injective h)),
    second.disjoint third (fun h => (by decide : (1 : Nat) ≠ 2) (natSetCode_injective h))⟩

end RefinementIndexLevelCode
end PartitionPilot.Forcing

end

end OAI
