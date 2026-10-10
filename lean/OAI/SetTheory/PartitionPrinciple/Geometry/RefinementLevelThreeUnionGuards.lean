import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFourFlatStageHistories

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

variable {I0 I1 T2 : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
variable (third : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid) (natSetCode 2))
include first second third

theorem refinementLevelTests_stageThreeUnion (Aold Anew : ZFSet.{u}) (p : P)
    (lower : Aold ⊆ stageOneAssignments (I0 ∪ I1) T) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 2) T2 (Aold ∪ Anew) p ↔
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 2) T2 Anew p := by
  apply M.refinementLevelTests_congr s pairing unions powers separation collection carrier order hT valid
    a b d base directed system
  intro t ht u _ w _
  rw [ZFSet.mem_union]
  have absent := stageThreeAssignment_old_no_upper first second third lower (u := u) (w := w) ht
  exact ⟨fun h => h.elim (fun impossible => False.elim (absent impossible)) id, Or.inr⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
