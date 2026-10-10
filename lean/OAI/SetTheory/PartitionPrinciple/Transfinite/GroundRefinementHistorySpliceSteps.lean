import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralHistoryTestUnions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
include pairing unions powers separation collection carrier order nodes hT indices system

theorem refinementLevelRawTests_flat_mono {R : Type u} [PartialOrder R]
    (c : Presentation R) (J : ZFSet.{u}) (F : FlatConditionSystem M c s J)
    (A : ZFSet.{u}) {p q : P}
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (rows : F.row q ≤ F.row p) (assignments : F.assignments p ⊆ F.assignments q) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode q) :=
  M.refinementLevelRawTests_mono a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system A tests ((F.le_iff q p).2 ⟨rows, assignments⟩)

variable {stages history : ZFSet.{u}} (historyValid : RefinementDataHistory stages history T)
variable (entry : ZFSet.pair level (refinementFormulaDataCode
  (M.refinementLevelFormulaData a s b d level T T2 valid)) ∈ history)
include historyValid entry

theorem refinementLevelRawTests_history_splice_below (alpha Aq Ap : ZFSet.{u})
    {p q : ZFSet.{u}} (inside : level ∈ alpha)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) Aq p)
    (below : ZFSet.pair q p ∈ s.conditionOrder) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) q :=
  (historyValid.rawTests_splice_below entry M alpha Aq Ap q inside).2
    (M.refinementLevelRawTests_order_mono a s b d level pairing unions powers separation collection
      carrier order nodes hT valid indices base directed system Aq tests below)

theorem refinementLevelRawTests_history_splice_above (alpha Aq Ap : ZFSet.{u})
    {p q : ZFSet.{u}} (outside : level ∉ alpha)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) Ap p)
    (below : ZFSet.pair q p ∈ s.conditionOrder) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (assignmentSplice (refinementDataHistoryLevels stages history T) alpha Aq Ap) q :=
  (historyValid.rawTests_splice_above entry M alpha Aq Ap q outside).2
    (M.refinementLevelRawTests_order_mono a s b d level pairing unions powers separation collection
      carrier order nodes hT valid indices base directed system Ap tests below)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
