import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedPositionCollisions

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

theorem stageOneCollisionTest_symm (Rf Rc u u' w w' : (M.nameDomain s).names) (p : P)
    (collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u' u w' w p := by
  constructor
  · intro q hq facts
    exact collision.1 q hq ⟨Name.forcesEq_symm facts.1,
      fun r hr equal => facts.2 r hr (Name.forcesEq_symm equal)⟩
  · intro q hq facts
    exact collision.2 q hq ⟨Name.forcesEq_symm facts.1,
      fun r hr equal => facts.2 r hr (Name.forcesEq_symm equal)⟩

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (level T2 : ZFSet.{u}) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelRawCollision_both_orders (C E : L) (U Rf Rc u u' w w' : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P)
    (collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p) :
    stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val u'.val.val w.val.val w'.val.val (s.encode p) ∧
    stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u'.val.val u.val.val w'.val.val w.val.val (s.encode p) := by
  refine ⟨(M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices C E U Rf Rc u u' w w' member p).2 collision, ?_⟩
  exact (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices C E U Rf Rc u' u w' w member p).2
    (M.stageOneCollisionTest_symm s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p collision)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
