import OAI.SetTheory.PartitionPrinciple.Definability.GroundStageOneFormulaData

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

theorem stageOneRawClass_iff (R w : (M.nameDomain s).names) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) R.val.val w.val.val z ↔
      z = (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w).val.val :=
  M.realize_refinementClassCodeFormula s pairing unions powers separation collection carrier order
    hT valid R.val w.val R.property w.property z hz

theorem stageOneClassName_mem_bound (R w : (M.nameDomain s).names) :
    (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w).val.val ∈
      M.groundRelations T s.carrier :=
  (M.mem_groundRelations T s.carrier _).2
    ⟨(M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w).property,
      Name.refinementClass_subset T valid R.val w.val⟩

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)

include indices in
theorem stageOneFormulaData_fields (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) :
    let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.stageOneFormulaData a s b d T T2 valid
    (∀ z, ZFSet.pair idx z ∈ data 1 ↔ z = b.encode C) ∧
    (∀ z, ZFSet.pair idx z ∈ data 2 ↔ z = b.encode E) ∧
    (∀ z, ZFSet.pair idx z ∈ data 3 ↔ z = U.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 4 ↔ z = Rf.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 5 ↔ z = Rc.val.val) :=
  ⟨M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 1,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 2,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 3,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 4,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 5⟩

include indices in
theorem stageOneFormulaData_map (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) (z : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) z ∈
      M.stageOneFormulaData a s b d T T2 valid 12 ↔
      z = (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc).val.val :=
  M.niceRefinementNameGraph_entry a s b d indices pairing unions powers separation collection hT carrier order
    2 C E U Rf Rc member z

variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem stageOneFormulaData_visibility (v : L) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode v) z ∈ M.stageOneFormulaData a s b d T T2 valid 13 ↔
      z = (M.stageOneVisibilityName s valid a b d base directed system v).val.val :=
  system.visibility_entries v z

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
