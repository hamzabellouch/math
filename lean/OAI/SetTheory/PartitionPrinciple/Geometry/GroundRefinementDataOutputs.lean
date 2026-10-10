import OAI.SetTheory.PartitionPrinciple.Definability.GroundPackedRefinementFormulaData

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementDataOutputGraph (kind : Fin 3) (data : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  M.refinementIndexNameGraph kind (data 0) (data 3) (data 4) (data 5)
    (data 6) (data 7) (data 8) (data 9)

theorem refinementDataOutputGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (data : Fin 15 → ZFSet.{u}) (members : ∀ j, data j ∈ M.sets) (kind : Fin 3) :
    M.refinementDataOutputGraph kind data ∈ M.sets :=
  M.refinementIndexNameGraph_mem kind pairing unions powers separation
    (members 0) (members 3) (members 4) (members 5)
    (members 6) (members 7) (members 8) (members 9)

variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

theorem refinementLevelFormulaData_map_output :
    M.refinementLevelFormulaData a s b d level T T2 valid 12 =
      M.refinementDataOutputGraph 2 (M.refinementLevelFormulaData a s b d level T T2 valid) := rfl

theorem refinementLevelFormulaData_output_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (members : ∀ j, M.refinementLevelFormulaData a s b d level T T2 valid j ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (kind : Fin 3) (y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) y ∈
      M.refinementDataOutputGraph kind (M.refinementLevelFormulaData a s b d level T T2 valid) ↔
      y = (Name.refinementOutput kind T valid U.val Rf.val Rc.val).val := by
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let bounds := M.niceRefinementIndexBounds s b level T T2
  let fields : Fin 6 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
  have entries (j : Fin 6) (z : ZFSet.{u}) :
      ZFSet.pair (nonemptyTupleCode 5 fields) z ∈ refinementIndexFieldGraph I (bounds j) j ↔
        z = fields j := by
    have function : ZFSet.IsFunc I (bounds j) (refinementIndexFieldGraph I (bounds j) j) :=
      M.refinementIndices_field_function level b.carrier b.conditionOrder
        (M.niceNameCandidateGraph a s b T d.principalFix)
        (M.niceNameCandidateGraph a s b T2 d.principalFix) T T2
        (Name.familySet ⊤ T valid).val s.carrier s.conditionOrder (s.encode ⊤) j
    constructor
    · intro entry
      exact ((refinementIndexFieldGraph_entry I (bounds j) fields j z).1 entry).2.2
    · intro equal
      obtain ⟨v, hv, _⟩ := function.2 _ member
      have value := ((refinementIndexFieldGraph_entry I (bounds j) fields j v).1 hv).2.2
      exact equal.symm ▸ (value ▸ hv)
  exact M.refinementIndexNameGraph_entry s kind pairing unions powers separation collection
    (members 7) (members 8) (members 0) (members 3) (members 4) (members 5) (members 6)
    valid U.val Rf.val Rc.val U.property Rf.property Rc.property member
    (entries 3) (entries 4) (entries 5) y

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
