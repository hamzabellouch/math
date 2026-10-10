import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPairNameFamilies
import OAI.SetTheory.PartitionPrinciple.Forcing.RefinementAssignmentLabelNames

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

private def labelEntryFormula : SetFormula 7 :=
  exBlock 10 (.conj (.mem 0 11) (.conj (.mem 1 11) (.conj (.mem 2 14)
    (.conj (orderedPairFormula 2 3 4)
    (.conj (orderedPairFormula 8 0 1)
    (.conj (orderedPairFormula 9 15 8) (.conj (.mem 9 4)
    (.conj (pairMembershipFormula 0 5 12)
    (.conj (pairMembershipFormula 1 6 13)
    (.conj (orderedPairNameCodeFormula 7 5 6 16)
      (orderedPairFormula 10 7 2)))))))))))

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem refinementAssignmentLabel_mem_of_graphs
    (hUpper : upper.carrier ∈ M.sets) (hOne : upper.encode one ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (idx : ZFSet.{u}) (hIdx : idx ∈ M.sets) (Rf Rc : Name s)
    (Gc Gf : ZFSet.{u}) (hGc : Gc ∈ M.sets) (hGf : Gf ∈ M.sets)
    (coarse : ∀ (v : Name s) y, ZFSet.pair v.val y ∈ Gc ↔ v.val ∈ T ∧
      y = (Name.rename upper incl (Name.refinementClass T valid Rc v)).val)
    (fine : ∀ (w : Name s) y, ZFSet.pair w.val y ∈ Gf ↔ w.val ∈ T ∧
      y = (Name.rename upper incl (Name.refinementClass T valid Rf w)).val) :
    (Name.refinementAssignmentLabel upper incl one T valid idx Rf Rc).val ∈ M.sets := by
  let cv (v : Name s) := Name.rename upper incl (Name.refinementClass T valid Rc v)
  let fw (w : Name s) := Name.rename upper incl (Name.refinementClass T valid Rf w)
  let label := Name.refinementAssignmentLabel upper incl one T valid idx Rf Rc
  let X := functionGraphRange T Gc
  let Y := functionGraphRange T Gf
  have hX := M.functionGraphRange_mem unions separation hT hGc
  have hY := M.functionGraphRange_mem unions separation hT hGf
  have cvX (v : Name s) (hv : v.val ∈ T) : (cv v).val ∈ X :=
    (mem_functionGraphRange T Gc _).2 ⟨v.val, hv, (coarse v _).2 ⟨hv, rfl⟩⟩
  have fwY (w : Name s) (hw : w.val ∈ T) : (fw w).val ∈ Y :=
    (mem_functionGraphRange T Gf _).2 ⟨w.val, hw, (fine w _).2 ⟨hw, rfl⟩⟩
  let bound := ZFSet.prod (orderedPairNameFamily (upper.encode one) X Y) upper.carrier
  have hBound : bound ∈ M.sets := M.prod_mem pairing unions powers separation
    (M.orderedPairNameFamily_mem pairing unions powers separation hOne hX hY) hUpper
  have bounded : label.val ⊆ bound := by
    intro z hz
    obtain ⟨sigma, p, rfl⟩ := Name.entries_cover label hz
    obtain ⟨v, w, hv, hw, _, rfl⟩ :=
      (Name.entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 hz
    apply ZFSet.pair_mem_prod.2
    refine ⟨?_, upper.encode_mem p⟩
    exact (mem_orderedPairNameFamily _ X Y _).2
      ⟨(cv v).val, cvX v hv, (fw w).val, fwY w hw, Name.orderedPair_code one (cv v) (fw w)⟩
  let params : Fin 6 → ZFSet.{u} := ![T, Gc, Gf, upper.carrier, idx, upper.encode one]
  have paramsGround : ∀ j, params j ∈ M.sets :=
    Fin.cases hT (Fin.cases hGc (Fin.cases hGf (Fin.cases hUpper
      (Fin.cases hIdx (Fin.cases hOne (fun j => Fin.elim0 j))))))
  have recognized (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets labelEntryFormula (extend z params) ↔ z ∈ label.val := by
    let env := extend z params
    have envGround : ∀ j, env j ∈ M.sets := Fin.cases hz paramsGround
    have body (fields : Fin 10 → ZFSet.{u}) (hg : ∀ j, fields j ∈ M.sets) :
        Realize M.sets
          (.conj (.mem 0 11) (.conj (.mem 1 11) (.conj (.mem 2 14)
          (.conj (orderedPairFormula 2 3 4) (.conj (orderedPairFormula 8 0 1)
          (.conj (orderedPairFormula 9 15 8) (.conj (.mem 9 4)
          (.conj (pairMembershipFormula 0 5 12) (.conj (pairMembershipFormula 1 6 13)
          (.conj (orderedPairNameCodeFormula 7 5 6 16) (orderedPairFormula 10 7 2)))))))))))
          (extendMany 10 fields env) ↔
        fields 0 ∈ T ∧ fields 1 ∈ T ∧ fields 2 ∈ upper.carrier ∧
        fields 2 = ZFSet.pair (fields 3) (fields 4) ∧
        fields 8 = ZFSet.pair (fields 0) (fields 1) ∧
        fields 9 = ZFSet.pair idx (fields 8) ∧ fields 9 ∈ fields 4 ∧
        ZFSet.pair (fields 0) (fields 5) ∈ Gc ∧
        ZFSet.pair (fields 1) (fields 6) ∈ Gf ∧
        fields 7 = orderedPairNameCode (upper.encode one) (fields 5) (fields 6) ∧
        z = ZFSet.pair (fields 7) (fields 2) := by
      have all := extendMany_members 10 fields env hg envGround
      simp only [Realize]
      rw [M.realize_orderedPairFormula pairing 2 3 4 _ (all _) (all _) (all _),
        M.realize_orderedPairFormula pairing 8 0 1 _ (all _) (all _) (all _),
        M.realize_orderedPairFormula pairing 9 15 8 _ (all _) (all _) (all _),
        M.realize_pairMembershipFormula pairing 0 5 12 _ (all _) (all _) (all _),
        M.realize_pairMembershipFormula pairing 1 6 13 _ (all _) (all _) (all _),
        M.realize_orderedPairNameCodeFormula pairing 7 5 6 16 _ all,
        M.realize_orderedPairFormula pairing 10 7 2 _ (all _) (all _) (all _)]
      rfl
    rw [labelEntryFormula, realize_exBlock]
    constructor
    · rintro ⟨fields, hg, holds⟩
      obtain ⟨hv, hw, hp, pCode, vwCode, tripleCode, old, gc, gf, pairCode, entryCode⟩ :=
        (body fields hg).1 holds
      let v : Name s := ⟨fields 0, valid _ hv⟩
      let w : Name s := ⟨fields 1, valid _ hw⟩
      obtain ⟨p, pEq⟩ := (upper.mem_carrier _).1 hp
      have cvEq := ((coarse v _).1 gc).2
      have fwEq := ((fine w _).1 gf).2
      have literal : stageOneAssignment idx v.val w.val ∈ fields 4 := by
        rw [tripleCode, vwCode] at old
        exact old
      have named : fields 7 = (Name.orderedPair one (cv v) (fw w)).val := by
        rw [pairCode, cvEq, fwEq]
        exact (Name.orderedPair_code one (cv v) (fw w)).symm
      rw [entryCode, named, ← pEq]
      exact (Name.entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc _ p).2
        ⟨v, w, hv, hw, ⟨fields 3, fields 4, pEq.trans pCode, literal⟩, rfl⟩
    · intro member
      obtain ⟨sigma, p, rfl⟩ := Name.entries_cover label member
      obtain ⟨v, w, hv, hw, ⟨row, A, pCode, old⟩, rfl⟩ :=
        (Name.entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 member
      have hp := M.transitive hUpper (upper.encode_mem p)
      have hpCode : ZFSet.pair row A ∈ M.sets := pCode ▸ hp
      have hrow := M.pair_left hpCode
      have hA := M.pair_right hpCode
      have hvM := M.transitive hT hv
      have hwM := M.transitive hT hw
      have hcv := M.transitive hX (cvX v hv)
      have hfw := M.transitive hY (fwY w hw)
      have hpair : (Name.orderedPair one (cv v) (fw w)).val ∈ M.sets := by
        rw [Name.orderedPair_code]
        exact M.orderedPairNameCode_mem pairing hOne hcv hfw
      let fields : Fin 10 → ZFSet.{u} := ![v.val, w.val, upper.encode p, row, A,
        (cv v).val, (fw w).val, (Name.orderedPair one (cv v) (fw w)).val,
        ZFSet.pair v.val w.val, stageOneAssignment idx v.val w.val]
      have hg : ∀ j, fields j ∈ M.sets :=
        Fin.cases hvM (Fin.cases hwM (Fin.cases hp (Fin.cases hrow (Fin.cases hA
          (Fin.cases hcv (Fin.cases hfw (Fin.cases hpair
            (Fin.cases (M.orderedPair_mem pairing hvM hwM)
              (Fin.cases (M.transitive hA old) (fun j => Fin.elim0 j))))))))))
      exact ⟨fields, hg, (body fields hg).2
        ⟨hv, hw, upper.encode_mem p, pCode, rfl, rfl, old,
          (coarse v _).2 ⟨hv, rfl⟩, (fine w _).2 ⟨hw, rfl⟩,
          Name.orderedPair_code one (cv v) (fw w), rfl⟩⟩
  have selected := M.separation_mem separation labelEntryFormula params paramsGround hBound
  have equal : ZFSet.sep (fun z => Realize M.sets labelEntryFormula (extend z params)) bound = label.val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (recognized z (M.transitive hBound h.1)).1 h.2,
      fun h => ⟨bounded h, (recognized z (M.transitive hBound (bounded h))).2 h⟩⟩
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
