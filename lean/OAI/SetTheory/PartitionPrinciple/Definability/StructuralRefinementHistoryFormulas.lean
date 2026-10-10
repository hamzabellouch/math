import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralHistoryTestUnions

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def definable_structuralRefinementEntry :
    GroundDefinableFunction M (fun env : Fin 11 → ZFSet.{u} =>
      ZFSet.pair (env 0) (M.rawRefinementFormulaDataCode (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 0))) := by
  let v := GroundSetTerm.var M (n := 11)
  let data := GroundSetTerm.app (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection)
    ![v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 0]
  let entry := GroundSetTerm.app (M.definable_nonemptyTuple pairing 1) ![v 0, data]
  exact entry.definition

noncomputable def structuralRefinementEntryFormula : SetFormula 9 :=
  let w := prefixIndex 9 5
  let old := suffixIndex 9 5
  exBlock 5 (.conj (BoundedFormula.nonemptyTupleFormula 4 (old 0) w).toFormula
    (.conj (.mem (w 0) (old 2))
      (SetFormula.reindex (extend (old 1)
        ![w 0, w 1, w 2, w 3, w 4, old 3, old 4, old 5, old 6, old 7, old 8])
        (M.definable_structuralRefinementEntry pairing unions powers separation collection).formula)))

theorem realize_structuralRefinementEntryFormula (env : Fin 9 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.structuralRefinementEntryFormula pairing unions powers separation collection) env ↔
      ∃ f : Fin 5 → ZFSet.{u}, env 0 = nonemptyTupleCode 4 f ∧ f 0 ∈ env 2 ∧
        env 1 = ZFSet.pair (f 0) (M.rawRefinementFormulaDataCode (f 1) (f 2) (f 3) (f 4)
          (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (f 0)) := by
  unfold structuralRefinementEntryFormula
  rw [realize_exBlock]
  have meaning (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.nonemptyTupleFormula 4 (suffixIndex 9 5 0)
        (prefixIndex 9 5)).toFormula (.conj (.mem (prefixIndex 9 5 0) (suffixIndex 9 5 2))
        (SetFormula.reindex (extend (suffixIndex 9 5 1)
          ![prefixIndex 9 5 0, prefixIndex 9 5 1, prefixIndex 9 5 2, prefixIndex 9 5 3,
            prefixIndex 9 5 4, suffixIndex 9 5 3, suffixIndex 9 5 4, suffixIndex 9 5 5,
            suffixIndex 9 5 6, suffixIndex 9 5 7, suffixIndex 9 5 8])
          (M.definable_structuralRefinementEntry pairing unions powers separation collection).formula)))
          (extendMany 5 f env) ↔
      env 0 = nonemptyTupleCode 4 f ∧ f 0 ∈ env 2 ∧
        env 1 = ZFSet.pair (f 0) (M.rawRefinementFormulaDataCode (f 1) (f 2) (f 3) (f 4)
          (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (f 0)) := by
    change (Realize M.sets (BoundedFormula.nonemptyTupleFormula 4 _ _).toFormula _ ∧ _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members),
      BoundedFormula.truth_nonemptyTupleFormula]
    simp only [extendMany_suffix, extendMany_prefix]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    rw [realize_reindex, map_extend]
    have args : (fun j : Fin 11 => extendMany 5 f env
      (![prefixIndex 9 5 0, prefixIndex 9 5 1, prefixIndex 9 5 2, prefixIndex 9 5 3,
        prefixIndex 9 5 4, suffixIndex 9 5 3, suffixIndex 9 5 4, suffixIndex 9 5 5,
        suffixIndex 9 5 6, suffixIndex 9 5 7, suffixIndex 9 5 8] j)) =
      ![f 0, f 1, f 2, f 3, f 4, env 3, env 4, env 5, env 6, env 7, env 8] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (fun k => Fin.elim0 k))))))))))) j
    rw [args]
    exact (M.definable_structuralRefinementEntry pairing unions powers separation collection).correct _
      (Fin.cases (ground 0) (Fin.cases (ground 1) (Fin.cases (ground 2) (Fin.cases (ground 3)
        (Fin.cases (ground 4) (Fin.cases (members 3) (Fin.cases (members 4) (Fin.cases (members 5)
          (Fin.cases (members 6) (Fin.cases (members 7) (Fin.cases (members 8) (fun j => Fin.elim0 j))))))))))))
      _ (members 1)
  constructor
  · rintro ⟨f, ground, holds⟩
    exact ⟨f, (meaning f ground).1 holds⟩
  · rintro ⟨f, shape, level, value⟩
    have ground := M.nonemptyTupleCode_field_mem 4 f (shape ▸ members 0)
    exact ⟨f, ground, (meaning f ground).2 ⟨shape, level, value⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
