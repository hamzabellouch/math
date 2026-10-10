import OAI.SetTheory.PartitionPrinciple.Definability.StructuralRefinementHistoryFormulas

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

private theorem imageMeaning (env : Fin 8 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    y ∈ M.structuralRefinementHistory (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) ↔
      ∃ x ∈ env 7, Realize M.sets (M.structuralRefinementEntryFormula pairing unions powers separation collection)
        (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5])) := by
  rw [M.mem_structuralRefinementHistory]
  have meaning (x : ZFSet.{u}) (hx : x ∈ env 7) :=
    M.realize_structuralRefinementEntryFormula pairing unions powers separation collection
      (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5]))
      (Fin.cases (M.transitive (members 7) hx) (Fin.cases hy
        (Fin.cases (members 6) (Fin.cases (members 0) (Fin.cases (members 1)
          (Fin.cases (members 2) (Fin.cases (members 3) (Fin.cases (members 4)
            (Fin.cases (members 5) (fun j => Fin.elim0 j))))))))))
  constructor
  · rintro ⟨level, hl, P, order, top, action, entry, equal⟩
    exact ⟨_, entry, (meaning _ entry).2 ⟨![level, P, order, top, action], rfl, hl, equal⟩⟩
  · rintro ⟨x, hx, holds⟩
    obtain ⟨f, shape, level, value⟩ := (meaning x hx).1 holds
    change x = ZFSet.pair (f 0) (forcingStageCode (f 1) (f 2) (f 3) (f 4)) at shape
    exact ⟨f 0, level, f 1, f 2, f 3, f 4, shape ▸ hx, value⟩

include pairing unions powers separation collection in
 theorem structuralRefinementHistory_mem (env : Fin 8 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    M.structuralRefinementHistory (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) ∈ M.sets := by
  let params : Fin 7 → ZFSet.{u} := ![env 6, env 0, env 1, env 2, env 3, env 4, env 5]
  have paramGround : ∀ j, params j ∈ M.sets := Fin.cases (members 6) (Fin.cases (members 0)
    (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3)
      (Fin.cases (members 4) (Fin.cases (members 5) (fun j => Fin.elim0 j)))))))
  apply M.definable_image_mem separation collection
    (M.structuralRefinementEntryFormula pairing unions powers separation collection) params paramGround (members 7)
  · intro y hy
    obtain ⟨level, _, P, order, top, action, entry, rfl⟩ := (M.mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _).1 hy
    have fields := M.nonemptyTupleCode_field_mem 4 (![level, P, order, top, action])
      (M.transitive (members 7) entry)
    exact (M.definable_structuralRefinementEntry pairing unions powers separation collection).closed
      ![level, P, order, top, action, env 0, env 1, env 2, env 3, env 4, env 5]
      (Fin.cases (fields 0) (Fin.cases (fields 1) (Fin.cases (fields 2) (Fin.cases (fields 3)
        (Fin.cases (fields 4) (Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2)
          (Fin.cases (members 3) (Fin.cases (members 4) (Fin.cases (members 5) (fun j => Fin.elim0 j))))))))))))
  · exact imageMeaning M pairing unions powers separation collection env members
  · intro x hx y hy z hz first second
    have meaning (w : ZFSet.{u}) (hw : w ∈ M.sets) :=
      M.realize_structuralRefinementEntryFormula pairing unions powers separation collection
        (extend x (extend w params))
        (Fin.cases (M.transitive (members 7) hx) (Fin.cases hw paramGround))
    obtain ⟨f, shape, _, value⟩ := (meaning y hy).1 first
    obtain ⟨g, shape', _, value'⟩ := (meaning z hz).1 second
    have same := nonemptyTupleCode_injective 4 (shape.symm.trans shape')
    exact value.trans (same ▸ value'.symm)

noncomputable def structuralRefinementHistoryFormula : SetFormula 9 :=
  exactSetFormula 0 (.ex (.conj (.mem 0 10)
    (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8]
      (M.structuralRefinementEntryFormula pairing unions powers separation collection))))

private theorem realizeHistoryReindex (U : Set ZFSet.{u}) (φ : SetFormula 9)
    (env : Fin 8 → ZFSet.{u}) (z y x : ZFSet.{u}) :
    Realize U (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8] φ)
      (extend x (extend y (extend z env))) ↔
      Realize U φ (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5])) := by
  rw [realize_reindex]
  have args : (fun j : Fin 9 =>
      extend x (extend y (extend z env)) (![0, 1, 9, 3, 4, 5, 6, 7, 8] j)) =
      extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5]) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))) j
  exact args ▸ Iff.rfl

private theorem historyFormula_correct (φ : SetFormula 9) (env : Fin 8 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (target : ZFSet.{u}) (target_mem : target ∈ M.sets)
    (meaning : ∀ y ∈ M.sets, y ∈ target ↔
      ∃ x ∈ env 7, Realize M.sets φ
        (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5])))
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets
      (exactSetFormula 0 (.ex (.conj (.mem 0 10)
        (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8] φ))))
      (extend z env) ↔ z = target := by
  apply M.realize_exactSetFormula 0 _ (extend z env) hz
    (fun _ h => M.transitive target_mem h)
  intro y hy
  refine (realize_ex M.sets _ _).trans ?_
  change (∃ x ∈ M.sets, x ∈ env 7 ∧ Realize M.sets
    (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8] φ)
      (extend x (extend y (extend z env)))) ↔ y ∈ target
  refine Iff.trans ?_ (meaning y hy).symm
  constructor
  · rintro ⟨x, _, hx, holds⟩
    exact ⟨x, hx, (realizeHistoryReindex M.sets φ env z y x).mp holds⟩
  · rintro ⟨x, hx, holds⟩
    refine ⟨x, M.transitive (members 7) hx, hx, ?_⟩
    exact (realizeHistoryReindex M.sets φ env z y x).mpr holds

noncomputable def definable_structuralRefinementHistory :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.structuralRefinementHistory (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) where
  formula := M.structuralRefinementHistoryFormula pairing unions powers separation collection
  closed := M.structuralRefinementHistory_mem pairing unions powers separation collection
  correct := fun env members => historyFormula_correct M
    (M.structuralRefinementEntryFormula pairing unions powers separation collection) env members _
    (M.structuralRefinementHistory_mem pairing unions powers separation collection env members)
    (imageMeaning M pairing unions powers separation collection env members)

end PartitionPilot.Forcing.TransitiveGround

end OAI
