import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialPreservedMainPrefix

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def preservedMainPrefixHistoryValueFormula {n} (K Labels C D rD N i q : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj
    (BoundedFormula.conj (BoundedFormula.successorFormula (field 0) (old i))
      (BoundedFormula.mainPrefixTupleFormula (old q) (field 0) (field 1) (field 2))).toFormula
    (.conj (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (field 0) (field 1) (field 2))
      (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
        (field 1) (field 2))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preservedMainPrefixHistoryValueFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N i q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (preservedMainPrefixHistoryValueFormula K Labels C D rD N i q) env ↔
      ∃ S E, env q = mainPrefixCode (insert (env i) (env i)) S E ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD)
          (insert (env i) (env i)) S E ∧
        MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) S E := by
  rw [preservedMainPrefixHistoryValueFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets
        (BoundedFormula.conj (BoundedFormula.successorFormula (field 0) (old i))
          (BoundedFormula.mainPrefixTupleFormula (old q) (field 0) (field 1) (field 2))).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
          (field 0) (field 1) (field 2)) (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D)
          (old rD) (old N) (field 1) (field 2)) (extendMany 3 f env)) ↔
      (f 0 = insert (env i) (env i) ∧ env q = mainPrefixCode (f 0) (f 1) (f 2)) ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 0) (f 1) (f 2) ∧
        MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 1) (f 2) := by
    have mems := extendMany_members 3 f env ground members
    rw [BoundedFormula.realize_toFormula M _ _ mems]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_successorFormula,
      BoundedFormula.truth_mainPrefixTupleFormula]
    rw [M.realize_mainPrefixGraphFormula pairing unions powers separation collection
      _ _ _ _ _ _ _ _ _ _ mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)]
    rw [M.realize_mainPrefixProfileGraphFormula pairing unions powers separation collection
      _ _ _ _ _ _ _ _ _ mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)]
    simp only [old, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, recognized⟩
    obtain ⟨⟨index, encoded⟩, valid, profiles⟩ := (actual f ground).1 recognized
    exact ⟨f 1, f 2, index ▸ encoded, index ▸ valid, profiles⟩
  · rintro ⟨S, E, encoded, valid, profiles⟩
    have ground := M.mainPrefixCode_fields_mem (encoded ▸ members q)
    let f : Fin 3 → ZFSet.{u} := Fin.cases (insert (env i) (env i)) (Fin.cases S (fun _ => E))
    have grounds : ∀ j, f j ∈ M.sets := Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨f, grounds, (actual f grounds).2 ⟨⟨rfl, encoded⟩, valid, profiles⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
