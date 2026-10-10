import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveStateFieldEnvironments

namespace OAI

section

namespace PartitionPilot.Forcing

universe u
namespace SetFormula

def stateFieldFormula {n} (code value : Fin n) (j : Fin 13) : SetFormula n :=
  exBlock 13 (.conj
    (BoundedFormula.nonemptyTupleFormula 12 (suffixIndex n 13 code) (prefixIndex n 13)).toFormula
    (.equal (suffixIndex n 13 value) (prefixIndex n 13 j)))

def historyFieldValueFormula {n} (index value history : Fin n) (j : Fin 13) : SetFormula n :=
  ex (.conj (BoundedFormula.pairMembershipFormula index.succ 0 history.succ).toFormula
    (stateFieldFormula 0 value.succ j))

def historyFieldPairFormula {n} (index output history : Fin n) (j : Fin 13) : SetFormula n :=
  ex (.conj (historyFieldValueFormula index.succ 0 history.succ j)
    (BoundedFormula.orderedPairFormula output.succ index.succ 0).toFormula)

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_stateFieldFormula {n} (code value : Fin n) (j : Fin 13)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (state : RecursiveStateData.{u}) (coded : env code = state.code) :
    Realize M.sets (stateFieldFormula code value j) env ↔ env value = state.field j := by
  rw [stateFieldFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, tuple, entry⟩
    have equal := (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 code)
      (prefixIndex n 13) _).1
      ((BoundedFormula.realize_toFormula M _ _ (extendMany_members 13 fields env fieldMembers members)).1 tuple)
    simp only [extendMany_suffix, extendMany_prefix] at equal
    have fieldsEqual : fields = state.field :=
      nonemptyTupleCode_injective 12 (equal.symm.trans coded)
    change extendMany 13 fields env (suffixIndex n 13 value) =
      extendMany 13 fields env (prefixIndex n 13 j) at entry
    simpa only [extendMany_suffix, extendMany_prefix, fieldsEqual] using entry
  · intro equal
    have fieldMembers := M.recursiveStateData_field_mem state (coded ▸ members code)
    refine ⟨state.field, fieldMembers, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _
        (extendMany_members 13 state.field env fieldMembers members)).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 code)
        (prefixIndex n 13) _).2
      simp only [extendMany_suffix, extendMany_prefix]
      exact coded
    · change extendMany 13 state.field env (suffixIndex n 13 value) =
        extendMany 13 state.field env (prefixIndex n 13 j)
      simpa only [extendMany_suffix, extendMany_prefix] using equal

theorem realize_historyFieldValueFormula {k} (index value history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (n : Nat) (indexEq : env index = natSetCode n) :
    Realize M.sets (historyFieldValueFormula index value history j) env ↔
      env value = (states n).field j := by
  rw [historyFieldValueFormula, realize_ex]
  constructor
  · rintro ⟨code, hcode, entry, projected⟩
    have extended : ∀ i, extend code env i ∈ M.sets := Fin.cases hcode members
    have actual := (BoundedFormula.truth_pairMembershipFormula index.succ 0 history.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 entry)
    change ZFSet.pair (env index) code ∈ env history at actual
    rw [indexEq] at actual
    exact (M.realize_stateFieldFormula 0 value.succ j (extend code env) extended
      (states n) ((entries n code).1 actual)).1 projected
  · intro equal
    have entry : ZFSet.pair (natSetCode n) (states n).code ∈ env history :=
      (entries n _).2 rfl
    have hcode := M.pair_right (M.transitive (members history) entry)
    have extended : ∀ i, extend (states n).code env i ∈ M.sets := Fin.cases hcode members
    refine ⟨(states n).code, hcode, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ extended).2
      apply (BoundedFormula.truth_pairMembershipFormula index.succ 0 history.succ _).2
      change ZFSet.pair (env index) (states n).code ∈ env history
      exact indexEq.symm ▸ entry
    · exact (M.realize_stateFieldFormula 0 value.succ j _ extended (states n) rfl).2 equal

theorem realize_historyFieldPairFormula {k} (index output history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (n : Nat) (indexEq : env index = natSetCode n) :
    Realize M.sets (historyFieldPairFormula index output history j) env ↔
      env output = ZFSet.pair (natSetCode n) ((states n).field j) := by
  rw [historyFieldPairFormula, realize_ex]
  constructor
  · rintro ⟨value, hvalue, specified, pair⟩
    have extended : ∀ i, extend value env i ∈ M.sets := Fin.cases hvalue members
    have valueEq := (M.realize_historyFieldValueFormula index.succ 0 history.succ j
      (extend value env) extended states entries n indexEq).1 specified
    have pairEq := (BoundedFormula.truth_orderedPairFormula output.succ index.succ 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 pair)
    change env output = ZFSet.pair (env index) value at pairEq
    exact pairEq.trans (congrArg₂ ZFSet.pair indexEq valueEq)
  · intro equal
    have codeM := M.pair_right (M.transitive (members history) ((entries n _).2 rfl))
    have valueM := M.recursiveStateData_field_mem (states n) codeM j
    have extended : ∀ i, extend ((states n).field j) env i ∈ M.sets := Fin.cases valueM members
    refine ⟨(states n).field j, valueM, ?_, ?_⟩
    · exact (M.realize_historyFieldValueFormula index.succ 0 history.succ j _ extended
        states entries n indexEq).2 rfl
    · apply (BoundedFormula.realize_toFormula M _ _ extended).2
      apply (BoundedFormula.truth_orderedPairFormula output.succ index.succ 0 _).2
      change env output = ZFSet.pair (env index) ((states n).field j)
      exact equal.trans (congrArg (fun x => ZFSet.pair x ((states n).field j)) indexEq.symm)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
