import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveLiftAgreement

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

theorem mem_recursiveSeparatorFamily (K I J D L Maps Ss z : ZFSet.{u}) :
    z ∈ recursiveSeparatorFamily K I J D L Maps Ss ↔
      ∃ i ∈ I, ∃ j ∈ J, ∃ S, ∃ e ∈ D, ∃ y ∈ L,
        z = ZFSet.pair (ZFSet.pair i j) y ∧ ZFSet.pair i j ∈ K ∧
          ZFSet.pair i S ∈ Maps ∧ ZFSet.pair j e ∈ Ss ∧ ZFSet.pair e y ∈ S := by
  unfold recursiveSeparatorFamily familyEvaluationGraph
  constructor
  · intro member
    obtain ⟨_, k, hk, S, _, e, he, y, hy, equal, first, second, image⟩ := ZFSet.mem_sep.1 member
    obtain ⟨_, _, i, hi, j, hj, rfl, mapEntry⟩ :=
      (pair_mem_pairFieldGraph true I J K (⋃₀ ⋃₀ Maps) Maps k S).1 first
    have sepEntry := ((pairFieldGraph_entry_iff false hi hj).1 second).2.2
    exact ⟨i, hi, j, hj, S, e, he, y, hy, equal, hk, mapEntry, sepEntry, image⟩
  · rintro ⟨i, hi, j, hj, S, e, he, y, hy, equal, hk, mapEntry, sepEntry, image⟩
    refine ZFSet.mem_sep.2 ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hk, hy⟩,
      ZFSet.pair i j, hk, S, pair_second_mem_doubleUnion mapEntry, e, he, y, hy, equal, ?_, ?_, image⟩
    · exact (pairFirstField_entry_iff hi hj).2 ⟨hk, mapEntry⟩
    · exact (pairFieldGraph_entry_iff false hi hj).2 ⟨hk, he, sepEntry⟩

namespace SetFormula

def recursiveSeparatorEntryFormula {n} (z K I J D L Maps Ss : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  let body := BoundedFormula.conj (.mem 4 (lift I)) (.conj (.mem 3 (lift J))
    (.conj (.mem 1 (lift D)) (.conj (.mem 0 (lift L))
      (.conj (BoundedFormula.orderedTripleFormula (lift z) 4 3 0)
        (.conj (BoundedFormula.pairMembershipFormula 4 3 (lift K))
          (.conj (BoundedFormula.pairMembershipFormula 4 2 (lift Maps))
            (.conj (BoundedFormula.pairMembershipFormula 3 1 (lift Ss))
              (BoundedFormula.pairMembershipFormula 1 0 2))))))))
  ex (ex (ex (ex (ex body.toFormula))))

def recursiveSeparatorFamilyFormula {n} (family K I J D L Maps Ss : Fin n) : SetFormula n :=
  exactSetFormula family
    (recursiveSeparatorEntryFormula 0 K.succ I.succ J.succ D.succ L.succ Maps.succ Ss.succ)

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_recursiveSeparatorEntryFormula {n} (z K I J D L Maps Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (recursiveSeparatorEntryFormula z K I J D L Maps Ss) env ↔
      env z ∈ recursiveSeparatorFamily (env K) (env I) (env J) (env D) (env L) (env Maps) (env Ss) := by
  simp only [recursiveSeparatorEntryFormula, realize_ex]
  rw [mem_recursiveSeparatorFamily]
  constructor
  · rintro ⟨i, hiM, j, hjM, S, hSM, e, heM, y, hyM, body⟩
    have extended : ∀ a, extend y (extend e (extend S (extend j (extend i env)))) a ∈ M.sets :=
      Fin.cases hyM (Fin.cases heM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members))))
    have spec := (BoundedFormula.realize_toFormula M _ _ extended).1 body
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula] at spec
    change i ∈ env I ∧ j ∈ env J ∧ e ∈ env D ∧ y ∈ env L ∧
      env z = ZFSet.pair (ZFSet.pair i j) y ∧ ZFSet.pair i j ∈ env K ∧
        ZFSet.pair i S ∈ env Maps ∧ ZFSet.pair j e ∈ env Ss ∧ ZFSet.pair e y ∈ S at spec
    exact ⟨i, spec.1, j, spec.2.1, S, e, spec.2.2.1, y, spec.2.2.2.1, spec.2.2.2.2⟩
  · rintro ⟨i, hi, j, hj, S, e, he, y, hy, equal, hk, mapEntry, sepEntry, image⟩
    have hiM := M.transitive (members I) hi
    have hjM := M.transitive (members J) hj
    have hSM := M.pair_right (M.transitive (members Maps) mapEntry)
    have heM := M.transitive (members D) he
    have hyM := M.transitive (members L) hy
    refine ⟨i, hiM, j, hjM, S, hSM, e, heM, y, hyM, ?_⟩
    apply (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hyM (Fin.cases heM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members)))))).2
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula]
    exact ⟨hi, hj, he, hy, equal, hk, mapEntry, sepEntry, image⟩

theorem realize_recursiveSeparatorFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family K I J D L Maps Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (recursiveSeparatorFamilyFormula family K I J D L Maps Ss) env ↔
      env family = recursiveSeparatorFamily (env K) (env I) (env J) (env D) (env L) (env Maps) (env Ss) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    unfold recursiveSeparatorFamily familyEvaluationGraph at member
    obtain ⟨k, hk, y, hy, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    exact M.orderedPair_mem pairing (M.transitive (members K) hk) (M.transitive (members L) hy)
  · intro z hz
    exact M.realize_recursiveSeparatorEntryFormula 0 K.succ I.succ J.succ D.succ L.succ Maps.succ Ss.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
