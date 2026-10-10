import OAI.SetTheory.PartitionPrinciple.Forcing.GroundActionFilterImages
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundActionPostcomposition
import OAI.SetTheory.PartitionPrinciple.Forcing.TaskTransportCodes

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def actionImageEqualityFormula {n} (P A g F output : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.mem 0 P.succ))
    (.allMem P (.conj
      (imp (.mem 0 output.succ) (actionImageFormula 0 A.succ g.succ F.succ))
      (imp (actionImageFormula 0 A.succ g.succ F.succ) (.mem 0 output.succ))))

theorem truth_actionImageEqualityFormula {n} (P A g F output : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionImageEqualityFormula P A g F output) env ↔
      env output = actionImage (env P) (env A) (env g) (env F) := by
  simp only [actionImageEqualityFormula, Truth, truth_imp, truth_actionImageFormula, ← iff_def]
  constructor
  · rintro ⟨subset, entries⟩
    apply ZFSet.ext
    intro y
    rw [mem_actionImage]
    exact ⟨fun hy => ⟨subset y hy, (entries y (subset y hy)).1 hy⟩,
      fun hy => (entries y hy.1).2 hy.2⟩
  · intro equal
    refine ⟨?_, ?_⟩
    · intro y hy
      exact actionImage_subset _ _ _ _ (equal ▸ hy)
    · intro y hy
      change y ∈ env output ↔ ∃ x ∈ env F, ZFSet.pair (ZFSet.pair (env g) x) y ∈ env A
      rw [equal, mem_actionImage]
      exact ⟨And.right, fun h => ⟨hy, h⟩⟩

def taskTransportFormula {n} (P R U Labels A g t t' : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  exMem P (exMem P.succ (exMem R.succ.succ (exMem P.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Labels.succ.succ.succ.succ.succ
      (exMem P.succ.succ.succ.succ.succ.succ
        (exMem R.succ.succ.succ.succ.succ.succ.succ
          (exMem P.succ.succ.succ.succ.succ.succ.succ.succ
            (exMem U.succ.succ.succ.succ.succ.succ.succ.succ.succ
              (.conj (literalTaskFormula (lift t) 9 8 7 6 5 4)
                (.conj (literalTaskFormula (lift t') 9 3 2 1 0 4)
                  (.conj (tripleMembershipFormula (lift g) 8 3 (lift A))
                    (.conj (tripleMembershipFormula (lift g) 6 1 (lift A))
                      (.conj (actionPostcomposeFormula (lift P) (lift A) (lift g) 7 2)
                        (actionImageEqualityFormula (lift P) (lift A) (lift g) 5 0)))))))))))))))

theorem truth_taskTransportFormula {n} (P R U Labels A g t t' : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskTransportFormula P R U Labels A g t t') env ↔
      TaskTransportCode (env P) (env R) (env U) (env Labels) (env A) (env g) (env t) (env t') := by
  simp only [taskTransportFormula, truth_exMem, Truth, truth_literalTaskFormula,
    truth_tripleMembershipFormula, truth_actionPostcomposeFormula, truth_actionImageEqualityFormula]
  rfl

def taskTransportEntryFormula {n} (z G I P R U Labels A : Fin n) : BoundedFormula n :=
  exMem G (exMem I.succ (exMem I.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (taskTransportFormula P.succ.succ.succ R.succ.succ.succ U.succ.succ.succ
        Labels.succ.succ.succ A.succ.succ.succ 2 1 0))))

theorem truth_taskTransportEntryFormula {n} (z G I P R U Labels A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskTransportEntryFormula z G I P R U Labels A) env ↔
      ∃ g ∈ env G, ∃ t ∈ env I, ∃ t' ∈ env I,
        env z = ZFSet.pair (ZFSet.pair g t) t' ∧
          TaskTransportCode (env P) (env R) (env U) (env Labels) (env A) g t t' := by
  simp only [taskTransportEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_taskTransportFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
