import OAI.SetTheory.PartitionPrinciple.Geometry.FiniteWordOperations

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def finiteWordAppendFormula {k} (a omega add f g h : Fin k) : BoundedFormula k :=
  exMem omega (exMem omega.succ (exMem omega.succ.succ
    (.conj (functionFormula 2 a.succ.succ.succ f.succ.succ.succ)
      (.conj (functionFormula 1 a.succ.succ.succ g.succ.succ.succ)
        (.conj (functionFormula 0 a.succ.succ.succ h.succ.succ.succ)
          (.conj (tripleMembershipFormula 2 1 0 add.succ.succ.succ)
            (.allMem 0 (.allMem a.succ.succ.succ.succ
              (let left := pairMembershipFormula 1 0 h.succ.succ.succ.succ.succ
               let right := disj (pairMembershipFormula 1 0 f.succ.succ.succ.succ.succ)
                 (exMem 3 (.conj (tripleMembershipFormula 5 0 2 add.succ.succ.succ.succ.succ.succ)
                   (pairMembershipFormula 0 1 g.succ.succ.succ.succ.succ.succ)))
               .conj (imp left right) (imp right left))))))))))

theorem truth_finiteWordAppendFormula {k} (a omega add f g h : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordAppendFormula a omega add f g h) env ↔
      FiniteWordAppendCode (env a) (env omega) (env add) (env f) (env g) (env h) := by
  simp only [finiteWordAppendFormula, truth_exMem, Truth, truth_functionFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_disj, truth_imp,
    ← iff_def, FiniteWordAppendCode]
  rfl

def finiteWordReverseFormula {k} (a omega add f h : Fin k) : BoundedFormula k :=
  exMem omega (.conj (functionFormula 0 a.succ f.succ)
    (.conj (functionFormula 0 a.succ h.succ)
      (.allMem 0 (.allMem a.succ.succ
        (let left := pairMembershipFormula 1 0 h.succ.succ.succ
         let right := exMem 2 (exMem 3
           (.conj (tripleMembershipFormula 3 1 0 add.succ.succ.succ.succ.succ)
             (.conj (successorFormula 4 0) (pairMembershipFormula 1 2 f.succ.succ.succ.succ.succ))))
         .conj (imp left right) (imp right left))))))

theorem truth_finiteWordReverseFormula {k} (a omega add f h : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordReverseFormula a omega add f h) env ↔
      FiniteWordReverseCode (env a) (env omega) (env add) (env f) (env h) := by
  simp only [finiteWordReverseFormula, truth_exMem, Truth, truth_functionFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_successorFormula,
    truth_imp, ← iff_def, FiniteWordReverseCode]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end OAI
