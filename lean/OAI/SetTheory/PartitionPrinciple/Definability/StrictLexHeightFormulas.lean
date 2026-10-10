import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def strictLexHeightFormula {n} (P C D r height rD : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .conj (functionToProductFormula P C D height)
    (.allMem P (.allMem P.succ (.allMem C.succ.succ (.allMem D.succ.succ.succ
      (.allMem C.succ.succ.succ.succ (.allMem D.succ.succ.succ.succ.succ
        (imp (.conj (pairMembershipFormula 5 4 (lift r))
          (.conj (.neg (.equal 5 4))
            (.conj (rightTripleMembershipFormula 5 3 2 (lift height))
              (rightTripleMembershipFormula 4 1 0 (lift height)))))
          (disj (.mem 3 1) (.conj (.equal 3 1) (pairMembershipFormula 2 0 (lift rD)))))))))))

theorem truth_strictLexHeightFormula {n} (P C D r height rD : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (strictLexHeightFormula P C D r height rD) env ↔
      StrictLexHeightCode (env P) (env C) (env D) (env r) (env height) (env rD) := by
  simp only [strictLexHeightFormula, Truth, truth_functionToProductFormula, truth_imp,
    truth_disj, truth_pairMembershipFormula, truth_rightTripleMembershipFormula]
  constructor
  · rintro ⟨function, strict⟩
    refine ⟨function, ?_⟩
    intro x hx y hy c q d v lower different first second
    have firstBounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 first)).2
    have secondBounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 second)).2
    exact strict x hx y hy c firstBounds.1 q firstBounds.2 d secondBounds.1 v secondBounds.2
      ⟨lower, different, first, second⟩
  · intro code
    refine ⟨code.function, ?_⟩
    intro x hx y hy c _ q _ d _ v _ condition
    exact code.strict x hx y hy c q d v condition.1 condition.2.1
      condition.2.2.1 condition.2.2.2

def heightColumnsBoundFormula {n} (P C D height columns : Fin n) : BoundedFormula n :=
  .allMem P (.allMem C.succ (.allMem D.succ.succ
    (imp (rightTripleMembershipFormula 2 1 0 height.succ.succ.succ)
      (.mem 1 columns.succ.succ.succ))))

theorem truth_heightColumnsBoundFormula {n} (P C D height columns : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (heightColumnsBoundFormula P C D height columns) env ↔
      ∀ x ∈ env P, ∀ c ∈ env C, ∀ q ∈ env D,
        ZFSet.pair x (ZFSet.pair c q) ∈ env height → c ∈ env columns := by
  simp only [heightColumnsBoundFormula, Truth, truth_imp, truth_rightTripleMembershipFormula]
  rfl

theorem truth_heightColumnsBoundFormula_of_function {n} (P C D height columns : Fin n)
    (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env P) (ZFSet.prod (env C) (env D)) (env height)) :
    Truth (heightColumnsBoundFormula P C D height columns) env ↔
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ env height → c ∈ env columns := by
  rw [truth_heightColumnsBoundFormula]
  constructor
  · intro bound x c q entry
    have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
    have coordinates := ZFSet.pair_mem_prod.1 shape.2
    exact bound x shape.1 c coordinates.1 q coordinates.2 entry
  · intro bound x _ c _ q _ entry
    exact bound x c q entry

theorem realize_strictLexHeightFormula (M : TransitiveGround.{u}) {n}
    (P C D r height rD : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (strictLexHeightFormula P C D r height rD).toFormula env ↔
      StrictLexHeightCode (env P) (env C) (env D) (env r) (env height) (env rD) :=
  (realize_toFormula M _ env members).trans (truth_strictLexHeightFormula P C D r height rD env)

theorem realize_heightColumnsBoundFormula (M : TransitiveGround.{u}) {n}
    (P C D height columns : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets)
    (function : ZFSet.IsFunc (env P) (ZFSet.prod (env C) (env D)) (env height)) :
    Realize M.sets (heightColumnsBoundFormula P C D height columns).toFormula env ↔
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ env height → c ∈ env columns :=
  (realize_toFormula M _ env members).trans
    (truth_heightColumnsBoundFormula_of_function P C D height columns env function)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
