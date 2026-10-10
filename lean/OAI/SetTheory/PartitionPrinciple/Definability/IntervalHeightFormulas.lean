import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCodedBinaryHeights

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def intervalHeightFormula {n} (L r D rD lo hi f : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  let strict : BoundedFormula n :=
    .allMem L (.allMem L.succ (.allMem D.succ.succ (.allMem D.succ.succ.succ
      (imp (.neg (.equal 3 2)) (imp (pairMembershipFormula 3 2 (lift r))
        (imp (pairMembershipFormula 3 1 (lift f))
          (imp (pairMembershipFormula 2 0 (lift f)) (pairMembershipFormula 1 0 (lift rD)))))))))
  let inside : BoundedFormula n :=
    .allMem L (.allMem D.succ (imp (pairMembershipFormula 1 0 f.succ.succ)
      (.conj (pairMembershipFormula lo.succ.succ 0 rD.succ.succ)
        (pairMembershipFormula 0 hi.succ.succ rD.succ.succ))))
  .conj (functionFormula L D f) (.conj strict inside)

theorem truth_intervalHeightFormula {n} (L r D rD lo hi f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalHeightFormula L r D rD lo hi f) env ↔
      IntervalHeightCode (env L) (env r) (env D) (env rD) (env lo) (env hi) (env f) := by
  simp only [intervalHeightFormula, Truth, truth_functionFormula,
    truth_imp, truth_pairMembershipFormula]
  change (ZFSet.IsFunc (env L) (env D) (env f) ∧
    (∀ x ∈ env L, ∀ y ∈ env L, ∀ a ∈ env D, ∀ b ∈ env D,
      x ≠ y → ZFSet.pair x y ∈ env r → ZFSet.pair x a ∈ env f →
        ZFSet.pair y b ∈ env f → ZFSet.pair a b ∈ env rD) ∧
    (∀ x ∈ env L, ∀ a ∈ env D, ZFSet.pair x a ∈ env f →
      ZFSet.pair (env lo) a ∈ env rD ∧ ZFSet.pair a (env hi) ∈ env rD)) ↔ _
  constructor
  · rintro ⟨function, strict, inside⟩
    refine ⟨⟨function, ?_⟩, ?_⟩
    · intro x hx y hy different lower a b first second
      exact strict x hx y hy a (ZFSet.pair_mem_prod.1 (function.1 first)).2
        b (ZFSet.pair_mem_prod.1 (function.1 second)).2 different lower first second
    · intro x a entry
      have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
      exact inside x bounds.1 a bounds.2 entry
  · intro code
    refine ⟨code.function, ?_, ?_⟩
    · intro x hx y hy a _ b _ different lower first second
      exact code.strict x hx y hy different lower a b first second
    · intro x _ a _ entry
      exact code.inside x a entry

theorem realize_intervalHeightFormula (M : TransitiveGround.{u}) {n}
    (L r D rD lo hi f : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (intervalHeightFormula L r D rD lo hi f).toFormula env ↔
      IntervalHeightCode (env L) (env r) (env D) (env rD) (env lo) (env hi) (env f) :=
  (realize_toFormula M _ env members).trans (truth_intervalHeightFormula L r D rD lo hi f env)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
