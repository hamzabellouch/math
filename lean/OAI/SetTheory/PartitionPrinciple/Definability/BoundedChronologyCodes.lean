import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def oldMeetFormula {n} (L T r μ birth : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem L (.allMem L.succ (.allMem L.succ.succ
    (.allMem T.succ.succ.succ (.allMem T.succ.succ.succ.succ
      (.allMem T.succ.succ.succ.succ.succ (imp
        (.conj (pairMembershipFormula 4 2 (lift birth))
          (.conj (pairMembershipFormula 5 1 (lift birth))
            (.conj (.mem 2 1) (.conj (.neg (pairMembershipFormula 5 4 (lift r)))
              (.conj (tripleMembershipFormula 5 4 3 (lift μ))
                (pairMembershipFormula 3 0 (lift birth)))))))
        (.mem 0 1)))))))

theorem truth_oldMeetFormula {n} (L T r μ birth : Fin n) (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Truth (oldMeetFormula L T r μ birth) env ↔ OldMeetCode (env r) (env μ) (env birth) := by
  simp only [oldMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · intro property x y z a b c bornY bornX earlier notLower meetXY bornZ
    have xBounds := ZFSet.pair_mem_prod.1 (function.1 bornX)
    have yBounds := ZFSet.pair_mem_prod.1 (function.1 bornY)
    have zBounds := ZFSet.pair_mem_prod.1 (function.1 bornZ)
    exact property x xBounds.1 y yBounds.1 z zBounds.1 a yBounds.2 b xBounds.2 c zBounds.2
      ⟨bornY, bornX, earlier, notLower, meetXY, bornZ⟩
  · intro property x _ y _ z _ a _ b _ c _ condition
    exact property x y z a b c condition.1 condition.2.1 condition.2.2.1
      condition.2.2.2.1 condition.2.2.2.2.1 condition.2.2.2.2.2

def birthBoundFormula {n} (L T birth s : Fin n) : BoundedFormula n :=
  .allMem L (.allMem T.succ (imp (pairMembershipFormula 1 0 birth.succ.succ)
    (disj (.equal 0 s.succ.succ) (.mem 0 s.succ.succ))))

theorem truth_birthBoundFormula {n} (L T birth s : Fin n) (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Truth (birthBoundFormula L T birth s) env ↔
      ∀ x ∈ env L, ∀ t, ZFSet.pair x t ∈ env birth → t = env s ∨ t ∈ env s := by
  simp only [birthBoundFormula, Truth, truth_imp, truth_pairMembershipFormula, truth_disj]
  exact ⟨fun bound x hx t entry => bound x hx t
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2 entry,
    fun bound x hx t _ entry => bound x hx t entry⟩

theorem realize_oldMeetFormula (M : TransitiveGround.{u}) {n}
    (L T r μ birth : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Realize M.sets (oldMeetFormula L T r μ birth).toFormula env ↔
      OldMeetCode (env r) (env μ) (env birth) :=
  (realize_toFormula M _ env members).trans (truth_oldMeetFormula L T r μ birth env function)

theorem realize_birthBoundFormula (M : TransitiveGround.{u}) {n}
    (L T birth s : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Realize M.sets (birthBoundFormula L T birth s).toFormula env ↔
      ∀ x ∈ env L, ∀ t, ZFSet.pair x t ∈ env birth → t = env s ∨ t ∈ env s :=
  (realize_toFormula M _ env members).trans (truth_birthBoundFormula L T birth s env function)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
