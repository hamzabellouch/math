import OAI.SetTheory.PartitionPrinciple.Geometry.IntervalEmbeddingFamilyCodes

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def intervalEmbeddingFormula {n} (A D rA rD lo hi f : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  let order : BoundedFormula n :=
    .allMem A (.allMem A.succ (.allMem D.succ.succ (.allMem D.succ.succ.succ
      (imp (pairMembershipFormula 3 1 (lift f))
        (imp (pairMembershipFormula 2 0 (lift f))
          (iffFormula (pairMembershipFormula 3 2 (lift rA))
            (pairMembershipFormula 1 0 (lift rD))))))))
  let inside : BoundedFormula n :=
    .allMem A (.allMem D.succ (imp (pairMembershipFormula 1 0 f.succ.succ)
      (.conj (pairMembershipFormula lo.succ.succ 0 rD.succ.succ)
        (pairMembershipFormula 0 hi.succ.succ rD.succ.succ))))
  .conj (injectionFormula A D f) (.conj order inside)

theorem truth_intervalEmbeddingFormula {n} (A D rA rD lo hi f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalEmbeddingFormula A D rA rD lo hi f) env ↔
      IntervalEmbeddingCode (env A) (env D) (env rA) (env rD) (env lo) (env hi) (env f) := by
  simp only [intervalEmbeddingFormula, Truth, truth_injectionFormula,
    truth_imp, truth_pairMembershipFormula, truth_iffFormula]
  change (InjectionCode (env A) (env D) (env f) ∧
    (∀ a ∈ env A, ∀ b ∈ env A, ∀ q ∈ env D, ∀ z ∈ env D,
      ZFSet.pair a q ∈ env f → ZFSet.pair b z ∈ env f →
        (ZFSet.pair a b ∈ env rA ↔ ZFSet.pair q z ∈ env rD)) ∧
    (∀ a ∈ env A, ∀ q ∈ env D, ZFSet.pair a q ∈ env f →
      ZFSet.pair (env lo) q ∈ env rD ∧ ZFSet.pair q (env hi) ∈ env rD)) ↔ _
  constructor
  · rintro ⟨injection, order, inside⟩
    refine ⟨injection, ?_, ?_⟩
    · intro a b q z first second
      have aq := ZFSet.pair_mem_prod.1 (injection.function.1 first)
      have bz := ZFSet.pair_mem_prod.1 (injection.function.1 second)
      exact order a aq.1 b bz.1 q aq.2 z bz.2 first second
    · intro a q entry
      have aq := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
      exact inside a aq.1 q aq.2 entry
  · intro code
    refine ⟨code.injection, ?_, ?_⟩
    · intro a _ b _ q _ z _ first second
      exact code.order a b q z first second
    · intro a _ q _ entry
      exact code.inside a q entry

theorem realize_intervalEmbeddingFormula (M : TransitiveGround.{u}) {n}
    (A D rA rD lo hi f : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (intervalEmbeddingFormula A D rA rD lo hi f).toFormula env ↔
      IntervalEmbeddingCode (env A) (env D) (env rA) (env rD) (env lo) (env hi) (env f) :=
  (realize_toFormula M _ env members).trans
    (truth_intervalEmbeddingFormula A D rA rD lo hi f env)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
