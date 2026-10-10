import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def componentHeightEntryFormula {n}
    (w I Qs B Hs Cs E C D boundQs boundHs boundE : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 8) := i.succ.succ.succ.succ.succ.succ.succ.succ
  let body : BoundedFormula (n + 8) :=
    .conj (pairOfPairsFormula (lift w) 7 3 1 0)
      (.conj (pairMembershipFormula 7 6 (lift Qs))
        (.conj (pairMembershipFormula 7 5 (lift Hs))
          (.conj (pairMembershipFormula 7 4 (lift E))
            (.conj (pairMembershipFormula 7 1 (lift Cs))
              (.conj (pairMembershipFormula 3 2 5) (pairMembershipFormula 2 0 4))))))
  exMem I (exMem boundQs.succ (exMem boundHs.succ.succ
    (exMem boundE.succ.succ.succ (exMem 2
      (exMem B.succ.succ.succ.succ.succ
        (exMem C.succ.succ.succ.succ.succ.succ
          (exMem D.succ.succ.succ.succ.succ.succ.succ body)))))))

theorem truth_componentHeightEntryFormula {n}
    (w I Qs B Hs Cs E C D boundQs boundHs boundE : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (componentHeightEntryFormula w I Qs B Hs Cs E C D boundQs boundHs boundE) env ↔
      ∃ i ∈ env I, ∃ Q ∈ env boundQs, ∃ g ∈ env boundHs, ∃ f ∈ env boundE,
        ∃ q ∈ Q, ∃ a ∈ env B, ∃ c ∈ env C, ∃ z ∈ env D,
          env w = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair c z) ∧
          ZFSet.pair i Q ∈ env Qs ∧ ZFSet.pair i g ∈ env Hs ∧ ZFSet.pair i f ∈ env E ∧
          ZFSet.pair i c ∈ env Cs ∧ ZFSet.pair q a ∈ g ∧ ZFSet.pair a z ∈ f := by
  simp only [componentHeightEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

def taggedHeightEntryFormula {n} (w P N H fresh : Fin n) : BoundedFormula n :=
  exMem N (exMem H.succ
    (.conj (orderedTripleFormula w.succ.succ P.succ.succ 1 0)
      (pairMembershipFormula 1 0 fresh.succ.succ)))

theorem truth_taggedHeightEntryFormula {n} (w P N H fresh : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taggedHeightEntryFormula w P N H fresh) env ↔
      ∃ x ∈ env N, ∃ h ∈ env H,
        env w = ZFSet.pair (ZFSet.pair (env P) x) h ∧ ZFSet.pair x h ∈ env fresh := by
  simp only [taggedHeightEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem componentHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs B Hs Cs E C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hB : B ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hCs : Cs ∈ M.sets) (hE : E ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    componentHeightGraph I Qs B Hs Cs E C D ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have hBound := M.union_mem unions (M.union_mem unions hHs)
  have eBound := M.union_mem unions (M.union_mem unions hE)
  let params := extend I (extend Qs (extend B (extend Hs (extend Cs (extend E
    (extend C (extend D (extend (⋃₀ ⋃₀ Qs) (extend (⋃₀ ⋃₀ Hs)
      (extend (⋃₀ ⋃₀ E) Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.componentHeightEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases hB (Fin.cases hHs (Fin.cases hCs
      (Fin.cases hE (Fin.cases hC (Fin.cases hD (Fin.cases qBound
        (Fin.cases hBound (Fin.cases eBound (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation
      (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs)
      (M.prod_mem pairing unions powers separation hC hD))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.componentHeightEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) (extend z params))
      (ZFSet.prod (indexedAttachmentDomain I Qs) (ZFSet.prod C D)) =
      componentHeightGraph I Qs B Hs Cs E C D := by
    apply ZFSet.ext
    intro z
    rw [componentHeightGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_componentHeightEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

theorem taggedHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N H old fresh : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hH : H ∈ M.sets)
    (hold : old ∈ M.sets) (hfresh : fresh ∈ M.sets) :
    taggedHeightGraph P N H old fresh ∈ M.sets := by
  let params := extend P (extend N (extend H (extend fresh Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taggedHeightEntryFormula 0 1 2 3 4) params
    (Fin.cases hP (Fin.cases hN (Fin.cases hH (Fin.cases hfresh (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.taggedExtension_mem pairing unions powers separation hP hN) hH)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taggedHeightEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (taggedExtension P N) H) =
      ZFSet.sep (fun w => ∃ x ∈ N, ∃ h ∈ H,
        w = ZFSet.pair (ZFSet.pair P x) h ∧ ZFSet.pair x h ∈ fresh)
        (ZFSet.prod (taggedExtension P N) H) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taggedHeightEntryFormula 0 1 2 3 4 _)
  exact M.binary_union_mem pairing unions hold (equal ▸ selected)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
