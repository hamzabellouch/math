import OAI.SetTheory.PartitionPrinciple.Definability.IntervalEmbeddingFormulas

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def intervalEmbeddingCandidateFormula {n}
    (As rs los his D rD i f boundAs boundRs : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) : Fin (n + 4) := j.succ.succ.succ.succ
  exMem boundAs (exMem boundRs.succ (exMem D.succ.succ (exMem D.succ.succ.succ
    (.conj (pairMembershipFormula (lift i) 3 (lift As))
      (.conj (pairMembershipFormula (lift i) 2 (lift rs))
        (.conj (pairMembershipFormula (lift i) 1 (lift los))
          (.conj (pairMembershipFormula (lift i) 0 (lift his))
            (intervalEmbeddingFormula 3 (lift D) 2 (lift rD) 1 0 (lift f)))))))))

theorem truth_intervalEmbeddingCandidateFormula {n}
    (As rs los his D rD i f boundAs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundAs = ⋃₀ ⋃₀ env As)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalEmbeddingCandidateFormula As rs los his D rD i f boundAs boundRs) env ↔
      intervalEmbeddingCandidate (env As) (env rs) (env los) (env his)
        (env D) (env rD) (env i) (env f) := by
  simp only [intervalEmbeddingCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_intervalEmbeddingFormula]
  change (∃ A ∈ env boundAs, ∃ rA ∈ env boundRs, ∃ lo ∈ env D, ∃ hi ∈ env D,
    ZFSet.pair (env i) A ∈ env As ∧ ZFSet.pair (env i) rA ∈ env rs ∧
    ZFSet.pair (env i) lo ∈ env los ∧ ZFSet.pair (env i) hi ∈ env his ∧
    IntervalEmbeddingCode A (env D) rA (env rD) lo hi (env f)) ↔ _
  rw [sourceBound, orderBound]
  rfl

def intervalEmbeddingRelationEntryFormula {n}
    (z I W As rs los his D rD boundAs boundRs : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (intervalEmbeddingCandidateFormula As.succ.succ rs.succ.succ
        los.succ.succ his.succ.succ D.succ.succ rD.succ.succ 1 0
        boundAs.succ.succ boundRs.succ.succ)))

theorem truth_intervalEmbeddingRelationEntryFormula {n}
    (z I W As rs los his D rD boundAs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundAs = ⋃₀ ⋃₀ env As)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalEmbeddingRelationEntryFormula z I W As rs los his D rD boundAs boundRs) env ↔
      ∃ i ∈ env I, ∃ f ∈ env W, env z = ZFSet.pair i f ∧
        intervalEmbeddingCandidate (env As) (env rs) (env los) (env his)
          (env D) (env rD) i f := by
  simp only [intervalEmbeddingRelationEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro f
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_intervalEmbeddingCandidateFormula
    As.succ.succ rs.succ.succ los.succ.succ his.succ.succ D.succ.succ
    rD.succ.succ 1 0 boundAs.succ.succ boundRs.succ.succ
    (extend f (extend i env)) sourceBound orderBound)

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem intervalEmbeddingRelation_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W As rs los his D rD : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hAs : As ∈ M.sets) (hrs : rs ∈ M.sets)
    (hlos : los ∈ M.sets) (hhis : his ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    intervalEmbeddingRelation I W As rs los his D rD ∈ M.sets := by
  have sourceBound := M.union_mem unions (M.union_mem unions hAs)
  have orderBound := M.union_mem unions (M.union_mem unions hrs)
  let params := extend I (extend W (extend As (extend rs (extend los (extend his
    (extend D (extend rD (extend (⋃₀ ⋃₀ As) (extend (⋃₀ ⋃₀ rs) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalEmbeddingRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hAs (Fin.cases hrs (Fin.cases hlos
      (Fin.cases hhis (Fin.cases hD (Fin.cases hrD (Fin.cases sourceBound
        (Fin.cases orderBound (fun j => Fin.elim0 j)))))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalEmbeddingRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10)
      (extend z params)) (ZFSet.prod I W) =
      intervalEmbeddingRelation I W As rs los his D rD := by
    apply ZFSet.ext
    intro z
    rw [intervalEmbeddingRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_intervalEmbeddingRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10
        (extend z params) rfl rfl)
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
