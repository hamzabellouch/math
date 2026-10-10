import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.IndexedOperationLiftCodes

namespace OAI

section

namespace PartitionPilot.Forcing
universe u
namespace BoundedFormula
open SetFormula

def indexedRelationLiftEntryFormula : BoundedFormula 8 :=
  exMem 3 (exMem 4 (exMem 3 (exMem 9 (exMem 11 (exMem 7 (exMem 8
    (.conj (orderedPairFormula 7 6 5)
      (.conj (pairMembershipFormula 4 3 11)
        (.conj (pairMembershipFormula 4 2 12)
          (.conj (pairMembershipFormula 1 6 2)
            (.conj (pairMembershipFormula 0 5 2)
              (pairMembershipFormula 1 0 3))))))))))))

theorem truth_indexedRelationLiftEntryFormula (env : Fin 8 → ZFSet.{u}) :
    Truth indexedRelationLiftEntryFormula env ↔
      ∃ p ∈ env 3, ∃ q ∈ env 3, ∃ i ∈ env 1,
        ∃ r ∈ env 6, ∃ e ∈ env 7, ∃ x ∈ env 2, ∃ y ∈ env 2,
          env 0 = ZFSet.pair p q ∧ ZFSet.pair i r ∈ env 4 ∧
          ZFSet.pair i e ∈ env 5 ∧ ZFSet.pair x p ∈ e ∧
          ZFSet.pair y q ∈ e ∧ ZFSet.pair x y ∈ r := by
  simp only [indexedRelationLiftEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

def indexedBinaryLiftEntryFormula : BoundedFormula 8 :=
  exMem 3 (exMem 4 (exMem 5 (exMem 4 (exMem 10 (exMem 12 (exMem 8 (exMem 9 (exMem 10
    (.conj (orderedTripleFormula 9 8 7 6)
      (.conj (pairMembershipFormula 5 4 13)
        (.conj (pairMembershipFormula 5 3 14)
          (.conj (pairMembershipFormula 2 8 3)
            (.conj (pairMembershipFormula 1 7 3)
              (.conj (pairMembershipFormula 0 6 3)
                (tripleMembershipFormula 2 1 0 4)))))))))))))))

theorem truth_indexedBinaryLiftEntryFormula (env : Fin 8 → ZFSet.{u}) :
    Truth indexedBinaryLiftEntryFormula env ↔
      ∃ p ∈ env 3, ∃ q ∈ env 3, ∃ v ∈ env 3, ∃ i ∈ env 1,
        ∃ b ∈ env 6, ∃ e ∈ env 7, ∃ x ∈ env 2, ∃ y ∈ env 2, ∃ z ∈ env 2,
          env 0 = ZFSet.pair (ZFSet.pair p q) v ∧ ZFSet.pair i b ∈ env 4 ∧
          ZFSet.pair i e ∈ env 5 ∧ ZFSet.pair x p ∈ e ∧
          ZFSet.pair y q ∈ e ∧ ZFSet.pair z v ∈ e ∧
          ZFSet.pair (ZFSet.pair x y) z ∈ b := by
  simp only [indexedBinaryLiftEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
open scoped ZFSet
variable (M : TransitiveGround.{u})

theorem indexedRelationLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U Q R J : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hR : R ∈ M.sets) (hJ : J ∈ M.sets) :
    indexedRelationLift T U Q R J ∈ M.sets := by
  have hBR := M.union_mem unions (M.union_mem unions hR)
  have hBJ := M.union_mem unions (M.union_mem unions hJ)
  let params := extend T (extend U (extend Q (extend R (extend J
    (extend (⋃₀ ⋃₀ R) (extend (⋃₀ ⋃₀ J) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedRelationLiftEntryFormula
    params (Fin.cases hT (Fin.cases hU (Fin.cases hQ (Fin.cases hR (Fin.cases hJ
      (Fin.cases hBR (Fin.cases hBJ (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hQ hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedRelationLiftEntryFormula
      (extend z params)) (ZFSet.prod Q Q) = indexedRelationLift T U Q R J := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedRelationLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedRelationLiftEntryFormula]
    rfl
  exact equal ▸ selected

theorem indexedBinaryLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U Q B J : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hB : B ∈ M.sets) (hJ : J ∈ M.sets) :
    indexedBinaryLift T U Q B J ∈ M.sets := by
  have hBB := M.union_mem unions (M.union_mem unions hB)
  have hBJ := M.union_mem unions (M.union_mem unions hJ)
  let params := extend T (extend U (extend Q (extend B (extend J
    (extend (⋃₀ ⋃₀ B) (extend (⋃₀ ⋃₀ J) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedBinaryLiftEntryFormula
    params (Fin.cases hT (Fin.cases hU (Fin.cases hQ (Fin.cases hB (Fin.cases hJ
      (Fin.cases hBB (Fin.cases hBJ (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hQ hQ) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedBinaryLiftEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod Q Q) Q) = indexedBinaryLift T U Q B J := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedBinaryLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedBinaryLiftEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
