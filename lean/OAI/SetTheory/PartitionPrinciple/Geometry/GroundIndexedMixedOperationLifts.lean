import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.IndexedMixedOperationLiftCodes

namespace OAI

section

namespace PartitionPilot.Forcing
universe u
namespace BoundedFormula
open SetFormula

def indexedMixedBinaryLiftEntryFormula : BoundedFormula 12 :=
  exMem 4 <| exMem 6 <| exMem 7 <| exMem 4 <| exMem 13 <|
    exMem 15 <| exMem 17 <| exMem 9 <| exMem 11 <| exMem 12 <|
      .conj (orderedTripleFormula 10 9 8 7) <|
        .conj (pairMembershipFormula 6 5 16) <|
          .conj (pairMembershipFormula 6 4 17) <|
            .conj (pairMembershipFormula 6 3 18) <|
              .conj (pairMembershipFormula 2 9 4) <|
                .conj (pairMembershipFormula 1 8 3) <|
                  .conj (pairMembershipFormula 0 7 3) (tripleMembershipFormula 2 1 0 5)

theorem truth_indexedMixedBinaryLiftEntryFormula (env : Fin 12 → ZFSet.{u}) :
    Truth indexedMixedBinaryLiftEntryFormula env ↔
      ∃ g ∈ env 4, ∃ p ∈ env 5, ∃ q ∈ env 5, ∃ i ∈ env 1,
        ∃ a ∈ env 9, ∃ eG ∈ env 10, ∃ eP ∈ env 11,
          ∃ u ∈ env 2, ∃ x ∈ env 3, ∃ y ∈ env 3,
            env 0 = ZFSet.pair (ZFSet.pair g p) q ∧
              ZFSet.pair i a ∈ env 6 ∧ ZFSet.pair i eG ∈ env 7 ∧ ZFSet.pair i eP ∈ env 8 ∧
              ZFSet.pair u g ∈ eG ∧ ZFSet.pair x p ∈ eP ∧ ZFSet.pair y q ∈ eP ∧
              ZFSet.pair (ZFSet.pair u x) y ∈ a := by
  simp only [indexedMixedBinaryLiftEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem indexedMixedBinaryLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T UG UP G P A JG JP : ZFSet.{u}} (hT : T ∈ M.sets) (hUG : UG ∈ M.sets)
    (hUP : UP ∈ M.sets) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
    (hA : A ∈ M.sets) (hJG : JG ∈ M.sets) (hJP : JP ∈ M.sets) :
    indexedMixedBinaryLift T UG UP G P A JG JP ∈ M.sets := by
  have hBA := M.union_mem unions (M.union_mem unions hA)
  have hBJG := M.union_mem unions (M.union_mem unions hJG)
  have hBJP := M.union_mem unions (M.union_mem unions hJP)
  let params := extend T (extend UG (extend UP (extend G (extend P (extend A (extend JG
    (extend JP (extend A.sUnion.sUnion (extend JG.sUnion.sUnion
      (extend JP.sUnion.sUnion Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedMixedBinaryLiftEntryFormula
    params (Fin.cases hT (Fin.cases hUG (Fin.cases hUP (Fin.cases hG (Fin.cases hP
      (Fin.cases hA (Fin.cases hJG (Fin.cases hJP (Fin.cases hBA (Fin.cases hBJG
        (Fin.cases hBJP (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hP) hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedMixedBinaryLiftEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod G P) P) = indexedMixedBinaryLift T UG UP G P A JG JP := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedMixedBinaryLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedMixedBinaryLiftEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
