import OAI.SetTheory.PartitionPrinciple.Definability.IndexedValueLiftCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedValueLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U Q V F J : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hV : V ∈ M.sets) (hF : F ∈ M.sets) (hJ : J ∈ M.sets) :
    indexedValueLift T U Q V F J ∈ M.sets := by
  have hBF := M.union_mem unions (M.union_mem unions hF)
  have hBJ := M.union_mem unions (M.union_mem unions hJ)
  let params := extend T (extend U (extend Q (extend V (extend F (extend J
    (extend (ZFSet.sUnion (ZFSet.sUnion F))
      (extend (ZFSet.sUnion (ZFSet.sUnion J)) Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedValueLiftEntryFormula params
    (Fin.cases hT (Fin.cases hU (Fin.cases hQ (Fin.cases hV (Fin.cases hF
      (Fin.cases hJ (Fin.cases hBF (Fin.cases hBJ (fun i => Fin.elim0 i)))))))))
    (M.prod_mem pairing unions powers separation hQ hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedValueLiftEntryFormula
      (extend z params)) (ZFSet.prod Q V) = indexedValueLift T U Q V F J := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedValueLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedValueLiftEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

theorem indexedValueLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U F J : ZFSet.{u}) {Q V : ZFSet.{u}}
    (hq : ZFSet.rank Q < o) (hv : ZFSet.rank V < o) :
    ZFSet.rank (indexedValueLift T U Q V F J) < o :=
  (ZFSet.rank_mono (indexedValueLift_subset T U Q V F J)).trans_lt (rank_product_lt limit hq hv)

end PartitionPilot.Forcing

end

end OAI
