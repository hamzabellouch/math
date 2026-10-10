import OAI.SetTheory.PartitionPrinciple.Definability.TaggedGrowthLayerFormulas
import OAI.SetTheory.PartitionPrinciple.Models.LiteralQuotientRankBounds

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem rank_nonemptyTupleCode_field_le (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) :
    ∀ j, ZFSet.rank (fields j) ≤ ZFSet.rank (nonemptyTupleCode k fields) := by
  induction k with
  | zero => exact Fin.cases le_rfl (fun i => Fin.elim0 i)
  | succ k ih =>
    let tail := nonemptyTupleCode k (fun j => fields j.succ)
    have both : ZFSet.rank ({fields 0, tail} : ZFSet.{u}) <
        ZFSet.rank (ZFSet.pair (fields 0) tail) :=
      ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
    have head : ZFSet.rank (fields 0) < ZFSet.rank (ZFSet.pair (fields 0) tail) :=
      (ZFSet.rank_lt_of_mem (show fields 0 ∈ ({fields 0, tail} : ZFSet.{u}) from
        ZFSet.mem_pair.2 (Or.inl rfl))).trans both
    have rest : ZFSet.rank tail < ZFSet.rank (ZFSet.pair (fields 0) tail) :=
      (ZFSet.rank_lt_of_mem (show tail ∈ ({fields 0, tail} : ZFSet.{u}) from
        ZFSet.mem_pair.2 (Or.inr rfl))).trans both
    exact Fin.cases head.le (fun j => (ih _ j).trans rest.le)

variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem countableLayerWitness_rank_lt {D injection : ZFSet.{u}}
    (hD : ZFSet.rank D < o) (hInjection : ZFSet.rank injection < o) :
    ZFSet.rank (countableLayerWitness D injection) < o :=
  rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (rank_natSetCode_lt limit 0) (Fin.cases hD (fun _ => hInjection)))

theorem copyLayerWitness_rank_lt {I parts Indices Maps W injection : ZFSet.{u}}
    (hI : ZFSet.rank I < o) (hParts : ZFSet.rank parts < o)
    (hIndices : ZFSet.rank Indices < o) (hMaps : ZFSet.rank Maps < o)
    (hW : ZFSet.rank W < o) (hInjection : ZFSet.rank injection < o) :
    ZFSet.rank (copyLayerWitness I parts Indices Maps W injection) < o :=
  rank_nonemptyTupleCode_lt limit 6 _ (Fin.cases (rank_natSetCode_lt limit 1)
    (Fin.cases hI (Fin.cases hParts (Fin.cases hIndices
      (Fin.cases hMaps (Fin.cases hW (fun _ => hInjection)))))))

theorem separatedLayerWitness_rank_lt {I Indices Maps W Components F : ZFSet.{u}}
    (hI : ZFSet.rank I < o) (hIndices : ZFSet.rank Indices < o)
    (hMaps : ZFSet.rank Maps < o) (hW : ZFSet.rank W < o)
    (hComponents : ZFSet.rank Components < o) (hF : ZFSet.rank F < o) :
    ZFSet.rank (separatedLayerWitness I Indices Maps W Components F) < o :=
  rank_nonemptyTupleCode_lt limit 6 _ (Fin.cases (rank_natSetCode_lt limit 2)
    (Fin.cases hI (Fin.cases hIndices (Fin.cases hMaps
      (Fin.cases hW (Fin.cases hComponents (fun _ => hF)))))))

end PartitionPilot.Forcing

end

end OAI
