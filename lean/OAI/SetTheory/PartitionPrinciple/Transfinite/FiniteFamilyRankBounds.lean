import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLiteralTaskFieldRecognition

namespace OAI


namespace PartitionPilot
universe u
namespace SetRealization

theorem rank_functionGraph_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A B f : ZFSet.{u}} (function : ZFSet.IsFunc A B f)
    (source : ZFSet.rank A < o) (target : ZFSet.rank B < o) :
    ZFSet.rank f < o :=
  (ZFSet.rank_mono function.1).trans_lt (rank_product_lt limit source target)

end SetRealization

namespace Forcing
open SetRealization

theorem rank_nonemptyTupleCode_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) (bounds : ∀ j, ZFSet.rank (fields j) < o) :
    ZFSet.rank (nonemptyTupleCode k fields) < o := by
  induction k with
  | zero => exact bounds 0
  | succ k ih => exact rank_orderedPair_lt limit (bounds 0) (ih _ (fun j => bounds j.succ))

end Forcing
end PartitionPilot



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_finiteRange_lt (n : Nat) (f : Fin n → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (f i) < o) : ZFSet.rank (ZFSet.range f) < o := by
  induction n with
  | zero =>
    have empty : ZFSet.range f = ∅ := by
      apply ZFSet.ext
      intro x
      rw [ZFSet.mem_range]
      exact ⟨fun ⟨i, _⟩ => Fin.elim0 i, fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    simpa only [empty, ZFSet.rank_empty] using limit.pos
  | succ n ih =>
    have split : ZFSet.range f = insert (f 0) (ZFSet.range (fun i : Fin n => f i.succ)) := by
      apply ZFSet.ext
      intro x
      rw [ZFSet.mem_range, ZFSet.mem_insert_iff, ZFSet.mem_range]
      constructor
      · rintro ⟨i, equal⟩
        exact Fin.cases (fun h => Or.inl h.symm) (fun j h => Or.inr ⟨j, h⟩) i equal
      · rintro (equal | ⟨i, equal⟩)
        · exact ⟨0, equal.symm⟩
        · exact ⟨i.succ, equal⟩
    rw [split, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (bounds 0)) (ih _ (fun i => bounds i.succ))

theorem rank_constantFamilyGraph_lt {I x : ZFSet.{u}}
    (domain : ZFSet.rank I < o) (value : ZFSet.rank x < o) :
    ZFSet.rank (constantFamilyGraph I x) < o :=
  rank_functionGraph_lt limit (constantFamilyGraph_function I x) domain
    (rank_singleton_lt limit value)

end PartitionPilot.Forcing

end OAI
