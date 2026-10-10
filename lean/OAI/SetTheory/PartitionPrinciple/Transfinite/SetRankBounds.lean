import OAI.SetTheory.PartitionPrinciple.Definability.SetPresentations

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {x y : ZFSet.{u}}
include limit

theorem rank_singleton_lt (hx : ZFSet.rank x < o) : ZFSet.rank {x} < o := by
  rw [ZFSet.rank_singleton]
  exact limit.succ_lt hx

theorem rank_unorderedPair_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank {x, y} < o := by
  rw [ZFSet.rank_pair]
  exact max_lt (limit.succ_lt hx) (limit.succ_lt hy)

theorem rank_orderedPair_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank (ZFSet.pair x y) < o :=
  rank_unorderedPair_lt limit (rank_singleton_lt limit hx) (rank_unorderedPair_lt limit hx hy)

theorem rank_product_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank (ZFSet.prod x y) < o := by
  have sub : ZFSet.prod x y ⊆ ZFSet.powerset (ZFSet.powerset (x ∪ y)) := by
    intro z hz
    rw [ZFSet.prod, ZFSet.pairSep] at hz
    exact (ZFSet.mem_sep.1 hz).1
  have bound := ZFSet.rank_mono sub
  rw [ZFSet.rank_powerset, ZFSet.rank_powerset, ZFSet.rank_union] at bound
  exact bound.trans_lt (limit.succ_lt (limit.succ_lt (max_lt hx hy)))

namespace Presentation
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem product_rank_lt (hs : ZFSet.rank s.carrier < o) (ht : ZFSet.rank t.carrier < o) :
    ZFSet.rank (s.product t).carrier < o :=
  rank_product_lt limit hs ht

omit limit in
theorem subset_rank_lt (hs : ZFSet.rank s.carrier < o) (p : A → Prop) :
    ZFSet.rank (s.subset p) < o :=
  (s.rank_subset_le p).trans_lt hs

end Presentation

end PartitionPilot.SetRealization

end

end OAI
