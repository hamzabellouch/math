import OAI.SetTheory.PartitionPrinciple.Definability.PresentedGroupCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
open scoped ZFSet
universe u

noncomputable def indexedRelationLift (T U Q R J : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ Q, ∃ q ∈ Q, ∃ i ∈ T,
    ∃ r ∈ ⋃₀ ⋃₀ R, ∃ e ∈ ⋃₀ ⋃₀ J, ∃ x ∈ U, ∃ y ∈ U,
      z = ZFSet.pair p q ∧ ZFSet.pair i r ∈ R ∧ ZFSet.pair i e ∈ J ∧
        ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair x y ∈ r)
    (ZFSet.prod Q Q)

theorem indexedRelationLift_subset (T U Q R J : ZFSet.{u}) :
    indexedRelationLift T U Q R J ⊆ ZFSet.prod Q Q :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_indexedRelationLift (T U Q R J p q : ZFSet.{u}) :
    ZFSet.pair p q ∈ indexedRelationLift T U Q R J ↔
      p ∈ Q ∧ q ∈ Q ∧ ∃ i ∈ T, ∃ r e, ∃ x ∈ U, ∃ y ∈ U,
        ZFSet.pair i r ∈ R ∧ ZFSet.pair i e ∈ J ∧
          ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair x y ∈ r := by
  rw [indexedRelationLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, p', hp, q', hq, i, hi, r, _, e, _, x, hx, y, hy, equal, relation, inclusion, first, second, source⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hp, hq, i, hi, r, e, x, hx, y, hy, relation, inclusion, first, second, source⟩
  · rintro ⟨hp, hq, i, hi, r, e, x, hx, y, hy, relation, inclusion, first, second, source⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hp, hq⟩, p, hp, q, hq, i, hi,
      r, pair_second_mem_doubleUnion relation, e, pair_second_mem_doubleUnion inclusion,
      x, hx, y, hy, rfl, relation, inclusion, first, second, source⟩

noncomputable def indexedBinaryLift (T U Q B J : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ∃ p ∈ Q, ∃ q ∈ Q, ∃ v ∈ Q, ∃ i ∈ T,
    ∃ b ∈ ⋃₀ ⋃₀ B, ∃ e ∈ ⋃₀ ⋃₀ J, ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
      w = ZFSet.pair (ZFSet.pair p q) v ∧ ZFSet.pair i b ∈ B ∧ ZFSet.pair i e ∈ J ∧
        ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair z v ∈ e ∧
          ZFSet.pair (ZFSet.pair x y) z ∈ b) (ZFSet.prod (ZFSet.prod Q Q) Q)

theorem indexedBinaryLift_subset (T U Q B J : ZFSet.{u}) :
    indexedBinaryLift T U Q B J ⊆ ZFSet.prod (ZFSet.prod Q Q) Q :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem triple_mem_indexedBinaryLift (T U Q B J p q v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p q) v ∈ indexedBinaryLift T U Q B J ↔
      p ∈ Q ∧ q ∈ Q ∧ v ∈ Q ∧ ∃ i ∈ T, ∃ b e, ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
        ZFSet.pair i b ∈ B ∧ ZFSet.pair i e ∈ J ∧
          ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair z v ∈ e ∧
            ZFSet.pair (ZFSet.pair x y) z ∈ b := by
  rw [indexedBinaryLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, p', hp, q', hq, v', hv, i, hi, b, _, e, _, x, hx, y, hy, z, hz,
      equal, operation, inclusion, first, second, third, source⟩
    obtain ⟨pq, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 pq
    exact ⟨hp, hq, hv, i, hi, b, e, x, hx, y, hy, z, hz,
      operation, inclusion, first, second, third, source⟩
  · rintro ⟨hp, hq, hv, i, hi, b, e, x, hx, y, hy, z, hz,
      operation, inclusion, first, second, third, source⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hp, hq⟩, hv⟩,
      p, hp, q, hq, v, hv, i, hi, b, pair_second_mem_doubleUnion operation,
      e, pair_second_mem_doubleUnion inclusion, x, hx, y, hy, z, hz,
      rfl, operation, inclusion, first, second, third, source⟩

theorem indexedRelationLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U R J : ZFSet.{u}) {Q : ZFSet.{u}} (rank : ZFSet.rank Q < o) :
    ZFSet.rank (indexedRelationLift T U Q R J) < o :=
  (ZFSet.rank_mono (indexedRelationLift_subset T U Q R J)).trans_lt
    (rank_product_lt limit rank rank)

theorem indexedBinaryLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U B J : ZFSet.{u}) {Q : ZFSet.{u}} (rank : ZFSet.rank Q < o) :
    ZFSet.rank (indexedBinaryLift T U Q B J) < o :=
  (ZFSet.rank_mono (indexedBinaryLift_subset T U Q B J)).trans_lt
    (rank_product_lt limit (rank_product_lt limit rank rank) rank)

end PartitionPilot.Forcing

end

end OAI
