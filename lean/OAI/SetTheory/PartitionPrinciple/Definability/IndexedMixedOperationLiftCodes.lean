import OAI.SetTheory.PartitionPrinciple.Definability.PresentedGroupCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

noncomputable def indexedMixedBinaryLift (T UG UP G P A JG JP : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ∃ g ∈ G, ∃ p ∈ P, ∃ q ∈ P, ∃ i ∈ T,
    ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion A),
      ∃ eG ∈ ZFSet.sUnion (ZFSet.sUnion JG), ∃ eP ∈ ZFSet.sUnion (ZFSet.sUnion JP),
      ∃ u ∈ UG, ∃ x ∈ UP, ∃ y ∈ UP,
        w = ZFSet.pair (ZFSet.pair g p) q ∧
          ZFSet.pair i a ∈ A ∧ ZFSet.pair i eG ∈ JG ∧ ZFSet.pair i eP ∈ JP ∧
          ZFSet.pair u g ∈ eG ∧ ZFSet.pair x p ∈ eP ∧ ZFSet.pair y q ∈ eP ∧
          ZFSet.pair (ZFSet.pair u x) y ∈ a) (ZFSet.prod (ZFSet.prod G P) P)

theorem indexedMixedBinaryLift_subset (T UG UP G P A JG JP : ZFSet.{u}) :
    indexedMixedBinaryLift T UG UP G P A JG JP ⊆ ZFSet.prod (ZFSet.prod G P) P :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem triple_mem_indexedMixedBinaryLift (T UG UP G P A JG JP g p q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g p) q ∈ indexedMixedBinaryLift T UG UP G P A JG JP ↔
      g ∈ G ∧ p ∈ P ∧ q ∈ P ∧ ∃ i ∈ T, ∃ a eG eP,
        ∃ u ∈ UG, ∃ x ∈ UP, ∃ y ∈ UP,
          ZFSet.pair i a ∈ A ∧ ZFSet.pair i eG ∈ JG ∧ ZFSet.pair i eP ∈ JP ∧
          ZFSet.pair u g ∈ eG ∧ ZFSet.pair x p ∈ eP ∧ ZFSet.pair y q ∈ eP ∧
          ZFSet.pair (ZFSet.pair u x) y ∈ a := by
  rw [indexedMixedBinaryLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, g', hg, p', hp, q', hq, i, hi, a, _, eG, _, eP, _,
      u, hu, x, hx, y, hy, equal, action, actors, points, actor, first, second, source⟩
    obtain ⟨gp, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 gp
    exact ⟨hg, hp, hq, i, hi, a, eG, eP, u, hu, x, hx, y, hy,
      action, actors, points, actor, first, second, source⟩
  · rintro ⟨hg, hp, hq, i, hi, a, eG, eP, u, hu, x, hx, y, hy,
      action, actors, points, actor, first, second, source⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, hp⟩, hq⟩,
      g, hg, p, hp, q, hq, i, hi, a, pair_second_mem_doubleUnion action,
      eG, pair_second_mem_doubleUnion actors, eP, pair_second_mem_doubleUnion points,
      u, hu, x, hx, y, hy, rfl, action, actors, points, actor, first, second, source⟩

theorem indexedMixedBinaryLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T UG UP A JG JP : ZFSet.{u}) {G P : ZFSet.{u}}
    (actors : ZFSet.rank G < o) (points : ZFSet.rank P < o) :
    ZFSet.rank (indexedMixedBinaryLift T UG UP G P A JG JP) < o :=
  (ZFSet.rank_mono (indexedMixedBinaryLift_subset T UG UP G P A JG JP)).trans_lt
    (rank_product_lt limit (rank_product_lt limit actors points) points)

end PartitionPilot.Forcing

end

end OAI
