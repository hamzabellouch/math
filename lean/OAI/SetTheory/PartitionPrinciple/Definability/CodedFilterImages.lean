import OAI.SetTheory.PartitionPrinciple.Forcing.ActionPostcompositionCodes

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def actionImage (P A g F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ x ∈ F, ZFSet.pair (ZFSet.pair g x) y ∈ A) P

theorem mem_actionImage (P A g F y : ZFSet.{u}) :
    y ∈ actionImage P A g F ↔
      y ∈ P ∧ ∃ x ∈ F, ZFSet.pair (ZFSet.pair g x) y ∈ A :=
  ZFSet.mem_sep

theorem actionImage_subset (P A g F : ZFSet.{u}) : actionImage P A g F ⊆ P :=
  fun y hy => ((mem_actionImage P A g F y).1 hy).1

theorem actionImage_one {G P m e r A F : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subset : F ⊆ P) :
    actionImage P A e F = F := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨_, x, hx, entry⟩ := (mem_actionImage P A e F y).1 hy
    obtain ⟨z, _, unique⟩ := action.function.2 (ZFSet.pair e x)
      (ZFSet.pair_mem_prod.1 (action.function.1 (action.one x (subset hx)))).1
    have equal : y = x := (unique y entry).trans (unique x (action.one x (subset hx))).symm
    exact equal.symm ▸ hx
  · intro hy
    exact (mem_actionImage P A e F y).2 ⟨subset hy, y, hy, action.one y (subset hy)⟩

theorem actionImage_mul {G P m e r A F g h k : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subset : F ⊆ P)
    (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m) :
    actionImage P A k F = actionImage P A g (actionImage P A h F) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzP, x, hx, entry⟩ := (mem_actionImage P A k F z).1 hz
    obtain ⟨y, hy, _⟩ := action.function.2 (ZFSet.pair h x) (ZFSet.pair_mem_prod.2 ⟨hh, subset hx⟩)
    have hyP := (ZFSet.pair_mem_prod.1 (action.function.1 hy)).2
    obtain ⟨w, hw, _⟩ := action.function.2 (ZFSet.pair g y) (ZFSet.pair_mem_prod.2 ⟨hg, hyP⟩)
    have hwP := (ZFSet.pair_mem_prod.1 (action.function.1 hw)).2
    have composed := action.mul g hg h hh k hk x (subset hx) y hyP w hwP product hy hw
    obtain ⟨v, _, unique⟩ := action.function.2 (ZFSet.pair k x) (ZFSet.pair_mem_prod.2 ⟨hk, subset hx⟩)
    have equal : w = z := (unique w composed).trans (unique z entry).symm
    exact (mem_actionImage P A g (actionImage P A h F) z).2
      ⟨hzP, y, (mem_actionImage P A h F y).2 ⟨hyP, x, hx, hy⟩, equal ▸ hw⟩
  · intro hz
    obtain ⟨hzP, y, hy, entry⟩ := (mem_actionImage P A g (actionImage P A h F) z).1 hz
    obtain ⟨hyP, x, hx, first⟩ := (mem_actionImage P A h F y).1 hy
    exact (mem_actionImage P A k F z).2
      ⟨hzP, x, hx, action.mul g hg h hh k hk x (subset hx) y hyP z hzP product first entry⟩

theorem actionImage_inverse {G P m inv e r A F g h : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (subset : F ⊆ P) (hg : g ∈ G) (hh : h ∈ G) (inverse : ZFSet.pair g h ∈ inv) :
    actionImage P A h (actionImage P A g F) = F := by
  rw [← actionImage_mul action subset hh hg group.identity_mem (group.inv_mul g hg h hh inverse)]
  exact actionImage_one action subset

theorem actionImage_lower_bound {G P m e r A F g s t : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subset : F ⊆ P)
    (hg : g ∈ G) (hs : s ∈ P) (entry : ZFSet.pair (ZFSet.pair g s) t ∈ A)
    (lower : ∀ x ∈ F, ZFSet.pair s x ∈ r) :
    ∀ y ∈ actionImage P A g F, ZFSet.pair t y ∈ r := by
  intro y hy
  obtain ⟨hyP, x, hx, acted⟩ := (mem_actionImage P A g F y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
  exact action.monotone g hg s hs x (subset hx) t ht y hyP entry acted (lower x hx)

theorem actionImage_filter {G P m inv e r μ A F g : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (filter : MeetFilterCode P r μ F) :
    MeetFilterCode P r μ (actionImage P A g F) := by
  refine ⟨actionImage_subset P A g F, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨y, entry, _⟩ := action.function.2 (ZFSet.pair g x)
      (ZFSet.pair_mem_prod.2 ⟨hg, filter.subset hx⟩)
    exact ⟨y, (mem_actionImage P A g F y).2
      ⟨(ZFSet.pair_mem_prod.1 (action.function.1 entry)).2, x, hx, entry⟩⟩
  · intro x hx y hy lower
    obtain ⟨_, a, ha, first⟩ := (mem_actionImage P A g F x).1 hx
    obtain ⟨b, hb, second⟩ := action.raw_preimage group hg hy
    exact (mem_actionImage P A g F y).2
      ⟨hy, b, filter.upward a ha b hb ((action.raw_order_iff group meet.order hg first second).1 lower),
        second⟩
  · intro x hx y hy z entry
    obtain ⟨hxP, a, ha, first⟩ := (mem_actionImage P A g F x).1 hx
    obtain ⟨hyP, b, hb, second⟩ := (mem_actionImage P A g F y).1 hy
    obtain ⟨c, oldMeet, _⟩ := meet.operation.2 (ZFSet.pair a b)
      (ZFSet.pair_mem_prod.2 ⟨filter.subset ha, filter.subset hb⟩)
    have hc := filter.closed_meet a ha b hb c oldMeet
    obtain ⟨d, third, _⟩ := action.function.2 (ZFSet.pair g c)
      (ZFSet.pair_mem_prod.2 ⟨hg, filter.subset hc⟩)
    have newMeet := action.raw_map_meet group meet hg oldMeet first second third
    obtain ⟨w, _, unique⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨hxP, hyP⟩)
    have equal : d = z := (unique d newMeet).trans (unique z entry).symm
    exact (mem_actionImage P A g F z).2
      ⟨(ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, c, hc, equal ▸ third⟩

end PartitionPilot.Forcing

end

end OAI
