import OAI.SetTheory.PartitionPrinciple.Definability.PairPushFilterFamilies

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem pushFilter_copyPullback_eq_of_coinitial {A L rL μL e F : ZFSet.{u}}
    (function : ZFSet.IsFunc A L e) (filter : MeetFilterCode L rL μL F)
    (coinitial : ∀ x ∈ F, ∃ b ∈ F, ∃ a ∈ A,
      ZFSet.pair a b ∈ e ∧ ZFSet.pair b x ∈ rL) :
    pushFilterCode L rL e (copyPullback A L e F) = F := by
  apply ZFSet.ext
  intro x
  rw [mem_pushFilterCode]
  constructor
  · rintro ⟨hx, a, ha, b, _, image, lower⟩
    obtain ⟨haA, c, hc, _, original⟩ := (mem_copyPullback A L e F a).1 ha
    obtain ⟨_, _, unique⟩ := function.2 a haA
    have equal : b = c := (unique b image).trans (unique c original).symm
    exact filter.upward b (equal.symm ▸ hc) x hx lower
  · intro hx
    obtain ⟨b, hb, a, ha, image, lower⟩ := coinitial x hx
    exact ⟨filter.subset hx, a,
      (mem_copyPullback A L e F a).2 ⟨ha, b, hb, filter.subset hb, image⟩,
      b, filter.subset hb, image, lower⟩

end PartitionPilot.Forcing

end

end OAI
