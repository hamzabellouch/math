import OAI.SetTheory.PartitionPrinciple.Definability.TaskCapFamilyCodes

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem relationImage_retarget_eq {A Q V F e : ZFSet.{u}}
    (shape : e ⊆ ZFSet.prod A Q) (subset : Q ⊆ V) :
    relationImage F V e = relationImage F Q e := by
  apply ZFSet.ext
  intro x
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨_, f, hf, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 (shape entry)).2, f, hf, entry⟩
  · rintro ⟨hx, f, hf, entry⟩
    exact ⟨subset hx, f, hf, entry⟩

namespace CodedCapProfile
variable {P r μ c E K F : ZFSet.{u}}

theorem fixedTop (profile : CodedCapProfile P r μ c E K F) (meet : MeetOrderCode P r μ) :
    CodedCapProfile (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) c E K F := by
  refine ⟨fixedTopCarrier_old profile.target_mem, fixedTopCarrier_old profile.separator_mem,
    fixedTopCarrier_old profile.cap_mem, fun _ hf => fixedTopCarrier_old (profile.filter_subset hf),
    profile.nonempty, ?_, fixedTopOrder_subset P r profile.target_below_cap,
    fun lower => profile.cap_not_below_target ((fixedTopOrder_old_iff profile.target_mem).1 lower),
    fun lower => profile.separator_not_below_cap ((fixedTopOrder_old_iff profile.cap_mem).1 lower)⟩
  intro x hx above
  rcases (mem_fixedTopCarrier P x).1 hx with equal | oldx
  · subst x
    have positive : ∃ f ∈ F, ZFSet.pair f P ∈ fixedTopOrder P r := by
      obtain ⟨f, hf⟩ := profile.nonempty
      exact ⟨f, hf, fixedTopOrder_greatest (fixedTopCarrier_old (profile.filter_subset hf))⟩
    exact ⟨fun _ => fixedTopOrder_greatest (fixedTopCarrier_old profile.cap_mem),
      fun negative => False.elim (negative positive)⟩
  · have old := profile.profile x oldx ((fixedTopOrder_old_iff oldx).1 above)
    have positive : (∃ f ∈ F, ZFSet.pair f x ∈ fixedTopOrder P r) ↔
        ∃ f ∈ F, ZFSet.pair f x ∈ r := by
      simp only [fixedTopOrder_old_iff oldx]
    exact ⟨fun hp => fixedTopOrder_subset P r (old.1 (positive.1 hp)),
      fun hn => fixedTopMeet_subset meet (old.2 (fun hp => hn (positive.2 hp)))⟩

end CodedCapProfile

namespace OldProfilePreservationCode
variable {P r μ Q R ν e Filters : ZFSet.{u}}

theorem fixedTop (preserved : OldProfilePreservationCode P r μ Q R ν e Filters)
    (target : MeetOrderCode Q R ν) (shape : e ⊆ ZFSet.prod P Q) :
    OldProfilePreservationCode P r μ (fixedTopCarrier Q) (fixedTopOrder Q R)
      (fixedTopMeet Q R) e Filters := by
  intro F hF c hc E hE K hK profile c' _ E' _ K' _ imageC imageE imageK
  have inherited := preserved F hF c hc E hE K hK profile
    c' (ZFSet.pair_mem_prod.1 (shape imageC)).2
    E' (ZFSet.pair_mem_prod.1 (shape imageE)).2
    K' (ZFSet.pair_mem_prod.1 (shape imageK)).2 imageC imageE imageK
  rw [relationImage_retarget_eq shape (fixedTopCarrier_subset Q)]
  exact inherited.fixedTop target

end OldProfilePreservationCode

end PartitionPilot.Forcing

end

end OAI
