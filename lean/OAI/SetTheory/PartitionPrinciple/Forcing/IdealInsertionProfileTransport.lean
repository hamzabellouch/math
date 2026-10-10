import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFinalInsertionExceptions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundHeightPushforward

namespace OAI

section

namespace PartitionPilot.Forcing.IdealEmbeddingCode
open Compression Compression.RecursiveMaps
universe u
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
variable (source : MeetOrderCode P rP μP) (target : MeetOrderCode Q rQ μQ)

noncomputable def toIdealEmbedding : IdealEmbedding source.toMeetOrder target.toMeetOrder where
  toMeetEmbedding := code.toMeetEmbeddingCode.toMeetEmbedding source target
  ideal v z lower := by
    obtain ⟨x, hx, _, entry⟩ := code.ideal v.val _ z.val
      (code.toMeetEmbeddingCode.toMeetEmbedding_entry source target v) z.property lower
    exact ⟨⟨x, hx⟩, (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target ⟨x,hx⟩ z).2 entry⟩

include code source target in
theorem capProfile {top c v K F c' v' K' : ZFSet.{u}}
    (hTop : top ∈ P) (greatest : ∀ x ∈ P, ZFSet.pair x top ∈ rP)
    (profile : CodedCapProfile P rP μP c v K F)
    (imageC : ZFSet.pair c c' ∈ e) (imageV : ZFSet.pair v v' ∈ e) (imageK : ZFSet.pair K K' ∈ e) :
    CodedCapProfile Q rQ μQ c' v' K' (relationImage F Q e) := by
  let embed := code.toIdealEmbedding source target
  have hc' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 imageC)).2
  have hv' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 imageV)).2
  have hK' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 imageK)).2
  have subset : relationImage F Q e ⊆ Q := by
    intro x hx
    exact ((mem_relationImage _ _ _ _).1 hx).1
  have nonempty : ∃ f, f ∈ relationImage F Q e := by
    obtain ⟨f, hf⟩ := profile.nonempty
    obtain ⟨y, entry, _⟩ := code.injection.function.2 f (profile.filter_subset hf)
    exact ⟨y, (mem_relationImage _ _ _ _).2 ⟨(ZFSet.pair_mem_prod.1 (code.injection.function.1 entry)).2, f, hf, entry⟩⟩
  have old := (CodedInsertionProfile.iff_profile source profile.target_mem profile.separator_mem profile.cap_mem
    profile.filter_subset).1 profile.profile
  have ne : ∃ f : {f : ZFSet.{u} // f ∈ P}, f.val ∈ F := by
    obtain ⟨f, hf⟩ := profile.nonempty
    exact ⟨⟨f, profile.filter_subset hf⟩, hf⟩
  have inherited := embed.preservesProfiles ⟨top,hTop⟩ (fun x => greatest x.val x.property)
    ⟨c,profile.target_mem⟩ ⟨v,profile.separator_mem⟩ ⟨K,profile.cap_mem⟩ (fun f => f.val ∈ F)
    ne profile.separator_not_below_cap old
  have ec : embed.toFun ⟨c,profile.target_mem⟩ = ⟨c',hc'⟩ :=
    (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ _).2 imageC
  have ev : embed.toFun ⟨v,profile.separator_mem⟩ = ⟨v',hv'⟩ :=
    (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ _).2 imageV
  have ek : embed.toFun ⟨K,profile.cap_mem⟩ = ⟨K',hK'⟩ :=
    (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ _).2 imageK
  have pred : (fun y : {y : ZFSet.{u} // y ∈ Q} => y.val ∈ relationImage F Q e) =
      imageFamily embed.toMeetEmbedding (fun f => f.val ∈ F) := by
    funext y
    apply propext
    rw [mem_relationImage]
    constructor
    · rintro ⟨_, x, hx, entry⟩
      exact ⟨⟨x,profile.filter_subset hx⟩, hx,
        (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ y).2 entry⟩
    · rintro ⟨x, hx, equal⟩
      exact ⟨y.property, x.val, hx,
        (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target x y).1 equal⟩
  have transported := (profileOver_iff_image embed.toMeetEmbedding _ _ _ _).1 inherited
  rw [ec, ev, ek, ← pred] at transported
  exact ⟨hc', hv', hK', subset, nonempty,
    (CodedInsertionProfile.iff_profile target hc' hv' hK' subset).2 transported,
    code.monotone _ _ _ _ profile.target_below_cap imageC imageK,
    fun lower => profile.cap_not_below_target (code.reflect _ _ _ _ imageK imageC lower),
    fun lower => profile.separator_not_below_cap (code.reflect _ _ _ _ imageV imageK lower)⟩

end PartitionPilot.Forcing.IdealEmbeddingCode

end

end OAI
