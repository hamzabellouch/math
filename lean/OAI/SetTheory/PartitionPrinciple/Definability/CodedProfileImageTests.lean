import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFinalInsertionExceptions

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace MeetEmbeddingCode
variable {P Q r R μ ν e F x x' : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P Q r R μ ν e)
variable (source : MeetOrderCode P r μ) (target : MeetOrderCode Q R ν)

include embedding source target in
theorem profilePositive_image_iff (subset : F ⊆ P) (image : ZFSet.pair x x' ∈ e) :
    (∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) ↔
      ∃ f ∈ F, ZFSet.pair f x ∈ r := by
  constructor
  · rintro ⟨f', member, lower⟩
    obtain ⟨_, f, hf, entry⟩ := (mem_relationImage F Q e f').1 member
    exact ⟨f, hf, (embedding.order_iff source target entry image).1 lower⟩
  · rintro ⟨f, hf, lower⟩
    obtain ⟨f', entry, _⟩ := embedding.injection.function.2 f (subset hf)
    exact ⟨f', (mem_relationImage F Q e f').2
      ⟨(ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2, f, hf, entry⟩,
      embedding.monotone f x f' x' lower entry image⟩

end MeetEmbeddingCode

namespace CodedInsertionProfile
variable {P Q r R μ ν e F c E K c' E' K' x x' : ZFSet.{u}}

theorem at_embedding (profile : CodedInsertionProfile P r μ c E K F)
    (embedding : MeetEmbeddingCode P Q r R μ ν e)
    (source : MeetOrderCode P r μ) (target : MeetOrderCode Q R ν) (subset : F ⊆ P)
    (imageC : ZFSet.pair c c' ∈ e) (imageE : ZFSet.pair E E' ∈ e)
    (imageK : ZFSet.pair K K' ∈ e) (imageX : ZFSet.pair x x' ∈ e)
    (above : ZFSet.pair E' x' ∈ R) :
    ((∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) → ZFSet.pair K' x' ∈ R) ∧
    (¬ (∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) →
      ZFSet.pair (ZFSet.pair K' x') c' ∈ ν) := by
  have hx := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 imageX)).1
  have old := profile x hx ((embedding.order_iff source target imageE imageX).1 above)
  have positive := embedding.profilePositive_image_iff source target subset imageX
  exact ⟨fun hp => embedding.monotone K x K' x' (old.1 (positive.1 hp)) imageK imageX,
    fun hn => embedding.map_meet K x c K' x' c'
      (old.2 (fun hp => hn (positive.2 hp))) imageK imageX imageC⟩

end CodedInsertionProfile
end PartitionPilot.Forcing

end

end OAI
