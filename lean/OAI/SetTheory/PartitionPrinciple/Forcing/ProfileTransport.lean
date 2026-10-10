import OAI.SetTheory.PartitionPrinciple.Geometry.PrincipalBatch

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u
variable {A B C : Type u} {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}

def PreservesProfiles (e : MeetEmbedding P Q) : Prop :=
  ∀ c v K F, (∃ a, F a) → ¬ P.le v K → Profile P c v K F → ProfileOver e c v K F

theorem profileOver_iff_image (e : MeetEmbedding P Q) (c v K : A) (F : A → Prop) :
    ProfileOver e c v K F ↔
      Profile Q (e.toFun c) (e.toFun v) (e.toFun K) (imageFamily e F) := by
  constructor
  · intro h x above
    exact ⟨fun hp => (h x above).1 ((positive_imageFamily e F x).mp hp),
      fun hn => (h x above).2 (fun hp => hn ((positive_imageFamily e F x).mpr hp))⟩
  · intro h x above
    exact ⟨fun hp => (h x above).1 ((positive_imageFamily e F x).mpr hp),
      fun hn => (h x above).2 (fun hp => hn ((positive_imageFamily e F x).mp hp))⟩

theorem preservesProfiles_identity (P : MeetOrder A) :
    PreservesProfiles (identityIso P).toMeetEmbedding := fun _ _ _ _ _ _ h => h

theorem preservesProfiles_comp (e : MeetEmbedding P Q) (j : MeetEmbedding Q R)
    (he : PreservesProfiles e) (hj : PreservesProfiles j) : PreservesProfiles (compose e j) := by
  intro c v K F nonempty separate profile
  have old := (profileOver_iff_image e c v K F).mp (he c v K F nonempty separate profile)
  have nonempty' : ∃ b, imageFamily e F b := by
    rcases nonempty with ⟨a, ha⟩
    exact ⟨e.toFun a, a, ha, rfl⟩
  have separate' : ¬ Q.le (e.toFun v) (e.toFun K) := fun h => separate ((e.le_iff _ _).mp h)
  have next := hj (e.toFun c) (e.toFun v) (e.toFun K) (imageFamily e F) nonempty' separate' old
  intro x above
  exact ⟨fun hp => (next x above).1 ((positiveOver_imageFamily e j F x).mpr hp),
    fun hn => (next x above).2 (fun hp => hn ((positiveOver_imageFamily e j F x).mp hp))⟩

theorem profileOver_at_embedding (e : MeetEmbedding P Q) (j : MeetEmbedding Q R)
    (i : MeetEmbedding P R) (coherent : ∀ a, j.toFun (e.toFun a) = i.toFun a)
    (c v K : A) (F : A → Prop) (profile : ProfileOver e c v K F) (x : B)
    (above : R.le (i.toFun v) (j.toFun x)) :
    (PositiveOver i F (j.toFun x) → R.le (i.toFun K) (j.toFun x)) ∧
    (¬ PositiveOver i F (j.toFun x) → R.meet (i.toFun K) (j.toFun x) = i.toFun c) := by
  have above' : Q.le (e.toFun v) x := by
    apply (j.le_iff _ _).mp
    rw [coherent]
    exact above
  have positive : PositiveOver i F (j.toFun x) ↔ PositiveOver e F x := by
    constructor
    · rintro ⟨a, ha, lower⟩
      rw [← coherent a] at lower
      exact ⟨a, ha, (j.le_iff _ _).mp lower⟩
    · rintro ⟨a, ha, lower⟩
      refine ⟨a, ha, ?_⟩
      rw [← coherent a]
      exact (j.le_iff _ _).mpr lower
  constructor
  · intro hp
    rw [← coherent K]
    exact (j.le_iff _ _).mpr ((profile x above').1 (positive.mp hp))
  · intro hn
    rw [← coherent K, ← j.map_meet, (profile x above').2 (fun hp => hn (positive.mpr hp)), coherent]

theorem IdealEmbedding.hasOldShadow (e : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) (x : B) : HasOldShadow e.toMeetEmbedding x := by
  refine ⟨e.projection top x, e.greatest_part top greatest x, ?_⟩
  intro a _
  rw [e.map_meet, e.projection_spec]
  apply Q.antisymm
  · exact Q.le_meet
      (Q.le_meet (Q.meet_le_left _ _) (Q.trans (Q.meet_le_right _ _) ((e.le_iff _ _).mpr (greatest a))))
      (Q.meet_le_right _ _)
  · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_left _ _)) (Q.meet_le_right _ _)

theorem IdealEmbedding.preservesProfiles (e : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) : PreservesProfiles e.toMeetEmbedding := by
  intro c v K F nonempty separate profile
  exact profile_persists_one_step e.toMeetEmbedding c v K F nonempty profile separate
    (fun x => Or.inr (Or.inl (e.hasOldShadow top greatest x)))

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
