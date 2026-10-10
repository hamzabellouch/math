import OAI.SetTheory.PartitionPrinciple.Forcing.ProfileTransport
import OAI.SetTheory.PartitionPrinciple.Transfinite.MainBirthOrigins

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TaskSystem

universe u
variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

theorem step_preservesProfiles (n : Nat) : PreservesProfiles (f.step n) := by
  intro c v K F nonempty separate profile
  exact profile_persists_one_step (f.step n) c v K F nonempty profile separate
    (Attachment.permitted_extension (f.stages n).batch.data (f.stages n).batch.component_meets)

theorem origin_preservesProfiles (n : Nat) : PreservesProfiles (f.origin n) := by
  induction n with
  | zero => exact preservesProfiles_identity P
  | succ n ih => exact preservesProfiles_comp (f.origin n) (f.step n) ih (f.step_preservesProfiles n)

theorem union_preservesProfiles : PreservesProfiles f.originalEmbedding := by
  intro c v K F nonempty separate profile x above
  rcases f.union_cover x with ⟨n, x, rfl⟩
  exact profileOver_at_embedding (f.origin n) (f.inclusionEmbedding n) f.originalEmbedding
    (f.inclusion_original n) c v K F
    (f.origin_preservesProfiles n c v K F nonempty separate profile) x above

end PartitionPilot.Compression.RecursiveMaps.TaskSystem



namespace PartitionPilot.Compression.RecursiveMaps.MainStage

universe u
variable (s : MainStage.{u}) (Label : Type u)

theorem internal_preservesProfiles : PreservesProfiles (s.internalTransition Label).points :=
  (s.tasks Label).union_preservesProfiles

theorem external_preservesProfiles : PreservesProfiles (s.externalTransition Label).points :=
  ((s.requests Label).extensionCopy (s.internal Label).action 1).preservesProfiles
    (s.internal Label).top (s.internal Label).greatest

theorem next_preservesProfiles : PreservesProfiles (s.nextTransition Label).points :=
  preservesProfiles_comp (s.internalTransition Label).points (s.externalTransition Label).points
    (s.internal_preservesProfiles Label) (s.external_preservesProfiles Label)

end PartitionPilot.Compression.RecursiveMaps.MainStage

end

end OAI
