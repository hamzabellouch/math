import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveReverseHom
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelMonoid

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma spherical_positive_cancel_left (T:Set S) (hT:IsSpherical M T)
    (a b c:PositiveArtin (restrictedMatrix M T)) (h:a*b=a*c) : b=c := by
  let := sphericalPositiveCancelMonoid M T hT
  exact mul_left_cancel h

theorem spherical_positive_head (T:Set S) (hT:IsSpherical M T)
    (a:PositiveArtin (restrictedMatrix M T)) : HasPositiveHead (restrictedMatrix M T) a := by
  let:Finite (restrictedMatrix M T).Group:=restricted_finite M T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M T).toCoxeterSystem
  exact positive_greedy_head _ (spherical_positive_cancel_left M T hT) z hz a

theorem spherical_positive_gcd_left (T:Set S) (hT:IsSpherical M T)
    (a b:PositiveArtin (restrictedMatrix M T)) :
    ∃g:PositiveArtin (restrictedMatrix M T),
      PositivePrefix (restrictedMatrix M T) g a ∧ PositivePrefix (restrictedMatrix M T) g b ∧
      ∀e:PositiveArtin (restrictedMatrix M T),PositivePrefix (restrictedMatrix M T) e a→
        PositivePrefix (restrictedMatrix M T) e b→PositivePrefix (restrictedMatrix M T) e g := by
  let:Finite (restrictedMatrix M T).Group:=restricted_finite M T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M T).toCoxeterSystem
  exact positive_greatest_common_left_divisor _ (spherical_positive_cancel_left M T hT) z hz a b

theorem spherical_positive_gcd_right (T:Set S) (hT:IsSpherical M T)
    (a b:PositiveArtin (restrictedMatrix M T)) :
    ∃g:PositiveArtin (restrictedMatrix M T),
      PositiveSuffix (restrictedMatrix M T) g a ∧ PositiveSuffix (restrictedMatrix M T) g b ∧
      ∀e:PositiveArtin (restrictedMatrix M T),PositiveSuffix (restrictedMatrix M T) e a→
        PositiveSuffix (restrictedMatrix M T) e b→PositiveSuffix (restrictedMatrix M T) e g := by
  let:Finite (restrictedMatrix M T).Group:=restricted_finite M T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M T).toCoxeterSystem
  exact positive_greatest_common_right_divisor _ z hz (spherical_positive_cancel_left M T hT) a b

end HarmonicArtin

end OAI
