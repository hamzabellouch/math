import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelLeft
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeSublevelFinite

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem spherical_positive_common_multiple (T:Set S) (hT:IsSpherical M T)
    (a b:PositiveArtin (restrictedMatrix M T)) :
    ∃c:PositiveArtin (restrictedMatrix M T),PositivePrefix (restrictedMatrix M T) a c ∧
      PositivePrefix (restrictedMatrix M T) b c := by
  let f:=positiveToArtin (restrictedMatrix M T)
  obtain ⟨x,y,hxy⟩:=(spherical_positive_monoid_fractions M T hT ((f a)⁻¹*f b)).1
  change (f a)⁻¹*f b=f x*(f y)⁻¹ at hxy
  have he:f (a*x)=f (b*y):=by
    rw [map_mul,map_mul]
    have fraction_mul:=eq_mul_inv_iff_mul_eq.mp hxy
    rw [mul_assoc] at fraction_mul
    exact (inv_mul_eq_iff_eq_mul.mp fraction_mul).symm
  have hpos:a*x=b*y:=spherical_positiveToArtin_injective M T hT he
  exact ⟨a*x,⟨x,rfl⟩,⟨y,hpos⟩⟩

theorem spherical_positive_lcm_left (T:Set S) (hT:IsSpherical M T)
    (a b:PositiveArtin (restrictedMatrix M T)) :
    ∃c:PositiveArtin (restrictedMatrix M T),PositivePrefix (restrictedMatrix M T) a c ∧
      PositivePrefix (restrictedMatrix M T) b c ∧
      ∀d:PositiveArtin (restrictedMatrix M T),PositivePrefix (restrictedMatrix M T) a d→
        PositivePrefix (restrictedMatrix M T) b d→PositivePrefix (restrictedMatrix M T) c d :=
  positive_lcm_of_common_multiple _ (spherical_positive_gcd_left M T hT) a b
    (spherical_positive_common_multiple M T hT a b)

end HarmonicArtin

end OAI
