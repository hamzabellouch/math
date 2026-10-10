import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FiniteArtinPositiveLeft
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordMonoid

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable abbrev sphericalPositiveCancelMonoid (T:Set S) (hT:IsSpherical M T) :
    CancelMonoid (PositiveArtin (restrictedMatrix M T)) := by
  let f:PositiveArtin (restrictedMatrix M T) →* Artin M :=
    (restrictedArtinHom M T).comp (positiveToArtin (restrictedMatrix M T))
  exact Function.Injective.cancelMonoid f (spherical_positiveToAmbient_injective M T hT)
    f.map_one f.map_mul f.map_pow

theorem spherical_positiveToArtin_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective (positiveToArtin (restrictedMatrix M T)) := by
  intro a b h
  apply spherical_positiveToAmbient_injective M T hT
  exact congrArg (restrictedArtinHom M T) h

omit [LinearOrder S] in
theorem spherical_positive_monoid_fractions (T:Set S) (hT:IsSpherical M T)
    (g:Artin (restrictedMatrix M T)) :
    (∃a b:PositiveArtin (restrictedMatrix M T),g=positiveToArtin _ a*(positiveToArtin _ b)⁻¹) ∧
    (∃c d:PositiveArtin (restrictedMatrix M T),g=(positiveToArtin _ c)⁻¹*positiveToArtin _ d) := by
  have : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  constructor
  · obtain ⟨a,b,h⟩:=finiteArtin_positive_fraction (restrictedMatrix M T) g
    exact ⟨wordPositive _ a,wordPositive _ b,by simpa only [positiveToArtin_word] using h⟩
  · obtain ⟨a,b,h⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) g
    exact ⟨wordPositive _ a,wordPositive _ b,by simpa only [positiveToArtin_word] using h⟩

end HarmonicArtin

end OAI
