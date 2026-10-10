import OAI.Topology.ArtinGroups.Harmonic.PositivePrefixMulLeft
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeSublevelFinite

namespace OAI

/-! The greedy head of a product with a simple left factor. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

/-- If `h` is the greatest simple prefix of `b`, the greatest simple prefix
of `a*b` is `a*g`, where `g` is the gcd of the complement of `a` and `h`.
This is the local normal-form step used in folding. -/
theorem positive_head_product
    (cancel : ∀ a b c : PositiveArtin M, a*b=a*c → b=c)
    (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
    (a h g : M.Group) (b : PositiveArtin M)
    (hh : PositivePrefix M (positiveSimpleLift M h) b)
    (hhead : ∀ w, PositivePrefix M (positiveSimpleLift M w) b →
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h))
    (hgc : PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M (a⁻¹*z)))
    (hgh : PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M h))
    (hgreat : ∀ e, PositivePrefix M e (positiveSimpleLift M (a⁻¹*z)) →
      PositivePrefix M e (positiveSimpleLift M h) → PositivePrefix M e (positiveSimpleLift M g)) :
    ∃ k : M.Group, positiveSimpleLift M k=positiveSimpleLift M a*positiveSimpleLift M g ∧
      PositivePrefix M (positiveSimpleLift M k) (positiveSimpleLift M a*b) ∧
      ∀ w, PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M a*b) →
        PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M k) := by
  have complement := positiveSimpleLift_left_complement M z hz a
  have hag : PositivePrefix M (positiveSimpleLift M a*positiveSimpleLift M g)
      (positiveSimpleLift M z) := by
    rw [←complement]
    exact positivePrefix_mul_left M _ hgc
  have hsimple := positivePrefix_of_simple_eq M hag rfl
  refine ⟨positiveToCoxeter M (positiveSimpleLift M a*positiveSimpleLift M g),
    hsimple.symm, ?_, ?_⟩
  · rw [←hsimple]
    exact positivePrefix_mul_left M _ (positivePrefix_trans M hgh hh)
  · intro w hw
    rw [←hsimple]
    have haZ : PositivePrefix M (positiveSimpleLift M a) (positiveSimpleLift M z) :=
      ⟨_, complement.symm⟩
    have hwZ : PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M z) :=
      ⟨_, (positiveSimpleLift_left_complement M z hz w).symm⟩
    obtain ⟨c,hac,hwc,hc⟩ := positive_lcm_of_common_multiple M
      (positive_greatest_common_left_divisor M cancel z hz) _ _ ⟨_,haZ,hwZ⟩
    have hcZ := hc _ haZ hwZ
    have hcab := hc _ ⟨b,rfl⟩ hw
    obtain ⟨e,he⟩ := hac
    have hcSimple := positivePrefix_of_simple_eq M hcZ rfl
    have heSimple := (positive_simple_factors M _ _ _ (he.symm.trans hcSimple)).2
    have heB : PositivePrefix M e b :=
      (positivePrefix_mul_left_iff M cancel _ _ _).mp (by rwa [←he])
    have heC : PositivePrefix M e (positiveSimpleLift M (a⁻¹*z)) :=
      (positivePrefix_mul_left_iff M cancel _ _ _).mp (by simpa only [←complement,he] using hcZ)
    have heH : PositivePrefix M e (positiveSimpleLift M h) := by
      rw [heSimple] at heB ⊢
      exact hhead _ heB
    have heg := hgreat e heC heH
    apply positivePrefix_trans M hwc
    rw [he]
    exact positivePrefix_mul_left M _ heg

end HarmonicArtin.ParabolicIntersections

end OAI
