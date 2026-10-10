import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelMonoid
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefix

namespace OAI

/-! Cancelling common atoms in a spherical common left extension. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [LinearOrder S] in
/-- The finite-type fraction theorem gives a common positive extension
whose two positive factors have no common left atom. Choosing the least
sum of positive lengths proves termination of the cancellation process. -/
theorem spherical_reduced_positive_extension (Y : Set S) (hY : IsSpherical M Y)
    (a b : Artin (restrictedMatrix M Y)) :
    ∃ p q : PositiveArtin (restrictedMatrix M Y),
      positiveToArtin _ p*a=positiveToArtin _ q*b ∧
      ∀ s : Y, ¬ (PositivePrefix _ (positiveGenerator _ s) p ∧
        PositivePrefix _ (positiveGenerator _ s) q) := by
  let N := restrictedMatrix M Y
  let f := positiveToArtin N
  obtain ⟨p,q,hpq⟩ := (spherical_positive_monoid_fractions M Y hY (a*b⁻¹)).2
  have he : f p*a=f q*b := by
    have h := congrArg (fun g : Artin N => f p*g*b) hpq
    change f p*(a*b⁻¹)*b=f p*((f p)⁻¹*f q)*b at h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel,
      mul_one, mul_inv_cancel_left] using h
  let P (n : ℕ) := ∃ p q : PositiveArtin N,
    f p*a=f q*b ∧ positiveDegree N p+positiveDegree N q=n
  have hex : ∃ n, P n := ⟨_,p,q,he,rfl⟩
  obtain ⟨p,q,hpq,hlen⟩ := Nat.find_spec hex
  refine ⟨p,q,hpq,?_⟩
  intro s hcommon
  obtain ⟨p',hp'⟩ := hcommon.1
  obtain ⟨q',hq'⟩ := hcommon.2
  have heq : f p'*a=f q'*b := by
    rw [hp',hq',map_mul,map_mul,mul_assoc,mul_assoc] at hpq
    exact mul_left_cancel hpq
  have hlt : positiveDegree N p'+positiveDegree N q'<Nat.find hex := by
    rw [hp',hq'] at hlen
    dsimp only [N] at hlen ⊢
    simp only [positiveDegree_mul,positiveDegree_generator] at hlen
    omega
  exact Nat.find_min hex hlt ⟨p',q',heq,rfl⟩

end HarmonicArtin.ParabolicIntersections

end OAI
