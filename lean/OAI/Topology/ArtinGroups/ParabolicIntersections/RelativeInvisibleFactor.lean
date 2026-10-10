import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedBoundaryZero
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeMinimumContainment
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTieLower
import OAI.Topology.ArtinGroups.ParabolicIntersections.FixedFactor

namespace OAI

/-! Removing the all-level invisible factor in the nonspherical case of §8. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

/-- Every exterior count below the cutoff is zero. The cutoff is chosen
from the actual finite family, independently of the harmonic minimum. -/
def ExteriorCutoff (Y : Set S) (x : Artin M) (cutoff : ℤ) : Prop :=
  ∀ k, k < cutoff → ∀ v, v ∉ Sum.inl '' Y → pointedMultiplicity M f x k v = 0

lemma exteriorCutoff_exists (Y : Set S) (x : Artin M) :
    ∃ cutoff : ℤ, cutoff ≤ 0 ∧ ExteriorCutoff M f Y x cutoff := by
  obtain ⟨b, hb⟩ := (pointedMultiplicity_support_finite M f x).bddBelow
  refine ⟨min b 0, min_le_right _ _, ?_⟩
  intro k hk v _
  have hz : pointedMultiplicity M f x k = 0 := by
    by_contra hn
    have := hb hn
    have := min_le_left b (0 : ℤ)
    omega
  exact congrFun hz v

lemma relative_profile_exterior {Y : Set S} {x : Artin M}
    (P : RelativeVertex M Y x) (cutoff : ℤ) (k : ℕ) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' Y) :
    pointedProfile M f P.val cutoff k v = pointedMultiplicity M f x (cutoff + k) v := by
  let z := sourceCosetRepresentative M P.val
  have hz : z ∈ rightCoset M Y x := P.property.2 (sourceCosetRepresentative_mem M P.val)
  have hvP : v ∉ Sum.inl '' P.val.val.1 := fun h => hv (Set.image_mono P.property.1 h)
  change pointedCosetVector M f P.val (cutoff+k) v = _
  rw [pointedCosetVector_eq M f P.val z (sourceCosetRepresentative_mem M P.val),
    pointedHarmonicAt_outside M f _ _ _ _ hvP]
  have he := pointedMultiplicity_exterior M Y (z*x⁻¹) hz f x v hv (cutoff+k)
  simpa only [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one] using he

/-- If the containing type is the whole acting type, every exterior
neighbor of the invisible set is absent at every level. -/
lemma relative_invisible_boundary_zero {Y : Set S} {x : Artin M}
    (P : RelativeVertex M Y x) (cutoff : ℤ) (hcut : ExteriorCutoff M f Y x cutoff)
    (hfull : relativeContainingType M f cutoff Y P.val = Y) :
    ∀ k v, v ∉ Sum.inl '' relativeInvisible M f cutoff Y P.val →
      (∃ u ∈ Sum.inl '' relativeInvisible M f cutoff Y P.val, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0 := by
  intro k v hv hn
  obtain ⟨u, hu, hvi⟩ := hn
  obtain ⟨i, hi, hei⟩ := hu
  rw [← hei] at hvi
  have hvY : v ∉ Sum.inl '' Y := by
    rintro ⟨j, hj, rfl⟩
    have hjD : j ∈ relativeContainingType M f cutoff Y P.val := hfull.symm ▸ hj
    rcases hjD with hjV | hjK
    · rw [framedCartan_symm] at hvi
      exact relativeVisible_nonadjacent M f cutoff Y P.val P.property.1 i j hi hjV hvi
    · exact hv ⟨j, hjK, rfl⟩
  by_cases hk : k < cutoff
  · exact hcut k hk v hvY
  · let n := (k-cutoff).toNat
    have he : cutoff + (n : ℤ) = k := by
      dsimp only [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hz : pointedProfile M f P.val cutoff n v = 0 := by
      apply le_antisymm _ (pointedCosetVector_nonneg M f P.val (cutoff+n) v)
      by_contra hn
      have hp : 0 < pointedProfile M f P.val cutoff n v := lt_of_not_ge hn
      apply hi.2 n
      exact Or.inr ⟨v, by rwa [framedCartan_symm], hp⟩
    rwa [relative_profile_exterior M f P cutoff n v hvY, he] at hz

/-- The entire invisible factor fixes the family, even below the cutoff.
This is the additional step after Proposition 6.9 in the proof of Theorem 8.2. -/
theorem relative_invisible_factor_fixes {Y : Set S} {x : Artin M}
    (hf : f ∉ Y) (hx : x ∈ artinParabolic M {f}ᶜ)
    (P : RelativeVertex M Y x) (cutoff : ℤ) (hcut : ExteriorCutoff M f Y x cutoff)
    (hfull : relativeContainingType M f cutoff Y P.val = Y)
    (g : Artin M) (hg : g ∈ artinParabolic M (relativeInvisible M f cutoff Y P.val)) :
    pointedFamily M f (g*x) = pointedFamily M f x := by
  let K := relativeInvisible M f cutoff Y P.val
  have hKf : f ∉ K := fun h => hf h.1
  have hbound := relative_invisible_boundary_zero M f P cutoff hcut hfull
  have hint := pointed_boundary_zero_interior_zero M f x hx K hKf hbound
  apply pointed_standard_fixes_of_closed_zero M f x K _ g hg
  intro k v hv
  rcases hv with hv | hn
  · obtain ⟨i, hi, rfl⟩ := hv
    exact hint k i hi
  · by_cases hvK : v ∈ Sum.inl '' K
    · obtain ⟨i, hi, rfl⟩ := hvK
      exact hint k i hi
    · exact hbound k v hvK hn

/-- The nonspherical case is reduced to a proper containing type or to a
proper spherical visible factor; no new containment is assumed. -/
theorem relative_nonspherical_reduction {Y : Set S} {x : Artin M}
    (hf : f ∉ Y) (hx : x ∈ artinParabolic M {f}ᶜ) (hY : ¬IsSpherical M Y) :
    ReductionAt M (pointedInitial M f) Y x := by
  obtain ⟨cutoff, _, hcut⟩ := exteriorCutoff_exists M f Y x
  let U := (Sum.inl : S → S ⊕ Unit) '' Y
  obtain ⟨P, hP⟩ := relative_minimum_exists M f U cutoff (Y := Y) (x := x)
  let D := relativeContainingType M f cutoff Y P.val
  have hDY : D ⊆ Y := relative_containing_subset M f cutoff P
  by_cases hD : D = Y
  · let T := relativeVisible M f cutoff Y P.val
    let K := relativeInvisible M f cutoff Y P.val
    have hT : T ⊆ Y := fun _ hi => P.property.1 hi.1
    have hTs : IsSpherical M T := source_spherical_mono M Set.sdiff_subset P.val.property.1
    have hTproper : T ⊂ Y := lt_of_le_of_ne hT (by intro he; exact hY (he ▸ hTs))
    have hK : K ⊆ Y := fun _ hi => hi.1
    have hc : ∀ k ∈ K, ∀ t ∈ T, M k t = 2 := by
      intro k hk t ht
      rw [M.symmetric]
      exact relativeVisible_commutes M f cutoff Y P.val P.property.1 t ht k hk
    apply ReductionAt.split T K hTproper hK
    · exact standard_factor_normalized M K T hc
    · have he := relativeStabilizer_fixed_factor M (pointedInitial M f) K T x hc
        (fun g hg => by
          have h := relative_invisible_factor_fixes M f hf hx P cutoff hcut hD g hg
          rw [← mul_smul]
          exact h)
      have hKT : K ∪ T = Y := (Set.union_comm K T).trans hD
      rwa [hKT] at he
  · apply ReductionAt.smaller D (sourceCosetRepresentative M P.val*x⁻¹)
      (lt_of_le_of_ne hDY hD)
      (P.property.2 (sourceCosetRepresentative_mem M P.val))
    intro a ha
    exact relative_minimum_stabilizer_containment M f U cutoff
      (fun i hi => ⟨i, hi, rfl⟩) (fun _ ⟨i, _, he⟩ => ⟨i, he⟩)
      (by rintro ⟨i, hi, he⟩; exact hf (Sum.inl.inj he ▸ hi)) hx P hP a ha.1 (by
        have h := ha.2
        change a • (x • pointedInitial M f) = x • pointedInitial M f at h
        rw [← mul_smul] at h
        exact h)

end HarmonicArtin.ParabolicIntersections

end OAI
