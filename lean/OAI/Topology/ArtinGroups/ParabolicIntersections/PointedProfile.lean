import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedMultiplicity
import OAI.Topology.ArtinGroups.Harmonic.CosetSum

namespace OAI

/-! Harmonic profiles on actual parabolic cosets for a relative frame. -/

namespace HarmonicArtin.ParabolicIntersections

open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)

noncomputable def pointedHarmonicAt (T : Set S) (x : Artin M) (k : ℤ) : S ⊕ Unit → ℝ :=
  harmonicExtension (framedCartan M) (Sum.inl '' T) (pointedMultiplicity M f x k)

lemma pointedHarmonicAt_outside (T : Set S) (x : Artin M) (k : ℤ) (i : S ⊕ Unit)
    (hi : i ∉ Sum.inl '' T) :
    pointedHarmonicAt M f T x k i = pointedMultiplicity M f x k i :=
  harmonicExtension_outside _ _ _ hi

lemma pointedHarmonicAt_nonneg (T : Set S) (hT : IsSpherical M T) (x : Artin M) (k : ℤ) :
    ∀ i, 0 ≤ pointedHarmonicAt M f T x k i :=
  harmonicExtension_nonneg _ _ (framed_spherical_posDef M T hT)
    (framedCartan_off M) _ (pointedMultiplicity_nonneg M f x k)

lemma pointedHarmonicAt_harmonic (T : Set S) (hT : IsSpherical M T)
    (x : Artin M) (k : ℤ) (i : (Sum.inl : S → S ⊕ Unit) '' T) :
    (framedCartan M *ᵥ pointedHarmonicAt M f T x k) i = 0 :=
  harmonicExtension_harmonic _ _ (framed_spherical_posDef M T hT) _ i

lemma pointedHarmonicAt_invariant (T : Set S) (g x : Artin M)
    (hg : g ∈ artinParabolic M T) (k : ℤ) :
    pointedHarmonicAt M f T (g * x) k = pointedHarmonicAt M f T x k := by
  apply harmonicExtension_congr_exterior
  intro i hi
  exact pointedMultiplicity_exterior M T g hg f x i hi k

lemma pointedHarmonicAt_of_mem (T : Set S) (x y : Artin M)
    (hy : y ∈ rightCoset M T x) (k : ℤ) :
    pointedHarmonicAt M f T y k = pointedHarmonicAt M f T x k := by
  have hh := pointedHarmonicAt_invariant M f T (y * x⁻¹) x hy k
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

noncomputable def pointedCosetVector (P : Deligne M) (k : ℤ) : S ⊕ Unit → ℝ :=
  pointedHarmonicAt M f P.val.1 (sourceCosetRepresentative M P) k

lemma pointedCosetVector_eq (P : Deligne M) (x : Artin M) (hx : x ∈ P.val.2) (k : ℤ) :
    pointedCosetVector M f P k = pointedHarmonicAt M f P.val.1 x k := by
  rw [sourceCosetRepresentative_spec] at hx
  exact (pointedHarmonicAt_of_mem M f P.val.1 _ x hx k).symm

lemma pointedCosetVector_nonneg (P : Deligne M) (k : ℤ) :
    ∀ i, 0 ≤ pointedCosetVector M f P k i :=
  pointedHarmonicAt_nonneg M f P.val.1 P.property.1 _ k

lemma pointedCosetVector_harmonic (P : Deligne M) (k : ℤ) (i : (Sum.inl : S → S ⊕ Unit) '' P.val.1) :
    (framedCartan M *ᵥ pointedCosetVector M f P k) i = 0 :=
  pointedHarmonicAt_harmonic M f P.val.1 P.property.1 _ k i

lemma pointedCosetVector_support_finite (P : Deligne M) :
    {k : ℤ | pointedCosetVector M f P k ≠ 0}.Finite := by
  apply (pointedMultiplicity_support_finite M f (sourceCosetRepresentative M P)).subset
  intro k hk
  by_contra hn
  apply hk
  have hz : pointedMultiplicity M f (sourceCosetRepresentative M P) k = 0 := not_not.mp hn
  change harmonicExtension _ _ _ = 0
  rw [hz, harmonicExtension_zero]

noncomputable def pointedCosetSum (P : Deligne M) (k : ℤ) : ℝ :=
  ∑ i, pointedCosetVector M f P k i

lemma pointedCosetVector_le_sum (P : Deligne M) (k : ℤ) (i : S ⊕ Unit) :
    pointedCosetVector M f P k i ≤ pointedCosetSum M f P k :=
  Finset.single_le_sum (fun j _ => pointedCosetVector_nonneg M f P k j) (Finset.mem_univ i)

lemma pointedCosetVector_bounded_finite (B : ℝ) :
    {p : S ⊕ Unit → ℝ | ∃ P : Deligne M, ∃ k : ℤ,
      pointedCosetSum M f P k ≤ B ∧ p = pointedCosetVector M f P k}.Finite := by
  let A : Set ℝ := {0} ∪ {r : ℝ | r ≤ B ∧ ∃ x k v, r = pointedMultiplicity M f x k v}
  have hA : A.Finite := (Set.finite_singleton 0).union (pointedMultiplicity_values_finite M f B)
  apply (finite_harmonic_images (framedCartan M) A hA).subset
  rintro p ⟨P, k, hB, rfl⟩
  let T : Set (S ⊕ Unit) := Sum.inl '' P.val.1
  let v : S ⊕ Unit → ℝ := fun i => if i ∈ T then 0 else pointedCosetVector M f P k i
  refine ⟨T, v, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · exact Or.inl (by simp only [v, hi, ↓reduceIte, Set.mem_singleton_iff])
    · right
      dsimp only [v]
      simp only [hi, ↓reduceIte]
      refine ⟨(pointedCosetVector_le_sum M f P k i).trans hB, ?_⟩
      exact ⟨sourceCosetRepresentative M P, k, i,
        pointedHarmonicAt_outside M f P.val.1 _ k i hi⟩
  · change harmonicExtension (framedCartan M) T _ = harmonicExtension (framedCartan M) T v
    apply harmonicExtension_congr_exterior
    intro i hi
    simp only [v, hi, ↓reduceIte]
    exact (pointedHarmonicAt_outside M f P.val.1 _ k i hi).symm

/-- Shift the fixed integer cutoff to zero while retaining every recorded level. -/
noncomputable def pointedProfile (P : Deligne M) (cutoff : ℤ) : ℕ →₀ (S ⊕ Unit → ℝ) :=
  Finsupp.ofSupportFinite (fun k => pointedCosetVector M f P (cutoff + k))
    ((pointedCosetVector_support_finite M f P).preimage (by
      intro a _ b _ he
      exact Int.ofNat_inj.mp (add_left_cancel he)))

@[simp] lemma pointedProfile_apply (P : Deligne M) (cutoff : ℤ) (k : ℕ) :
    pointedProfile M f P cutoff k = pointedCosetVector M f P (cutoff + k) := rfl

end HarmonicArtin.ParabolicIntersections

end OAI
