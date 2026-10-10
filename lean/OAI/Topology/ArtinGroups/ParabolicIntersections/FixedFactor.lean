import OAI.Topology.ArtinGroups.ParabolicIntersections.StabilizerDescent
import OAI.Topology.ArtinGroups.Coxeter.ParabolicProductMap

namespace OAI

/-!
# Removing an invisible factor

The nonspherical branch of §8 of paper 082-03 splits off a standard
factor fixing the entire family. This module proves that step for the
actual subgroup lattice and group action. Pairwise label 2 is the precise
commutation hypothesis; no product decomposition is assumed.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {G V : Type*} [Group G] [MulAction G V]

/-- A subgroup centralized pointwise by an element is invariant under its
conjugation. -/
theorem conjugate_eq_of_commute (P : Subgroup G) (g : G)
    (hc : ∀ a ∈ P, Commute a g) : conjugate g P = P := by
  apply le_antisymm
  · intro a ha
    rw [mem_conjugate] at ha
    have hh := (hc (g⁻¹ * a * g) ha).eq
    have he : g⁻¹ * a * g = a := by
      calc
        g⁻¹ * a * g = (g⁻¹ * a * g) * g * g⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hh]
        _ = a := by group
    rwa [he] at ha
  · intro a ha
    rw [mem_conjugate]
    have he : g⁻¹ * a * g = a := by
      calc
        g⁻¹ * a * g = g⁻¹ * (a * g) := by group
        _ = g⁻¹ * (g * a) := by rw [(hc a ha).eq]
        _ = a := by group
    rwa [he]

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
  {W : Type*} [MulAction (Artin M) W] (v : W)

omit [Fintype S] [LinearOrder S] in
/-- A fixed commuting standard factor splits off from the simultaneous
stabilizer. Surjectivity of the multiplication map suffices. -/
theorem relativeStabilizer_fixed_factor (K T : Set S) (x : Artin M)
    (hc : ∀ k ∈ K, ∀ t ∈ T, M k t = 2)
    (hfix : ∀ k ∈ artinParabolic M K, k • (x • v) = x • v) :
    relativeStabilizer M v (K ∪ T) x =
      artinParabolic M K ⊔ relativeStabilizer M v T x := by
  apply le_antisymm
  · intro a ha
    have hr : a ∈ (sourceParabolicProductMap M K T hc).range := by
      rw [sourceParabolicProductMap_range]
      exact ha.1
    obtain ⟨⟨k, t⟩, he⟩ := hr
    change (k : Artin M) * t = a at he
    have ht : (t : Artin M) • (x • v) = x • v := by
      apply (smul_left_cancel_iff (k : Artin M)).mp
      rw [hfix k k.property, ← mul_smul, he]
      exact ha.2
    rw [← he]
    exact Subgroup.mul_mem _
      ((show artinParabolic M K ≤ _ from le_sup_left) k.property)
      ((show relativeStabilizer M v T x ≤ _ from le_sup_right) ⟨t.property, ht⟩)
  · apply sup_le
    · intro k hk
      exact ⟨standard_mono M Set.subset_union_left hk, hfix k hk⟩
    · exact inf_le_inf (standard_mono M Set.subset_union_right) le_rfl

omit [Fintype S] [LinearOrder S] in
/-- The fixed factor is normalized by the complementary standard factor,
as required by the rank induction. -/
theorem standard_factor_normalized (K T : Set S)
    (hc : ∀ k ∈ K, ∀ t ∈ T, M k t = 2)
    (t : Artin M) (ht : t ∈ artinParabolic M T) :
    conjugate t (artinParabolic M K) = artinParabolic M K :=
  conjugate_eq_of_commute _ t (fun k hk => sourceParabolics_commute M K T hc k t hk ht)

end HarmonicArtin.ParabolicIntersections

end OAI
