import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedFamily
import OAI.Topology.ArtinGroups.Harmonic.MultiplicitySum

namespace OAI

/-! Layer counts of the pointed categorical family, at every integer level. -/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

noncomputable def pointedMultiplicity (f : S) (x : Artin M) (k : ℤ) (v : S ⊕ Unit) : ℝ :=
  fusionFamilyMultiplicity m d hd hm (pointedFamily M f x) k v

lemma pointedMultiplicity_nonneg (f : S) (x : Artin M) (k : ℤ) (v : S ⊕ Unit) :
    0 ≤ pointedMultiplicity M f x k v := fusionFamilyMultiplicity_nonneg m d hd hm _ k v

lemma pointedFamily_word (f : S) (w : List (S × Bool)) :
    pointedFamily M f (sourceSignedWord M w) =
      fusionPacketOrbit m d hd diag (sourcePacketWord w) (.inl f) := by
  funext L
  unfold pointedFamily pointedAction
  rw [sourceArtinAction_signedWord]
  rfl

lemma pointedMultiplicity_sum (f : S) (x : Artin M) (k : ℤ) (v : S ⊕ Unit) :
    pointedMultiplicity M f x k v =
      (∑ L, fusionWeight m L * (classLevelArray Q (pointedFamily M f x L)
        ((v, fusionZeroLabel m hm), k) : ℝ)) / fusionWeight m (fusionZeroLabel m hm) := by
  unfold pointedMultiplicity fusionFamilyMultiplicity
  simp only [classTotalVector_layer_apply]

/-- Bounded count intervals contain only finitely many actual count values. -/
lemma pointedMultiplicity_values_finite (f : S) (B : ℝ) :
    {r : ℝ | r ≤ B ∧ ∃ x k v, r = pointedMultiplicity M f x k v}.Finite := by
  have hh := finite_normalized_weighted_nat_sums (fusionWeight m) (fusionWeight_pos m hm)
    (fusionWeight m (fusionZeroLabel m hm)) (fusionWeight_pos m hm _) B
  apply hh.subset
  rintro r ⟨hr, x, k, v, rfl⟩
  exact ⟨hr, ⟨fun L => classLevelArray Q (pointedFamily M f x L)
    ((v, fusionZeroLabel m hm), k), pointedMultiplicity_sum M f x k v⟩⟩

lemma pointedMultiplicity_support_finite (f : S) (x : Artin M) :
    {k : ℤ | pointedMultiplicity M f x k ≠ 0}.Finite := by
  have hh := finiteFamily_level_support Q (pointedFamily M f x)
  apply hh.subset
  intro k hk
  by_contra hn
  apply hk
  funext v
  have hz (L : FusionLabel m) : classLevelArray Q (pointedFamily M f x L)
      ((v, fusionZeroLabel m hm), k) = 0 := by
    by_contra hne
    exact hn ⟨L, _, hne⟩
  rw [pointedMultiplicity_sum]
  simp only [hz, Nat.cast_zero, MulZeroClass.mul_zero, Finset.sum_const_zero, zero_div, Pi.zero_apply]

/-- The relative family changes no count outside the operated standard subgroup. -/
lemma pointedMultiplicity_exterior (J : Set S) (g : Artin M)
    (hg : g ∈ artinParabolic M J) (f : S) (x : Artin M)
    (v : S ⊕ Unit) (hv : v ∉ Sum.inl '' J) (k : ℤ) :
    pointedMultiplicity M f (g * x) k v = pointedMultiplicity M f x k v := by
  unfold pointedMultiplicity
  have he : pointedFamily M f (g * x) =
      fun L => sourceArtinAction M g (pointedFamily M f x L) := by
    funext L
    simp only [pointedFamily, pointedAction, map_mul, Equiv.Perm.mul_apply]
  rw [he]
  exact sourceArtinAction_multiplicity_exterior M J g hg _ v hv k

/-- A frame color outside the operated type retains its unique level-zero count. -/
lemma pointedMultiplicity_frame (J : Set S) (f : S) (hf : f ∉ J)
    (x : Artin M) (hx : x ∈ artinParabolic M J) (k : ℤ) :
    pointedMultiplicity M f x k (.inl f) = if k = 0 then 1 else 0 := by
  obtain ⟨w, hw, rfl⟩ := artinParabolic_signed_word M J x hx
  have hav : ∀ a ∈ sourcePacketWord w, a.1 ≠ (.inl f : S ⊕ Unit) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    intro he
    exact hf (Sum.inl.inj he ▸ hw b hb)
  unfold pointedMultiplicity
  rw [pointedFamily_word]
  unfold fusionFamilyMultiplicity
  simp_rw [classTotalVector_layer_apply,
    fusionOrbit_frame_level m d hd diag _ _ _ _ _ hav]
  by_cases hk : k = 0
  · subst k
    simp only [and_true, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, _root_.mul_one,
      MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact div_self (ne_of_gt (fusionWeight_pos m hm _))
  · simp only [hk, and_false, ite_false, Nat.cast_zero, MulZeroClass.mul_zero, Finset.sum_const_zero,
      zero_div]

end HarmonicArtin.ParabolicIntersections

end OAI
