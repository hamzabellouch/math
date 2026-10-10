import OAI.Topology.ArtinGroups.ParabolicIntersections.ConnectedSupport
import OAI.Topology.ArtinGroups.Harmonic.DimensionPosMultiplicityPos
import OAI.Topology.ArtinGroups.Complexes.LevelArrayMinimalApply

namespace OAI

/-!
# A boundary witness below a capped isolated layer

The relative frame need not be adjacent to the isolated set. Connected
support finds an occupied exterior boundary color. A zero boundary cap
then puts that occupation strictly below the isolated layer. This is the
additional boundary argument of §5 of paper 082-03.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)
  (hdiag : ∀ s, d s s = .units 0) (hm : ∀ e, 2 ≤ m e)

local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

/-- The unchanged initial frame occurs in every minimal representative,
with its original label and level. -/
theorem orbit_frame_generator (w : List (V × Bool)) (s : V)
    (hw : ∀ a ∈ w, a.1 ≠ s) (L : FusionLabel m) :
    ∃ j : (fusionOrbitModel m d hd hdiag w s L).Index,
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).color = (s, L) ∧
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).level = 0 := by
  have hc := fusionOrbit_frame_level m d hd hdiag w s L L 0 hw
  rw [classLevelArray_minimal_apply] at hc
  simp only [and_self, ite_true] at hc
  have hp : 0 < Nat.card {i : (minimalClassModel Q (O w s L)).Index //
      ((minimalClassModel Q (O w s L)).complex.placement i).color = (s, L) ∧
      ((minimalClassModel Q (O w s L)).complex.placement i).level = 0} := by
    rw [hc]
    exact Nat.zero_lt_one
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hp
  obtain ⟨j⟩ := hp
  exact ⟨j.val, j.property⟩

/-- A positive folded count is witnessed by an actual generator in one
member of the family, at the specified color and level. -/
theorem orbit_generator_of_positive (w : List (V × Bool)) (s v : V) (q : ℤ)
    (hp : 0 < μ w s q v) :
    ∃ L : FusionLabel m, ∃ i : (fusionOrbitModel m d hd hdiag w s L).Index,
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).color.1 = v ∧
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).level = q := by
  let H : FusionLabel m := fun e => ⟨0, by have := hm e; omega⟩
  have hweighted : 0 < fusionOrbitWeightedVector m d hd hdiag w s q (v, H) := by
    rw [fusionOrbitWeightedVector_eq m d hd hdiag hm]
    exact mul_pos (fusionWeight_pos m hm H) hp
  have hsum : 0 < ∑ L, fusionWeight m L * generatorVector Q (Y w s L q) (v, H) := by
    simpa only [fusionOrbitWeightedVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hweighted
  have hex : ∃ L, 0 < fusionWeight m L * generatorVector Q (Y w s L q) (v, H) := by
    by_contra hn
    push Not at hn
    exact (not_lt_of_ge (Finset.sum_nonpos (fun L _ => hn L))) hsum
  obtain ⟨L, hL⟩ := hex
  have hg : 0 < generatorVector Q (Y w s L q) (v, H) :=
    (mul_pos_iff_of_pos_left (fusionWeight_pos m hm L)).mp hL
  change 0 < (Nat.card {i : FusionOrbitLayerIndex m d hd hdiag w s L q //
    ((Y w s L q).placement i).color = (v, H)} : ℝ) at hg
  have hcard : 0 < Nat.card {i : FusionOrbitLayerIndex m d hd hdiag w s L q //
      ((Y w s L q).placement i).color = (v, H)} := by exact_mod_cast hg
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hcard
  obtain ⟨i⟩ := hcard
  exact ⟨L, i.val.val, congrArg Prod.fst i.property, i.val.property⟩

/-- An occupied generator in `U` and an unoperated frame outside `U`
force an occupied boundary below `q`, if every boundary count at `q`
and above is zero. No condition `0 < q` is used. -/
theorem orbit_boundary_below (w : List (V × Bool)) (s : V)
    (hw : ∀ a ∈ w, a.1 ≠ s) (U : Set V) (hs : s ∉ U) (q : ℤ)
    (L : FusionLabel m) (i : (fusionOrbitModel m d hd hdiag w s L).Index)
    (hi : ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).color.1 ∈ U)
    (hcap : ∀ H, ClassCapOn Q (O w s H)
      (colorBoundary Q (fusionColorRegion m U)) q)
    (hzero : ∀ v, v ∉ U → (∃ u ∈ U, C v u < 0) → μ w s q v = 0) :
    ∃ k v, k < q ∧ v ∉ U ∧ (∃ u ∈ U, C v u < 0) ∧ 0 < μ w s k v := by
  obtain ⟨j, hj, _⟩ := orbit_frame_generator m d hd hdiag w s hw L
  have hjs : ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).color.1 = s :=
    congrArg Prod.fst hj
  obtain ⟨b, hb⟩ := fusionOrbit_support_meets_boundary m d hd hdiag w s L
    (fusionColorRegion m U) i j hi (by change _ ∉ U; rwa [hjs])
  have hbound := hcap L b hb
  obtain ⟨hbout, a, ha, he⟩ := hb
  let k := ((fusionOrbitModel m d hd hdiag w s L).complex.placement b).level
  let v := ((fusionOrbitModel m d hd hdiag w s L).complex.placement b).color.1
  have hv : v ∉ U := hbout
  have hau : a.1.1.1 ∈ U := ha
  have hev : a.1.2.1 = v := congrArg Prod.fst he
  have hne : a.1.1.1 ≠ a.1.2.1 := by
    intro h
    exact hv (hev ▸ h ▸ hau)
  have hneg := fusion_arrow_color_cartan_neg m d hm a hne
  rw [fusionFoldedCartan_symm m d hd, hev] at hneg
  have hinc : ∃ u ∈ U, C v u < 0 := ⟨a.1.1.1, hau, hneg⟩
  have hpos : 0 < μ w s k v :=
    fusionOrbitMultiplicity_pos_at_generator m d hd hdiag hm w s k L ⟨b, rfl⟩
  refine ⟨k, v, ?_, hv, hinc, hpos⟩
  by_contra hlt
  have hk : k = q := le_antisymm hbound (le_of_not_gt hlt)
  rw [hk, hzero v hv hinc] at hpos
  exact lt_irrefl 0 hpos

end HarmonicArtin.ParabolicIntersections

end OAI
