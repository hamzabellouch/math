import OAI.Topology.ArtinGroups.ParabolicIntersections.BoundaryWitness
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedMultiplicityZero
import OAI.Topology.ArtinGroups.Complexes.EmptyTestIndex

namespace OAI

/-! The all-level connected-support argument in the nonspherical case of §8. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

section Fusion
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)
  (hdiag : ∀ s, d s s = .units 0) (hm : ∀ e, 2 ≤ m e)

/-- An unoperated exterior frame and an empty boundary exclude every
interior generator, including generators below the harmonic cutoff. -/
theorem orbit_boundary_zero_interior_zero (w : List (V × Bool)) (s : V)
    (hw : ∀ a ∈ w, a.1 ≠ s) (U : Set V) (hs : s ∉ U)
    (hz : ∀ k v, v ∉ U → (∃ u ∈ U, fusionFoldedCartan m d v u < 0) →
      fusionOrbitMultiplicity m d hd hdiag hm w s k v = 0) :
    ∀ k v, v ∈ U → fusionOrbitMultiplicity m d hd hdiag hm w s k v = 0 := by
  intro k v hv
  apply le_antisymm _ (fusionOrbitMultiplicity_nonneg m d hd hdiag hm w s k v)
  by_contra hn
  have hp : 0 < fusionOrbitMultiplicity m d hd hdiag hm w s k v := lt_of_not_ge hn
  obtain ⟨L, i, hi, _⟩ := orbit_generator_of_positive m d hd hdiag hm w s v k hp
  obtain ⟨j, hj, _⟩ := orbit_frame_generator m d hd hdiag w s hw L
  obtain ⟨b, hb⟩ := fusionOrbit_support_meets_boundary m d hd hdiag w s L
    (fusionColorRegion m U) i j (by change _ ∈ U; rwa [hi])
    (by change _ ∉ U; rw [congrArg Prod.fst hj]; exact hs)
  let q := ((fusionOrbitModel m d hd hdiag w s L).complex.placement b).level
  have he := fusionOrbit_boundary_absent m d hd hdiag hm w s q U (hz q) L ⟨b, rfl⟩
  exact he hb
end Fusion

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

/-- Connectedness of the actual pointed family converts an all-level
exterior boundary vanishing statement to interior vanishing. -/
theorem pointed_boundary_zero_interior_zero (x : Artin M)
    (hx : x ∈ artinParabolic M {f}ᶜ) (K : Set S) (hf : f ∉ K)
    (hz : ∀ k v, v ∉ Sum.inl '' K →
      (∃ u ∈ Sum.inl '' K, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0) :
    ∀ k i, i ∈ K → pointedMultiplicity M f x k (.inl i) = 0 := by
  obtain ⟨w, hw, rfl⟩ := artinParabolic_signed_word M {f}ᶜ x hx
  have hC : fusionFoldedCartan m d = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    congr 1
    exact Subsingleton.elim _ _
  have hh := orbit_boundary_zero_interior_zero m d hd diag (fusionLabelSize_ge_two M)
    (sourcePacketWord w) (.inl f)
    (by
      intro a ha he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hw b hb (Sum.inl.inj he)) (Sum.inl '' K)
    (by rintro ⟨i, hi, he⟩; exact hf (Sum.inl.inj he ▸ hi))
    (by simpa only [hC, pointedMultiplicity_word] using hz)
  intro k i hi
  simpa only [pointedMultiplicity_word] using hh k (.inl i) ⟨i, hi, rfl⟩

/-- Termwise absence in a closed neighborhood makes its negative twists
identity maps on each member of the pointed family. -/
theorem pointed_negativeTwist_of_zero (x : Artin M) (K : Set S)
    (hz : ∀ k v, v ∈ Sum.inl '' K ∨
      (∃ u ∈ Sum.inl '' K, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0)
    (i : S) (hi : i ∈ K) (L H : FusionLabel m) :
    classNegativeTwist Q (.inl i, L) (pointedFamily M f x H) = pointedFamily M f x H := by
  let E := minimalClassModel Q (pointedFamily M f x H)
  have hC : fusionFoldedCartan m d = framedCartan M := by
    convert fusionFoldedCartan_eq_framedCartan M using 1
    congr 1
    exact Subsingleton.elim _ _
  have hE : ∀ a : E.Index, (E.complex.placement a).color ∉
      closedNeighborhood Q (fusionColorRegion m (Sum.inl '' K)) := by
    intro a ha
    let v := (E.complex.placement a).color.1
    let k := (E.complex.placement a).level
    have hv : pointedMultiplicity M f x k v = 0 := by
      rcases ha with ha | ⟨β, hβ, r, hr, he⟩
      · obtain ⟨j, hj, he⟩ := ha
        have hv : v = .inl j := he.symm
        rw [hv]
        exact hz k (.inl j) (Or.inl ⟨j, hj, rfl⟩)
      · obtain ⟨j, hj, hej⟩ := hβ
        have hc := fusion_arrow_color_cartan_neg m d (fusionLabelSize_ge_two M) r
        have ht : r.1.2.1 = v := congrArg Prod.fst he
        have hs : r.1.1.1 = .inl j := (congrArg Prod.fst hr).trans hej.symm
        by_cases hne : r.1.1.1 = r.1.2.1
        · have hv : v = .inl j := ht ▸ hne ▸ hs
          rw [hv]
          exact hz k (.inl j) (Or.inl ⟨j, hj, rfl⟩)
        · have hneg := hc hne
          rw [hs, ht, hC, framedCartan_symm] at hneg
          exact hz k v (Or.inr ⟨.inl j, ⟨j, hj, rfl⟩, hneg⟩)
    have hn := (pointedMultiplicity_zero_iff M f x k v).mp hv H
      (E.complex.placement a).color.2
    rw [classLevelArray_minimal_apply] at hn
    have hp : 0 < Nat.card {b : E.Index // (E.complex.placement b).color =
        (E.complex.placement a).color ∧ (E.complex.placement b).level = k} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
      exact ⟨⟨a, rfl, rfl⟩⟩
    exact (ne_of_gt hp) hn
  have h := classNegativeTwist_far Q E.complex (fusionColorRegion m (Sum.inl '' K))
    hE (.inl i, L) ⟨i, hi, rfl⟩
  have hm : classOfComplex Q E.complex = pointedFamily M f x H :=
    minimalClassModel_class Q _
  rw [hm] at h
  exact h

/-- Vanishing on a full closed neighborhood makes the standard subgroup
fix the actual family, with no restriction on the levels. -/
theorem pointed_standard_fixes_of_closed_zero (x : Artin M) (K : Set S)
    (hz : ∀ k v, v ∈ Sum.inl '' K ∨
      (∃ u ∈ Sum.inl '' K, framedCartan M v u < 0) →
      pointedMultiplicity M f x k v = 0)
    (g : Artin M) (hg : g ∈ artinParabolic M K) :
    pointedFamily M f (g * x) = pointedFamily M f x := by
  have hpos (i : S) (hi : i ∈ K) (L H : FusionLabel m) :
      classPositiveTwist Q (.inl i, L) (pointedFamily M f x H) =
        pointedFamily M f x H := by
    let e := classTwistPerm Q (K := ℂ) (fusionQuiver_no_loops m d hd diag) (.inl i, L)
    have hn := pointed_negativeTwist_of_zero M f x K hz i hi L H
    calc
      _ = e (e.symm (pointedFamily M f x H)) := congrArg e hn.symm
      _ = _ := e.apply_symm_apply _
  have hgen (i : S) (hi : i ∈ K) (H : FusionLabel m) :
      pointedAction M (generator M i) (pointedFamily M f x H) =
        pointedFamily M f x H := by
    rw [pointedAction_generator, fusionPacketPerm, ← classPacketPerm_toList]
    have hlist (l : List (FusionLabel m)) :
        (l.map (fun L => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
          (.inl i, L))).prod (pointedFamily M f x H) = pointedFamily M f x H := by
      induction l with
      | nil => rfl
      | cons L l ih =>
        change classPositiveTwist Q (.inl i, L)
          ((l.map (fun J => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
            (.inl i, J))).prod (pointedFamily M f x H)) = _
        rw [ih]
        exact hpos i hi L H
    exact hlist _
  have hall (H : FusionLabel m) :
      pointedAction M g (pointedFamily M f x H) = pointedFamily M f x H := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      exact hgen i hi H
    | one => simp only [map_one, Equiv.Perm.one_apply]
    | mul g h hg hh ihg ihh =>
      simp only [map_mul, Equiv.Perm.mul_apply, ihh, ihg]
    | inv g hg ih =>
      rw [map_inv]
      apply (pointedAction M g).injective
      change (pointedAction M g) ((pointedAction M g).symm _) = _
      rw [Equiv.apply_symm_apply, ih]
  funext H
  change pointedAction M (g * x) (pointedInitial M f H) = _
  rw [map_mul, Equiv.Perm.mul_apply]
  exact hall H

end HarmonicArtin.ParabolicIntersections

end OAI
