import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalNoChain
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedBoundaryZero
import OAI.Topology.ArtinGroups.Harmonic.ArtinActionWordArtin

namespace OAI

/-! The bounded-positive-height obstruction for the actual pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

/-- Every member is the transport of one indecomposable projective. -/
lemma pointed_endomorphism_dimension_le_one (z : Artin M)
    (hz : z ∈ artinParabolic M {f}ᶜ) (L : PointedLabel M) :
    classHomDimension Q 0 0 (pointedFamily M f z L) (pointedFamily M f z L) ≤ 1 := by
  obtain ⟨u, _, rfl⟩ := artinParabolic_signed_word M {f}ᶜ z hz
  rw [pointedFamily_word]
  rw [fusionOrbit_homDimension m d hd diag]
  exact initial_homDimension_le_one Q (fusionQuiver_no_loops m d hd diag) (.inl f,L) 0 0

/-- An unoperated frame supplies a nonzero exterior generator in each
member, including when its cochain position is not explicitly chosen. -/
lemma pointed_exterior_generator (Y : Set S) (hf : f ∉ Y) (z : Artin M)
    (hz : z ∈ artinParabolic M {f}ᶜ) (L : PointedLabel M) :
    ∃ p : GeneratorPlacement (FusionVertex (V := S⊕Unit) m),
      p.color ∉ fusionColorRegion m (Sum.inl '' Y) ∧
        0 < classGeneratorArray Q (pointedFamily M f z L) p := by
  obtain ⟨u, hu, rfl⟩ := artinParabolic_signed_word M {f}ᶜ z hz
  rw [pointedFamily_word]
  obtain ⟨j, hj, _⟩ := orbit_frame_generator m d hd diag (sourcePacketWord u) (.inl f)
    (by
      intro a ha he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hu b hb (Sum.inl.inj he)) L
  refine ⟨(fusionOrbitModel m d hd diag (sourcePacketWord u) (.inl f) L).complex.placement j,
    ?_, (generatorArray_positive_iff Q _ _).mpr ⟨j, rfl⟩⟩
  change ((fusionOrbitModel m d hd diag (sourcePacketWord u) (.inl f) L).complex.placement j).color.1
    ∉ Sum.inl '' Y
  rw [congrArg Prod.fst hj]
  rintro ⟨s, hs, he⟩
  exact hf (Sum.inl.inj he ▸ hs)

/-- Proposition 7.4, with the actual Artin action and complete passes
through the original colors. The mesh hypothesis is the abstract
published finite-Dynkin path input; no categorical obstruction is assumed. -/
theorem pointed_no_bounded_complete_positive_chain (Y : Set S) (hf : f ∉ Y)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (z : ℕ → Artin M) (u : ℕ → List S)
    (hz : z 0 ∈ artinParabolic M {f}ᶜ)
    (hstep : ∀ n, z (n+1) = wordArtin M (u n) * z n)
    (hu : ∀ n s, s ∈ u n ↔ s ∈ Y)
    (L : PointedLabel M)
    (hnonzero : ¬ ∀ α ∈ fusionColorRegion m (Sum.inl '' Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f (z 0) L))
    (t : ℤ) (ht : ∀ n, ClassTestUpper Q (pointedFamily M f (z n) L)
      (fusionColorRegion m (Sum.inl '' Y)) t) : False := by
  apply no_bounded_complete_positive_chain Q (fusionQuiver_no_loops m d hd diag)
    (fusionColorRegion m (Sum.inl '' Y)) hmesh
    (fun n => pointedFamily M f (z n) L)
    (fun n => fusionExpandedWord m ((u n).map (Sum.inl : S → S⊕Unit)))
  · intro n
    rw [hstep n]
    change pointedAction M (wordArtin M (u n)*z n) (pointedInitial M f L) = _
    rw [map_mul, Equiv.Perm.mul_apply]
    exact sourceArtinAction_positiveWord M (u n) _
  · intro n α
    simp only [fusionExpandedWord, List.mem_flatMap, List.mem_map,
      Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨s, hs, rfl⟩, H, rfl⟩
      exact ⟨s, (hu n s).mp hs, rfl⟩
    · rintro ⟨s, hs, he⟩
      refine ⟨.inl s, ⟨s, (hu n s).mpr hs, rfl⟩, α.2, ?_⟩
      exact Prod.ext he rfl
  · exact pointed_endomorphism_dimension_le_one M f (z 0) hz L
  · exact pointed_exterior_generator M f Y hf (z 0) hz L
  · exact hnonzero
  · exact ht

end HarmonicArtin.ParabolicIntersections

end OAI
