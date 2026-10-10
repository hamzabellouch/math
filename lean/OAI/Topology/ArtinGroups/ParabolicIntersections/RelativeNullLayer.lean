import OAI.Topology.ArtinGroups.ParabolicIntersections.BoundaryWitness
import OAI.Topology.ArtinGroups.ParabolicIntersections.NullBoundary
import OAI.Topology.ArtinGroups.Harmonic.CosetOrbitCap

namespace OAI

/-!
# The relative null-layer obstruction at every integer level

This is the version of Proposition 5.1 of paper 082-03 needed for a
relative frame. It uses connected support, cap accessibility and finite
spherical socle saturation. It does not require the frame to be adjacent
to every operated color, or the isolated level to be positive.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd diag
local notation "μ" => fusionOrbitMultiplicity m d hd diag hm
local notation "C" => fusionFoldedCartan m d
local notation "aw" => sourceArtinAction M (K := ℂ)

/-- Relative null-layer obstruction, with no restriction on the sign of
`q`. All the inputs concern concrete layer counts and spherical caps. -/
theorem relative_null_layer (I J : Set S) (hI : I.Nonempty)
    (hJI : J ⊆ I) (hJ : IsSpherical M J)
    (z₀ : List ((S ⊕ Unit) × Bool)) (s : S ⊕ Unit)
    (hs : s ∉ Sum.inl '' I) (hw : ∀ a ∈ z₀, a.1 ≠ s) (q : ℤ)
    (c : S ⊕ Unit → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hcSupp : ∀ v, v ∉ Sum.inl '' I → c v = 0)
    (hcPos : ∀ v, v ∈ Sum.inl '' I → 0 < c v)
    (hcNull : ∀ v, v ∈ Sum.inl '' I → (C *ᵥ c) v = 0)
    (hE : ∀ L, ClassCapOn Q (O z₀ s L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' J)) q)
    (hdata : ∀ v, (v ∈ Sum.inl '' I ∧ v ∉ Sum.inl '' J) ∨
      (v ∉ Sum.inl '' I ∧ ∃ u ∈ Sum.inl '' I, C v u < 0) → μ z₀ s q v = c v)
    (huniv : ∀ g ∈ artinParabolic M J,
      (∀ L, ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q) →
      ∀ j : J, c (.inl (j : S)) < fusionFamilyMultiplicity m d hd hm
        (fun L => aw g (O z₀ s L)) q (.inl (j : S))) : False := by
  have hstrict : ∀ g ∈ artinParabolic M J,
      (∀ L, ClassCapOn Q (aw g (O z₀ s L))
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) →
      ∀ j : J, c (.inl (j : S)) < fusionFamilyMultiplicity m d hd hm
        (fun L => aw g (O z₀ s L)) q (.inl (j : S)) := by
    intro g hg hcap
    apply huniv g hg
    intro L
    apply source_cap_closed_of_cap_parts M I J hJI _ q (hcap L)
    exact sourceArtinAction_cap_exterior M J g hg (O z₀ s L) _
      (fun _ h => h.2) q (hE L)
  let D := isolatedDataOfCoset M I J hJI hJ z₀ s q c hc hcSupp hcPos hcNull hdata hstrict
  obtain ⟨zcap, hzcap, hcap⟩ := sourceCosetOrbit_exists_cap M I J hJI hJ z₀ s q hE
  obtain ⟨g, hg, hge⟩ := hzcap
  obtain ⟨w, hwt, hwe⟩ := artinParabolic_signed_word M J g hg
  let z := sourcePacketWord w ++ z₀
  have he (L : FusionLabel m) : O z s L = O zcap s L := by
    rw [hge L, ← hwe]
    exact sourcePacketOrbit_signedPrepend M w z₀ s L
  have hz : D.valid z := by
    refine ⟨g, hg, fun L => ?_⟩
    exact (he L).trans (hge L)
  have hcz' (L : FusionLabel m) : ClassCapOn Q (O z s L)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q := by
    rw [he L]
    exact hcap L
  have hcz : D.capped z := hcz' 
  have hwz : ∀ a ∈ z, a.1 ≠ s := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      intro heq
      exact hs ⟨b.1, hJI (hwt b hb), heq⟩
    · exact hw a ha
  obtain ⟨i, hi⟩ := hI
  have hipos : 0 < μ z s q (.inl i) := by
    have hci := hcPos (.inl i) ⟨i, hi, rfl⟩
    by_cases hij : i ∈ J
    · have h := D.strict z hz 1 (artinParabolic M J).one_mem
        (by intro L; simpa only [map_one, Equiv.Perm.one_apply] using D.capJ z hcz L) ⟨i, hij⟩
      simp only [map_one, Equiv.Perm.one_apply, fusionFamilyMultiplicity_orbit] at h
      exact lt_trans hci h
    · have hiq := D.data z hz (.inl i) (Or.inl ⟨⟨i, hi, rfl⟩, by
        rintro ⟨j, hj, hej⟩; exact hij (Sum.inl.inj hej ▸ hj)⟩)
      change μ z s q (.inl i) = c (.inl i) at hiq
      rw [hiq]
      exact hci
  obtain ⟨L, b, hb, _⟩ := orbit_generator_of_positive m d hd diag hm z s (.inl i) q hipos
  have hbin : ((fusionOrbitModel m d hd diag z s L).complex.placement b).color.1 ∈
      Sum.inl '' I := hb.symm ▸ ⟨i, hi, rfl⟩
  obtain ⟨k, v, hk, hv, hinc, hp⟩ := orbit_boundary_below m d hd diag hm z s hwz
    (Sum.inl '' I) hs q L b hbin
    (fun H => ClassCapOn.mono Q (hcz' H) (by
      rintro α ⟨_, a, ha, ht⟩
      exact Or.inr ⟨(Q).source a, ha, a, rfl, ht⟩))
    (by
      intro v hv hinc
      have hh := D.data z hz v (Or.inr ⟨hv, hinc⟩)
      change μ z s q v = c v at hh
      exact hh.trans (hcSupp v hv))
  have hvJ : v ∉ Sum.inl '' J := fun h => hv (Set.image_mono hJI h)
  apply null_boundary_contradiction D k hk v hv hinc _ z hz hcz
  intro z' hz'
  have heq : μ z' s k v = μ z s k v := by
    rw [sourceCosetOrbit_multiplicity_exterior M J z₀ s z' hz' v hvJ k,
      sourceCosetOrbit_multiplicity_exterior M J z₀ s z hz v hvJ k]
  change 0 < μ z' s k v
  rw [heq]
  exact hp

end HarmonicArtin.ParabolicIntersections

end OAI
