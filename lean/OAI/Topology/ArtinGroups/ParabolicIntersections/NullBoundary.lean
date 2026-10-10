import OAI.Topology.ArtinGroups.Harmonic.Stage

namespace OAI

/-!
# The boundary form of the relative null-layer obstruction

The old universal-frame argument used a boundary generator in degree zero
and therefore applied only above zero. In §5 of paper 082-03 the relative
frame can instead be joined to the isolated layer through a boundary
color at any lower integer degree. This is the saturation contradiction
at that degree. Establishing the occupied boundary for a relative family
is a separate support argument, not a published hypothesis.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] {M : CoxeterMatrix S}

/-- Saturation kills every exterior boundary count below the isolated
layer. Thus a boundary count preserved throughout the permitted orbit
prevents the isolated null-layer configuration, at any integer height. -/
theorem null_boundary_contradiction (D : IsolatedIterationData M)
    (k : ℤ) (hk : k < D.q) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' D.I)
    (hinc : ∃ u ∈ Sum.inl '' D.I,
      fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) v u < 0)
    (hoccupied : ∀ z, D.valid z →
      0 < fusionOrbitMultiplicity (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
        (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) z D.s k v)
    (z : List ((S ⊕ Unit) × Bool)) (hz : D.valid z) (hc : D.capped z) : False := by
  obtain ⟨b, hb⟩ := finiteFamily_lowerBound
    (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M))
    (fusionPacketOrbit (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) z D.s)
  obtain ⟨z', hz', hc', _, hs⟩ := D.saturate z hz hc b k hk hb
  have hzero := (D.separation z' hz' hc' k hs).1 v hv hinc
  have hpositive := hoccupied z' hz'
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

end HarmonicArtin.ParabolicIntersections

end OAI
