import OAI.Topology.ArtinGroups.Complexes.BlockClosed
import OAI.Topology.ArtinGroups.Complexes.HomDetector
import OAI.Topology.ArtinGroups.Complexes.DiagonalVertex
import OAI.Topology.ArtinGroups.Complexes.ColorBoundary
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitModel

namespace OAI

/-!
# Connected support of transported indecomposable projectives

This proves the support-cut form of the connectedness assertion in
Proposition 2.7 of paper 082-03. The input is the dimension of the actual
endomorphism cohomology, rather than an assumed connectedness property.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type*} [Fintype I] [DecidableEq I]

private noncomputable def blockProjector (E : BasedComplex Q (K := K) I) (T : Set I)
    (hT : BlockClosed Q E T) : Map Q E E :=
  (blockProjectionMap Q E T hT).comp Q (blockInclusionMap Q E T hT)

omit [Fintype V] [DecidableEq A] in
private theorem blockProjector_diagonal (E : BasedComplex Q (K := K) I)
    (T : Set I) (hT : BlockClosed Q E T) (i : I) :
    diagonalVertex Q E i (blockProjector Q E T hT).matrix = if i ∈ T then 1 else 0 := by
  change ((blockProjection Q E T * blockInclusion Q E T) i i).vertex _ = _
  by_cases hi : i ∈ T
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, hi⟩ : T)]
    · simp [blockProjection, blockInclusion, projectiveIdentity, hi, vertexId_mul_self]
    · intro j _ hji
      have hne : i ≠ (j : I) := fun he => hji (Subtype.ext he.symm)
      simp [blockProjection, projectiveIdentity, hne]
    · simp
  · have hz : (blockProjection Q E T * blockInclusion Q E T) i i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hne : i ≠ (j : I) := fun he => hi (he.symm ▸ j.property)
      simp [blockProjection, projectiveIdentity, hne]
    simp [hz, hi]

omit [DecidableEq A] in
/-- A minimal complex with at most one-dimensional degree-zero
endomorphism cohomology cannot have two nonempty differential blocks. -/
theorem no_proper_block (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (hd : homDimension Q E E 0 0 ≤ 1) (T : Set I) (hT : BlockClosed Q E T)
    (i j : I) (hi : i ∈ T) (hj : j ∉ T) : False := by
  have hf := map_mem_homCycles Q (blockProjector Q E T hT)
  have hb := boundary_of_homDimension_le_one Q E E 0 0 hd
    (diagonalVertex Q E j) (fun _ h => diagonalVertex_boundary Q E hE j 0 0 h)
    (identity_mem_homCycles Q E) (by rw [diagonalVertex_identity]; exact one_ne_zero)
    hf (by rw [blockProjector_diagonal]; simp [hj])
  have hz := diagonalVertex_boundary Q E hE i 0 0 hb
  have he : diagonalVertex Q E i (blockProjector Q E T hT).matrix = 1 := by
    rw [blockProjector_diagonal]
    simp only [hi, ↓reduceIte]
  rw [he] at hz
  exact one_ne_zero hz

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
/-- Nonzero minimal differential entries either stay at one color or
follow an arrow of the quiver. This includes the token entries between
successive layers. -/
theorem differential_same_or_arrow (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i j : I) (hn : E.differential i j ≠ 0) :
    (E.placement i).color = (E.placement j).color ∨
      ∃ a : A, Q.source a = (E.placement i).color ∧
        Q.target a = (E.placement j).color := by
  by_cases hc : (E.placement i).color = (E.placement j).color
  · exact Or.inl hc
  right
  by_contra ha
  push Not at ha
  apply hn
  apply ReversibleQuiver.Zigzag.ext
  · exact hE i j
  · funext a
    by_contra hnz
    have hh := coordinates_corner Q (E.entries.1 i j) (E.entries.2 i j)
      (p := .inr (.inl a)) hnz
    exact ha a hh.1 hh.2
  · funext v
    by_contra hnz
    have hh := coordinates_corner Q (E.entries.1 i j) (E.entries.2 i j)
      (p := .inr (.inr v)) hnz
    exact hc (hh.1.symm.trans hh.2)

omit [DecidableEq A] in
/-- If the support meets both a color set and its complement, it must
meet the exterior boundary of that set. This is the exact support fact
needed to find a boundary level below an isolated null layer. -/
theorem support_meets_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (hd : homDimension Q E E 0 0 ≤ 1) (U : Set V)
    (i j : I) (hi : (E.placement i).color ∈ U) (hj : (E.placement j).color ∉ U) :
    ∃ k : I, (E.placement k).color ∈ colorBoundary Q U := by
  by_contra hb
  push Not at hb
  apply no_proper_block Q E hE hd {k | (E.placement k).color ∈ U} _ i j hi hj
  intro a b hn
  rcases differential_same_or_arrow Q E hE a b hn with he | ⟨c, hs, ht⟩
  · change (E.placement a).color ∈ U ↔ (E.placement b).color ∈ U
    rw [he]
  · constructor
    · intro ha
      by_contra hnb
      exact hb b ⟨hnb, c, hs ▸ ha, ht⟩
    · intro hbb
      change (E.placement b).color ∈ U at hbb
      by_contra hna
      exact hb a ⟨hna, Q.reverse c,
        by simpa only [Q.source_reverse, ht] using hbb,
        by simpa only [Q.target_reverse] using hs⟩

section Fusion

variable {E W : Type} [Fintype E] [DecidableEq E] [Fintype W] [DecidableEq W]
  (m : E → ℕ) (d : W → W → FusionEdge E) (hd : ∀ s t, d s t = d t s)
  (hdiag : ∀ s, d s s = .units 0)

/-- The preceding support statement applies unconditionally to the
minimal representative of every transported projective in the fusion
packet action. -/
theorem fusionOrbit_support_meets_boundary (w : List (W × Bool)) (s : W)
    (L : FusionLabel m) (U : Set (FusionVertex (V := W) m))
    (i j : (fusionOrbitModel m d hd hdiag w s L).Index)
    (hi : ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).color ∈ U)
    (hj : ((fusionOrbitModel m d hd hdiag w s L).complex.placement j).color ∉ U) :
    ∃ k : (fusionOrbitModel m d hd hdiag w s L).Index,
      ((fusionOrbitModel m d hd hdiag w s L).complex.placement k).color ∈
        colorBoundary (fusionQuiver m d hd) U := by
  apply support_meets_boundary (fusionQuiver m d hd) _
    (fusionOrbitModel_minimal m d hd hdiag w s L) _ U i j hi hj
  change homDimension (fusionQuiver m d hd)
    (minimalClassModel (fusionQuiver m d hd) (fusionPacketOrbit m d hd hdiag w s L)).complex
    (minimalClassModel (fusionQuiver m d hd) (fusionPacketOrbit m d hd hdiag w s L)).complex
    0 0 ≤ 1
  rw [minimalClassModel_homDimension, fusionOrbit_homDimension]
  exact initial_homDimension_le_one (fusionQuiver m d hd)
    (fusionQuiver_no_loops m d hd hdiag) (s, L) 0 0

end Fusion

end HarmonicArtin.ParabolicIntersections

end OAI
