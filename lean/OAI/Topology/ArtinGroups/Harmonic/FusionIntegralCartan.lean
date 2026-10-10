import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SphericalFoldedMatrix
import OAI.Topology.ArtinGroups.Harmonic.IntegralRowReflect

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ)

noncomputable def fusionIntegralCartan (d:V → V → FusionEdge E) :
    Matrix (V × FusionLabel m) (V × FusionLabel m) ℤ :=
  Matrix.diagonal (fun _=>2)-Matrix.of (fun (α β:V × FusionLabel m)=>((d α.1 β.1).multiplicity m α.2 β.2:ℤ))

omit [Fintype V] in
lemma fusionIntegralCartan_cast (d:V → V → FusionEdge E) :
    (fusionIntegralCartan m d).map (Int.cast:ℤ → ℝ)=fusionUnfoldedCartan m d := by
  ext α β
  simp [fusionIntegralCartan,fusionUnfoldedCartan,Matrix.diagonal_apply]

omit [Fintype V] in
lemma fusionIntegralCartan_symm (d:V → V → FusionEdge E) (hd:∀i j,d i j=d j i)
    (α β:V × FusionLabel m) : fusionIntegralCartan m d α β=fusionIntegralCartan m d β α := by
  have h:=fusionUnfoldedCartan_symm m d hd α β
  rw [← fusionIntegralCartan_cast] at h
  simp only [Matrix.map_apply] at h
  exact_mod_cast h

omit [Fintype V] in
lemma fusionIntegralCartan_diag (d:V → V → FusionEdge E) (hd:∀i,d i i=.units 0)
    (α:V × FusionLabel m) : fusionIntegralCartan m d α α=2 := by
  simp [fusionIntegralCartan,hd,FusionEdge.multiplicity]

omit [Fintype V] in
lemma fusionIntegralCartan_off (d:V → V → FusionEdge E) (α β:V × FusionLabel m)
    (h:α≠β) : fusionIntegralCartan m d α β≤0 := by
  simp [fusionIntegralCartan,h]

variable {S:Type*} [Fintype S] [LinearOrder S]

theorem spherical_unfolded_root_sign (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J)
    (w:List (J × FusionLabel (fusionLabelSize M))) (α:J × FusionLabel (fusionLabelSize M)) :
    (∀ β,0 ≤ rowReflectWord (fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))) w (Pi.single α 1) β) ∨
    (∀ β,rowReflectWord (fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))) w (Pi.single α 1) β≤0) := by
  let d:J → J → FusionEdge (FiniteFusionEdge M):=fun i j=>coxeterFusionEdge M (.inl i) (.inl j)
  let C:=fusionIntegralCartan (fusionLabelSize M) d
  have hs:∀ α β,C α β=C β α :=fusionIntegralCartan_symm _ d
    (fun i j=>coxeterFusionEdge_symm M (.inl i) (.inl j))
  have hd:∀ α,C α α=2:=fusionIntegralCartan_diag _ d
    (fun i=>coxeterFusionEdge_diag M (.inl i))
  have ho:∀ α β,α≠β → C α β≤0:=fusionIntegralCartan_off _ d
  have hp:(C.map (Int.cast:ℤ → ℝ)).PosDef := by
    rw [fusionIntegralCartan_cast]
    exact spherical_unfolded_posDef M J hJ
  have he:=integralReflectWord_cast C w (Pi.single α 1)
  rw [fusionIntegralCartan_cast] at he
  have hc:(fun j:J × FusionLabel (fusionLabelSize M)=>
      (((Pi.single α (1:ℤ)):J × FusionLabel (fusionLabelSize M) → ℤ) j:ℝ))=
      (Pi.single α (1:ℝ):J × FusionLabel (fusionLabelSize M) → ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hc] at he
  rcases integralReflectWord_sign C hs hd ho hp w α with h|h
  · left
    intro β
    have heβ:=congrFun he β
    rw [← heβ]
    exact_mod_cast h β
  · right
    intro β
    have heβ:=congrFun he β
    rw [← heβ]
    exact_mod_cast h β

end HarmonicArtin

end OAI
