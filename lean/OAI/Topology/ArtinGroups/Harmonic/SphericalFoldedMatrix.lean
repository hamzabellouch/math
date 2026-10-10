import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FiniteFusionEdge
import OAI.Topology.ArtinGroups.Geometry.CartanOffNonpos
import OAI.Topology.ArtinGroups.Geometry.SphericalCartanPos

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S]

omit [Fintype S] in
lemma spherical_folded_matrix (M:CoxeterMatrix S) (J:Set S) :
    fusionFoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))=
      (Geometric.cartan M).submatrix ((↑):J → S) ((↑):J → S) := by
  ext i j
  have h:=congrFun (congrFun (fusionFoldedCartan_eq_framedCartan M) (.inl i)) (.inl j)
  simpa [fusionFoldedCartan,Matrix.diagonal_apply,framedCartan,Geometric.cartan,
    Subtype.ext_iff] using h

theorem spherical_unfolded_posDef (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J) :
    (fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))).PosDef := by
  apply fusion_positive_definite (fusionLabelSize M)
    (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
    (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))
    (fun i j=>coxeterFusionEdge_symm M (.inl i) (.inl j))
  · intro i j hij
    rw [spherical_folded_matrix]
    exact Geometric.cartan_off_nonpos M i j (fun h=>hij (Subtype.ext h))
  · rw [spherical_folded_matrix]
    exact Geometric.spherical_cartan_posDef M J hJ

omit [LinearOrder S] in
theorem spherical_no_infinite_label (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J)
    (i j:J) (hij:i≠j) : M i j≠0 := by
  intro hzero
  let C:=((Geometric.cartan M).submatrix ((↑):J → S) ((↑):J → S))
  let x:J → ℝ:=Pi.single i 1+Pi.single j 1
  have hne:x≠0 := by
    intro h
    have hi:=congrFun h i
    simp [x,hij] at hi
  have hpos:0 < x ⬝ᵥ (C *ᵥ x) := by
    simpa only [star_trivial] using (Geometric.spherical_cartan_posDef M J hJ).dotProduct_mulVec_pos hne
  have hval : (i:S)≠j := fun h=>hij (Subtype.ext h)
  have hval' : (j:S)≠i := Ne.symm hval
  have hct : x ⬝ᵥ (C *ᵥ x)=0 := by
    simp [x,C,Matrix.mulVec_add,add_dotProduct,dotProduct_add,Matrix.mulVec_single,
      Geometric.cartan,hval,hval',hzero,← M.symmetric i j]
  rw [hct] at hpos
  exact lt_irrefl _ hpos

theorem spherical_fusion_multiplicity_le_one (M:CoxeterMatrix S) (J:Set S)
    (hJ:IsSpherical M J) (i j:J) (L L':FusionLabel (fusionLabelSize M)) :
    (coxeterFusionEdge M (.inl i) (.inl j)).multiplicity (fusionLabelSize M) L L' ≤ 1 := by
  by_cases hij:i=j
  · subst j
    simp [coxeterFusionEdge_diag,FusionEdge.multiplicity]
  have hval : (i:S)≠j := fun h=>hij (Subtype.ext h)
  have hzero := spherical_no_infinite_label M J hJ i j hij
  simp only [coxeterFusionEdge,dite_eq_right hval,dite_eq_right hzero]
  split_ifs with h2 h3
  · simp [FusionEdge.multiplicity]
  · simp only [FusionEdge.multiplicity]
    split_ifs <;> omega
  · exact factorMultiplicity_le_one (fusionLabelSize M) _ L L'

theorem spherical_unfolded_off_entries (M:CoxeterMatrix S) (J:Set S)
    (hJ:IsSpherical M J) (α β:J × FusionLabel (fusionLabelSize M)) (h:α≠β) :
    fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j)) α β=0 ∨
    fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j)) α β= -1 := by
  have hn:=spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
  have he : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
      (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
      (fusionLabelSize M) α.2 β.2=1 := by omega
  rcases he with he|he <;>
    simp [fusionUnfoldedCartan,h,he]

end HarmonicArtin

end OAI
