import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SphericalFoldedMatrix
import OAI.Topology.ArtinGroups.Harmonic.RowReflect
import OAI.Topology.ArtinGroups.Geometry.RestrictionLength
import OAI.Topology.ArtinGroups.Geometry.RootPair

namespace OAI

namespace HarmonicArtin
open Matrix Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S]

noncomputable def unfoldedMatrix (M : CoxeterMatrix S) (J : Set S) :
    CoxeterMatrix (J × FusionLabel (fusionLabelSize M)) where
  M α β := if α=β then 1 else if (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
    (fusionLabelSize M) α.2 β.2=0 then 2 else 3
  isSymm := by
    ext α β
    dsimp [Matrix.transpose]
    rw [coxeterFusionEdge_symm M (.inl β.1) (.inl α.1),FusionEdge.multiplicity_symm]
    simp only [eq_comm]
  diagonal α := by simp
  off_diagonal α β h := by simp only [ite_eq_right h]; split_ifs <;> omega

@[simp] lemma unfoldedMatrix_apply (M : CoxeterMatrix S) (J : Set S)
    (α β : J × FusionLabel (fusionLabelSize M)) :
    unfoldedMatrix M J α β=if α=β then 1 else
      if (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 then 2 else 3 := rfl

lemma unfoldedMatrix_cartan (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    cartan (unfoldedMatrix M J)=fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j)) := by
  funext α β
  by_cases he : α=β
  · subst β
    simp [cartan,fusionUnfoldedCartan,coxeterFusionEdge_diag,FusionEdge.multiplicity]
  · have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
    have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=1 := by omega
    rcases hp with hzero | hone
    · have hm : unfoldedMatrix M J α β=2 := by rw [unfoldedMatrix_apply,ite_eq_right he,ite_eq_left hzero]
      have hc : cartan (unfoldedMatrix M J) α β=0 := by
        simp only [cartan,ite_eq_right he,hm]
        norm_num
      rw [hc]
      simp only [fusionUnfoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,ite_eq_right he,
        Matrix.of_apply,hzero,Nat.cast_zero,sub_zero]
    · have hm : unfoldedMatrix M J α β=3 := by simp only [unfoldedMatrix_apply,ite_eq_right he,hone]; norm_num
      have hc : cartan (unfoldedMatrix M J) α β= -1 := by
        simp only [cartan,ite_eq_right he,hm]
        norm_num [Real.cos_pi_div_three]
      rw [hc]
      simp only [fusionUnfoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,ite_eq_right he,
        Matrix.of_apply,hone,Nat.cast_one,zero_sub]

omit [Fintype S] in
lemma foldedMatrix_cartan (M : CoxeterMatrix S) (J : Set S) :
    fusionFoldedCartan (fusionLabelSize M)
      (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j))=cartan (restrictedMatrix M J) := by
  rw [spherical_folded_matrix,cartan_restricted]

lemma rowReflectWord_representation {V W : Type*} [Fintype V] [DecidableEq V] [Group W]
    {N : CoxeterMatrix V} (cs : CoxeterSystem N W) (u : List V) (p : V → ℝ) :
    rowReflectWord (cartan N) u p=representation cs (cs.wordProd u) p := by
  induction u with
  | nil => simp [rowReflectWord]
  | cons i u ih =>
    change rowReflect (cartan N) i (rowReflectWord (cartan N) u p)=_
    rw [ih,rowReflect_geometric,CoxeterSystem.wordProd_cons,map_mul,
      LinearEquiv.mul_apply,representation_simple]

theorem unfolded_word_representation (M : CoxeterMatrix S) (J : Set S)
    (hJ : IsSpherical M J) (u : List J) (p : J → ℝ) :
    representation (unfoldedMatrix M J).toCoxeterSystem
      ((unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u))
      (fusionFold (fusionLabelSize M) p)=
      fusionFold (fusionLabelSize M)
        (representation (restrictedMatrix M J).toCoxeterSystem
          ((restrictedMatrix M J).toCoxeterSystem.wordProd u) p) := by
  rw [← rowReflectWord_representation,← rowReflectWord_representation,unfoldedMatrix_cartan M J hJ]
  simpa only [foldedMatrix_cartan] using fusion_word_intertwining (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e))
    (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j))
    (fun i => coxeterFusionEdge_diag M (.inl i)) u p

lemma unfolded_rootRow_fold (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (p : J → ℝ) (α : J × FusionLabel (fusionLabelSize M)) :
    rootRow (unfoldedMatrix M J) α (fusionFold (fusionLabelSize M) p)=
      fusionWeight (fusionLabelSize M) α.2*rootRow (restrictedMatrix M J) α.1 p := by
  rw [rootRow_apply,unfoldedMatrix_cartan M J hJ,fusion_intertwining (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)),foldedMatrix_cartan]
  rfl

lemma unfolded_strict_chamber (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    ∃ p : J → ℝ,(∀ i,0 < rootRow (restrictedMatrix M J) i p) ∧
      ∀ α,0 < rootRow (unfoldedMatrix M J) α (fusionFold (fusionLabelSize M) p) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let : Fintype (restrictedMatrix M J).Group := Fintype.ofFinite _
  obtain ⟨p,hp⟩ := exists_strict_chamber (restrictedMatrix M J).toCoxeterSystem
  refine ⟨p,?_,?_⟩
  · intro i
    rw [rootRow_apply,hp]
    norm_num
  · intro α
    rw [unfolded_rootRow_fold M J hJ,rootRow_apply,hp,mul_one]
    exact fusionWeight_pos (fusionLabelSize M)
      (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) α.2

theorem unfolded_left_ascent_iff (M : CoxeterMatrix S) (J : Set S)
    (hJ : IsSpherical M J) (u : List J) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (d.simple α*d.wordProd (fusionExpandedWord (fusionLabelSize M) u))=
        d.length (d.wordProd (fusionExpandedWord (fusionLabelSize M) u))+1 ↔
      c.length (c.simple α.1*c.wordProd u)=c.length (c.wordProd u)+1 := by
  dsimp only
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  rw [← rootRow_pos_iff_left_ascent _ (fusionFold (fusionLabelSize M) p) hq,
    ← rootRow_pos_iff_left_ascent _ p hp,unfolded_word_representation M J hJ,
    unfolded_rootRow_fold M J hJ]
  exact mul_pos_iff_of_pos_left (fusionWeight_pos (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) α.2)

theorem unfolded_word_one (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.wordProd u=1) :
    (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u)=1 := by
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  apply chamber_stabilizer (unfoldedMatrix M J).toCoxeterSystem
    (fusionFold (fusionLabelSize M) p) hq
  rw [unfolded_word_representation M J hJ,hu,map_one]
  rfl

end HarmonicArtin

end OAI
