import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CharacteristicSaturatedInterior
import OAI.Topology.ArtinGroups.Realizations.CellIndex
import OAI.Topology.ArtinGroups.Realizations.PartialEquivContinuousSymm

namespace OAI

namespace HarmonicArtin
open Topology Set Metric Geometric CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

noncomputable def sourceCellInteriorChart {n : ℕ} (i : SourceCellIndex M n) :
    ball (0 : Fin n → ℝ) 1 ≃ₜ SourceModelInterior M i.val where
  toFun x := ⟨(sourceCellBallHomeomorph M i).symm ⟨x.val,ball_subset_closedBall x.property⟩,
    (sourceCellBallHomeomorph_interior_iff M i _).mpr (by
      simpa only [Homeomorph.apply_symm_apply] using x.property)⟩
  invFun y := ⟨(sourceCellBallHomeomorph M i y.val).val,
    (sourceCellBallHomeomorph_interior_iff M i y.val).mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : closedBall (0 : Fin n → ℝ) 1 => z.val) ((sourceCellBallHomeomorph M i).apply_symm_apply
      ⟨x.val,ball_subset_closedBall x.property⟩)
  right_inv y := by
    apply Subtype.ext
    exact (sourceCellBallHomeomorph M i).symm_apply_apply y.val
  continuous_toFun := (((sourceCellBallHomeomorph M i).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp
    ((sourceCellBallHomeomorph M i).continuous.comp continuous_subtype_val)).subtype_mk _)

lemma sourceCellTotal_restrict_ball {n : ℕ} (i : SourceCellIndex M n) :
    (ball 0 1).domRestrict (sourceCellTotal M i)=
      (fun x : SourceModelInterior M i.val => sourceCharacteristic M i.val x.val) ∘
        sourceCellInteriorChart M i := by
  funext x
  exact sourceCellTotal_closedBall M i x.val (ball_subset_closedBall x.property)

lemma sourceCellTotal_embedding_ball {n : ℕ} (i : SourceCellIndex M n) :
    IsEmbedding ((ball 0 1).domRestrict (sourceCellTotal M i)) := by
  rw [sourceCellTotal_restrict_ball]
  exact (sourceCharacteristic_interior_embedding M i.val).comp
    (sourceCellInteriorChart M i).isEmbedding

lemma sourceCellTotal_injOn_ball {n : ℕ} (i : SourceCellIndex M n) :
    Set.InjOn (sourceCellTotal M i) (ball 0 1) := by
  intro x hx y hy hxy
  have h := (sourceCellTotal_embedding_ball M i).injective
    (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy
  exact congrArg Subtype.val h

noncomputable def sourceCellPartial {n : ℕ} (i : SourceCellIndex M n) :
    PartialEquiv (Fin n → ℝ) (SourceSalvetti M) :=
  (sourceCellTotal_injOn_ball M i).toPartialEquiv (sourceCellTotal M i) (ball 0 1)

lemma sourceCellPartial_source {n : ℕ} (i : SourceCellIndex M n) :
    (sourceCellPartial M i).source=ball 0 1 := rfl

lemma sourceCellPartial_apply {n : ℕ} (i : SourceCellIndex M n) (x : Fin n → ℝ) :
    sourceCellPartial M i x=sourceCellTotal M i x := rfl

lemma sourceCellPartial_continuousOn_symm {n : ℕ} (i : SourceCellIndex M n) :
    ContinuousOn (sourceCellPartial M i).symm (sourceCellPartial M i).target :=
  partialEquiv_continuousOn_symm _ (sourceCellTotal_embedding_ball M i)

lemma sourceCellPartial_image_closedBall {n : ℕ} (i : SourceCellIndex M n) :
    sourceCellPartial M i '' closedBall 0 1=Set.range (sourceCharacteristic M i.val) :=
  sourceCellTotal_image_closedBall M i

lemma sourceCellPartial_image_ball {n : ℕ} (i : SourceCellIndex M n) :
    sourceCellPartial M i '' ball 0 1=sourceOpenCell M i.val :=
  sourceCellTotal_image_ball M i

lemma sourceCellPartial_boundary {n : ℕ} (i : SourceCellIndex M n)
    (x : Fin n → ℝ) (hx : x ∈ sphere 0 1) :
    ∃ m : ℕ, m<n ∧ ∃ j : SourceCellIndex M m,
      sourceCellPartial M i x ∈ sourceCellPartial M j '' closedBall 0 1 := by
  let y := (sourceCellBallHomeomorph M i).symm ⟨x,sphere_subset_closedBall hx⟩
  have hy : y.val ∈ frontier (permutahedron (restrictedMatrix M i.val.val)) := by
    apply (sourceCellBallHomeomorph_frontier_iff M i y).mpr
    simpa only [y,Homeomorph.apply_symm_apply] using hx
  obtain ⟨R,hR,hq⟩ := sourceCharacteristic_boundary_lower M i.val y hy
  refine ⟨R.val.ncard,by rwa [←i.property],⟨R,rfl⟩,?_⟩
  rw [sourceCellPartial_image_closedBall,sourceCellPartial_apply,
    sourceCellTotal_closedBall M i x (sphere_subset_closedBall hx)]
  exact hq

end HarmonicArtin

end OAI
