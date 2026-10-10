import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Characteristic

namespace OAI

namespace HarmonicArtin
open Topology Set Metric Geometric CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

abbrev SourceCellIndex (n : ℕ) := {T : SphericalType M // T.val.ncard=n}

lemma sourceCell_ball_pair {n : ℕ} (i : SourceCellIndex M n) :
    ∃ h : (i.val.val → ℝ) ≃ₜ (Fin n → ℝ),
      h '' interior (permutahedron (restrictedMatrix M i.val.val)) = ball 0 1 ∧
      h '' permutahedron (restrictedMatrix M i.val.val) = closedBall 0 1 ∧
      h '' frontier (permutahedron (restrictedMatrix M i.val.val)) = sphere 0 1 := by
  obtain ⟨h,hi,hc,hf⟩ := permutahedron_ball_pair (restrictedMatrix M i.val.val)
  let e : i.val.val ≃ Fin n := Fintype.equivFinOfCardEq
    ((Set.fintypeCard_eq_ncard i.val.val).trans i.property)
  let j : (i.val.val → ℝ) ≃ᵢ (Fin n → ℝ) := IsometryEquiv.piCongrLeft' (Y := fun _ : i.val.val => ℝ) e
  have hz : j 0=0 := by
    ext k
    change (0 : i.val.val → ℝ) (e.symm k)=0
    rfl
  refine ⟨h.trans j.toHomeomorph,?_,?_,?_⟩
  · change (fun x => j (h x)) '' _ = _
    rw [←Set.image_image (⇑j) (⇑h),hi,j.image_ball,hz]
  · change (fun x => j (h x)) '' _ = _
    rw [←Set.image_image (⇑j) (⇑h),hc,j.image_closedBall,hz]
  · change (fun x => j (h x)) '' _ = _
    rw [←Set.image_image (⇑j) (⇑h),hf,j.image_sphere,hz]

noncomputable def sourceCellCoordinates {n : ℕ} (i : SourceCellIndex M n) :
    (i.val.val → ℝ) ≃ₜ (Fin n → ℝ) := (sourceCell_ball_pair M i).choose

lemma sourceCellCoordinates_spec {n : ℕ} (i : SourceCellIndex M n) :
    sourceCellCoordinates M i '' interior (permutahedron (restrictedMatrix M i.val.val)) = ball 0 1 ∧
    sourceCellCoordinates M i '' permutahedron (restrictedMatrix M i.val.val) = closedBall 0 1 ∧
    sourceCellCoordinates M i '' frontier (permutahedron (restrictedMatrix M i.val.val)) = sphere 0 1 :=
  (sourceCell_ball_pair M i).choose_spec

noncomputable def sourceCellBallHomeomorph {n : ℕ} (i : SourceCellIndex M n) :
    SourceModelCell M i.val ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (sourceCellCoordinates M i).sets (by
    rw [←(sourceCellCoordinates_spec M i).2.1,
      Set.preimage_image_eq _ (sourceCellCoordinates M i).injective])

lemma sourceCellBallHomeomorph_apply {n : ℕ} (i : SourceCellIndex M n)
    (x : SourceModelCell M i.val) :
    (sourceCellBallHomeomorph M i x).val=sourceCellCoordinates M i x.val := rfl

lemma sourceCellBallHomeomorph_interior_iff {n : ℕ} (i : SourceCellIndex M n)
    (x : SourceModelCell M i.val) :
    x.val ∈ interior (permutahedron (restrictedMatrix M i.val.val)) ↔
      (sourceCellBallHomeomorph M i x).val ∈ ball 0 1 := by
  rw [sourceCellBallHomeomorph_apply,←(sourceCellCoordinates_spec M i).1]
  exact ((sourceCellCoordinates M i).injective.mem_set_image).symm

lemma sourceCellBallHomeomorph_frontier_iff {n : ℕ} (i : SourceCellIndex M n)
    (x : SourceModelCell M i.val) :
    x.val ∈ frontier (permutahedron (restrictedMatrix M i.val.val)) ↔
      (sourceCellBallHomeomorph M i x).val ∈ sphere 0 1 := by
  rw [sourceCellBallHomeomorph_apply,←(sourceCellCoordinates_spec M i).2.2]
  exact ((sourceCellCoordinates M i).injective.mem_set_image).symm

noncomputable def sourceCellTotal {n : ℕ} (i : SourceCellIndex M n) (x : Fin n → ℝ) :
    SourceSalvetti M :=
  if hx : x ∈ closedBall 0 1 then
    sourceCharacteristic M i.val ((sourceCellBallHomeomorph M i).symm ⟨x,hx⟩)
  else sourceCharacteristic M i.val ((sourceCellBallHomeomorph M i).symm ⟨0,by simp⟩)

lemma sourceCellTotal_closedBall {n : ℕ} (i : SourceCellIndex M n) (x : Fin n → ℝ)
    (hx : x ∈ closedBall 0 1) : sourceCellTotal M i x =
      sourceCharacteristic M i.val ((sourceCellBallHomeomorph M i).symm ⟨x,hx⟩) := by
  simp only [sourceCellTotal,dite_eq_left hx]

lemma sourceCellTotal_continuousOn {n : ℕ} (i : SourceCellIndex M n) :
    ContinuousOn (sourceCellTotal M i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closedBall 0 1).domRestrict (sourceCellTotal M i)=
      sourceCharacteristic M i.val ∘ (sourceCellBallHomeomorph M i).symm := by
    funext x
    exact sourceCellTotal_closedBall M i x.val x.property
  rw [he]
  exact (sourceCharacteristic M i.val).continuous.comp (sourceCellBallHomeomorph M i).symm.continuous

lemma sourceCellTotal_image_closedBall {n : ℕ} (i : SourceCellIndex M n) :
    sourceCellTotal M i '' closedBall 0 1=Set.range (sourceCharacteristic M i.val) := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨_,(sourceCellTotal_closedBall M i x hx).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨(sourceCellBallHomeomorph M i x).val,(sourceCellBallHomeomorph M i x).property,?_⟩
    rw [sourceCellTotal_closedBall M i _ (sourceCellBallHomeomorph M i x).property]
    exact congrArg (sourceCharacteristic M i.val) ((sourceCellBallHomeomorph M i).symm_apply_apply x)

lemma sourceCellTotal_image_ball {n : ℕ} (i : SourceCellIndex M n) :
    sourceCellTotal M i '' ball 0 1=sourceOpenCell M i.val := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    let y := (sourceCellBallHomeomorph M i).symm ⟨x,ball_subset_closedBall hx⟩
    have hy : y.val ∈ interior (permutahedron (restrictedMatrix M i.val.val)) := by
      apply (sourceCellBallHomeomorph_interior_iff M i y).mpr
      simpa only [y,Homeomorph.apply_symm_apply] using hx
    exact ⟨⟨y,hy⟩,(sourceCellTotal_closedBall M i x (ball_subset_closedBall hx)).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨(sourceCellBallHomeomorph M i x.val).val,
      (sourceCellBallHomeomorph_interior_iff M i x.val).mp x.property,?_⟩
    rw [sourceCellTotal_closedBall M i _ (sourceCellBallHomeomorph M i x.val).property]
    exact congrArg (sourceCharacteristic M i.val) ((sourceCellBallHomeomorph M i).symm_apply_apply x.val)

end HarmonicArtin

end OAI
