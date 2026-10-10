import OAI.RingTheory.BassTrace.FaceFiltration

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y X : Type*} [DecidableEq Y] [TopologicalSpace X]

variable {K : PreAbstractSimplicialComplex Y}

variable {T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)}

variable (P : Cuts.MarkedFamily T)

lemma marked_localConstancy_window (W : Finset Y) :
    IsLocallyConstant (fun x=>P.val x ∩ probabilitySet W) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let A := W.powerset.filter (fun s=>s∈K.faces)
  have hA : ∀ s∈A, ∀ᶠ y in nhds x,
      P.val y ∩ probabilitySet s=P.val x ∩ probabilitySet s := by
    intro s hs
    have hsK := (Finset.mem_filter.mp hs).2
    have hh := (P.localConstancy_inter (simplexVertices s) ⟨s,hsK,rfl⟩
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) subset_rfl).eventually_eq x
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hh
  filter_upwards [(Filter.eventually_all_finite (Finset.finite_toSet A)).mpr hA] with y hy
  have he (z z' : X) (hz : ∀ s∈A,P.val z ∩ probabilitySet s=P.val z' ∩ probabilitySet s) :
      P.val z∩probabilitySet W⊆P.val z'∩probabilitySet W := by
    rintro p ⟨hp,hpW⟩
    have hpK : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
      (T.val z).space_eq ▸ (P.marked z).subset_space hp
    let q := GraphGeometry.pointProbability K ⟨p,hpK⟩
    have hq : q.coeff=p := GraphGeometry.pointProbability_coeff K _
    have hsK : p.support∈K.faces := hq ▸ GraphGeometry.pointProbability_face K ⟨p,hpK⟩
    have hs : p.support∈A := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hpW.2.2,hsK⟩
    have hpp : p∈probabilitySet p.support := ⟨hpW.1,hpW.2.1,subset_rfl⟩
    exact ⟨((hz _ hs) ▸ (show p∈P.val z∩probabilitySet p.support from ⟨hp,hpp⟩)).1,hpW⟩
  exact Set.Subset.antisymm (he y x hy) (he x y (fun s hs=>(hy s hs).symm))

omit [DecidableEq Y] [TopologicalSpace X] in
lemma connectedComponentIn_inter_of_subset {V : Type*} [TopologicalSpace V]
    (S W : Set V) (p : V) (hp : p∈S)
    (hW : connectedComponentIn S p⊆W) :
    connectedComponentIn (S∩W) p=connectedComponentIn S p := by
  apply Set.Subset.antisymm (connectedComponentIn_mono p Set.inter_subset_left)
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hp) (fun _ h=>⟨connectedComponentIn_subset S p h,hW h⟩)

end Sparse

namespace Sparse.Cuts.PointFiltration

open Set Finset

open scoped Classical

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

variable (Q Q' : PointFiltration K n)

lemma faceLevel_eq_of_window (F : Finset V)
    (hF : F∈(Q.T 0).faces) (hF' : F∈(Q'.T 0).faces)
    (W : Set V) (hm : vertexMean F∈W)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) :
    Q.faceLevel ⟨F,hF⟩=Q'.faceLevel ⟨F,hF'⟩ := by
  apply Nat.le_antisymm
  · apply (Q.mean_mem_iff_level_le ⟨F,hF⟩ (Q'.faceLevel_le ⟨F,hF'⟩)).mp
    exact ((hZ _ (Q'.faceLevel_le ⟨F,hF'⟩)).symm ▸
      (show vertexMean F∈Q'.Z (Q'.faceLevel ⟨F,hF'⟩)∩W from
        ⟨Q'.mean_mem_faceLevel ⟨F,hF'⟩,hm⟩)).1
  · apply (Q'.mean_mem_iff_level_le ⟨F,hF'⟩ (Q.faceLevel_le ⟨F,hF⟩)).mp
    exact ((hZ _ (Q.faceLevel_le ⟨F,hF⟩)) ▸
      (show vertexMean F∈Q.Z (Q.faceLevel ⟨F,hF⟩)∩W from
        ⟨Q.mean_mem_faceLevel ⟨F,hF⟩,hm⟩)).1

lemma stratum_inter_eq_of_window (W : Set V)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) (i : ℕ) (hi : i≤n) :
    Q.stratum i∩W=Q'.stratum i∩W := by
  have he (A B : Set V) : (A\B)∩W=(A∩W)\(B∩W) := by ext p; simp; tauto
  unfold stratum
  rw [he,he,hZ i hi]
  congr 1
  unfold below
  split_ifs with hz
  · rfl
  · exact hZ (i-1) (by omega)

lemma faceComponent_eq_of_window (F : Finset V)
    (hF : F∈(Q.T 0).faces) (hF' : F∈(Q'.T 0).faces)
    (W : Set V)
    (hW : Q.faceComponent ⟨F,hF⟩⊆W) (hW' : Q'.faceComponent ⟨F,hF'⟩⊆W)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) :
    Q.faceComponent ⟨F,hF⟩=Q'.faceComponent ⟨F,hF'⟩ := by
  have hlev := Q.faceLevel_eq_of_window Q' F hF hF' W
    (hW (Q.mean_mem_component ⟨F,hF⟩)) hZ
  change connectedComponentIn (Q.stratum (Q.faceLevel ⟨F,hF⟩)) (vertexMean F)=
    connectedComponentIn (Q'.stratum (Q'.faceLevel ⟨F,hF'⟩)) (vertexMean F)
  rw [← BassTrace.Sparse.connectedComponentIn_inter_of_subset
    (Q.stratum (Q.faceLevel ⟨F,hF⟩)) W (vertexMean F)
    (Q.mean_mem_stratum ⟨F,hF⟩) hW]
  rw [Q.stratum_inter_eq_of_window Q' W hZ _ (Q.faceLevel_le ⟨F,hF⟩),hlev]
  exact BassTrace.Sparse.connectedComponentIn_inter_of_subset
    (Q'.stratum (Q'.faceLevel ⟨F,hF'⟩)) W (vertexMean F)
    (Q'.mean_mem_stratum ⟨F,hF'⟩) hW'

end Sparse.Cuts.PointFiltration

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hK in
lemma component_subset_window (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    (Q.point x).faceComponent F⊆probabilitySet (labelWindow Γ n R s) := by
  intro v hv
  let p := pointProbability K ⟨v,faceComponent_mem_space Γ hΓ Q x F hv⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hh : v∈probabilitySet v.support := by
    rw [←hp]
    exact ⟨p.nonneg,by simpa only [coefficientSum_apply] using p.total,subset_rfl⟩
  exact ⟨hh.1,hh.2.1,component_support_subset Γ hΓ Q hK hn hR x F s hFs hv⟩

include hK in
lemma faceComponents_eq_local (hn : 0<n) (hR : 0≤R) (s : Finset Y) (hs : s∈K.faces)
    (x : X) : ∀ᶠ y in nhds x,
    (Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces=
    (Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces ∧
    ∀ (F : Finset (Y →₀ ℝ))
      (hFx : F∈((Q.pair 0).T.val x).complex.faces)
      (hFy : F∈((Q.pair 0).T.val y).complex.faces),
      convexHull ℝ (F : Set (Y →₀ ℝ))⊆
        convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) →
      (Q.point y).faceComponent ⟨F,hFy⟩=(Q.point x).faceComponent ⟨F,hFx⟩ := by
  let W := probabilitySet (labelWindow Γ n R s)
  have hZ : ∀ i∈Finset.range (n+1), ∀ᶠ y in nhds x,
      (Q.point y).Z i∩W=(Q.point x).Z i∩W := by
    intro i _
    exact (marked_localConstancy_window (Q.pair i).P (labelWindow Γ n R s)).eventually_eq x
  filter_upwards [((Q.pair 0).T.localConstancy (simplexVertices s) ⟨s,hs,rfl⟩).eventually_eq x,
    (Filter.eventually_all_finite (Finset.finite_toSet (Finset.range (n+1)))).mpr hZ] with y hT hy
  refine ⟨hT,?_⟩
  intro F hFx hFy hFs
  have hm := hFs (Cuts.vertexMean_mem_convexHull
    (((Q.pair 0).T.val x).complex.nonempty_of_mem_faces hFx))
  apply (Q.point y).faceComponent_eq_of_window (Q.point x) F hFy hFx W
    (component_subset_window Γ hΓ Q hK hn hR y ⟨F,hFy⟩ s hm)
    (component_subset_window Γ hΓ Q hK hn hR x ⟨F,hFx⟩ s hm)
  intro i hi
  exact hy i (Finset.mem_range.mpr (by omega))

end Sparse.GraphGeometry

namespace Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

private def componentVectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 :=
  Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)

private lemma componentVectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    componentVectorEmbedding v y = v y := by
  simp only [componentVectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

lemma push_norm (h : H) (p : Y →₀ ℝ) : ‖push h p‖=‖p‖ := by
  change ‖componentVectorEmbedding (push h p)‖=‖componentVectorEmbedding p‖
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ENNReal).toReal)]
  congr 1
  simp only [componentVectorEmbedding_apply,push_apply]
  exact (Equiv.tsum_eq (MulAction.toPerm h⁻¹ : Y ≃ Y) (fun i=>‖p i‖ ^ (2:ENNReal).toReal))

def pushIsometry (h : H) : (Y →₀ ℝ) ≃ₗᵢ[ℝ] (Y →₀ ℝ) where
  __ := push h
  norm_map' := push_norm h

def pushHomeomorph (h : H) : (Y →₀ ℝ) ≃ₜ (Y →₀ ℝ) :=
  (pushIsometry h).toHomeomorph

variable {X : Type*} [TopologicalSpace X] [MulAction H X]

variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}

variable (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)

namespace SeparatingFiltration

def translateFace (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).FinalFace :=
  ⟨F.val.map (push h).toEmbedding,(Q.pair 0).equivariant h x F.val F.property⟩

lemma translateFace_mean (h : H) (x : X) (F : (Q.point x).FinalFace) :
    Cuts.vertexMean (Q.translateFace h x F).val=push h (Cuts.vertexMean F.val) :=
  Cuts.vertexMean_map (push h).toAffineEquiv
    (((Q.pair 0).T.val x).complex.nonempty_of_mem_faces F.property)

lemma push_mem_marked_iff (h : H) (x : X) (i : ℕ) (p : Y →₀ ℝ) :
    push h p∈(Q.point (h • x)).Z i ↔ p∈(Q.point x).Z i := by
  constructor
  · intro hp
    have hh := (Q.pair i).markedEquivariant h⁻¹ (h • x) (push h p) hp
    change p∈(Q.pair i).P.val x
    simpa only [push_inv_push,inv_smul_smul] using hh
  · exact (Q.pair i).markedEquivariant h x p

lemma translateFace_level (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).faceLevel (Q.translateFace h x F)=(Q.point x).faceLevel F := by
  apply Nat.le_antisymm
  · apply ((Q.point (h • x)).mean_mem_iff_level_le _ ((Q.point x).faceLevel_le F)).mp
    rw [Q.translateFace_mean,Q.push_mem_marked_iff]
    exact (Q.point x).mean_mem_faceLevel F
  · apply ((Q.point x).mean_mem_iff_level_le F ((Q.point (h • x)).faceLevel_le _)).mp
    have hh := (Q.point (h • x)).mean_mem_faceLevel (Q.translateFace h x F)
    rwa [Q.translateFace_mean,Q.push_mem_marked_iff] at hh

lemma push_mem_stratum_iff (h : H) (x : X) (i : ℕ) (p : Y →₀ ℝ) :
    push h p∈(Q.point (h • x)).stratum i ↔ p∈(Q.point x).stratum i := by
  simp only [Cuts.PointFiltration.stratum,Cuts.PointFiltration.below,Set.mem_sdiff,
    Q.push_mem_marked_iff]
  split_ifs <;> simp only [Set.mem_empty_iff_false,Q.push_mem_marked_iff]

lemma stratum_image (h : H) (x : X) (i : ℕ) :
    push h '' (Q.point x).stratum i=(Q.point (h • x)).stratum i := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (Q.push_mem_stratum_iff h x i q).mpr hq
  · intro hp
    refine ⟨push h⁻¹ p,?_,?_⟩
    · have hh := (Q.push_mem_stratum_iff h⁻¹ (h • x) i p).mpr hp
      simpa only [inv_smul_smul] using hh
    · rw [←push_mul,mul_inv_cancel,push_one]

lemma translateFace_component (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).faceComponent (Q.translateFace h x F)=
      push h '' (Q.point x).faceComponent F := by
  unfold Cuts.PointFiltration.faceComponent
  rw [Q.translateFace_level,Q.translateFace_mean]
  rw [←Q.stratum_image h x ((Q.point x).faceLevel F)]
  exact ((pushHomeomorph h).image_connectedComponentIn
    ((Q.point x).mean_mem_stratum F)).symm

end SeparatingFiltration

end Sparse.OrbitForms

end BassTrace

end

end OAI
