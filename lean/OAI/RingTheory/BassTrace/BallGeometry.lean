import OAI.RingTheory.BassTrace.OrbitForms

namespace OAI

noncomputable section

namespace BassTrace

/-! Finite-center selection from compactness of closed original simplices, without a
cocompactness assumption on the continuous ambient space. -/

namespace Sparse

open Set

variable {H V I : Type*} [Group H] [PseudoMetricSpace V] [MulAction H V]

lemma finite_centers_of_compact {Q : Set V} (hQ : IsCompact Q) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset V, (C : Set V) ⊆ Q ∧ ∀ x ∈ Q, ∃ c ∈ C, dist x c < r := by
  classical
  obtain ⟨C,hC,hfin,hcov⟩ := hQ.elim_finite_subcover_image
    (b := Q) (c := fun c => Metric.ball c r) (fun _ _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨x,hx,by simpa using hr⟩)
  refine ⟨hfin.toFinset,by simpa using hC,?_⟩
  intro x hx
  obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨c,by simpa using hc,hxc⟩

theorem exists_finite_orbit_centers (S : Set V) (P : I → Set V) (F : Finset I)
    (hcompact : ∀ i ∈ F, IsCompact (P i)) (hPS : ∀ i ∈ F, P i ⊆ S)
    (hcover : ∀ x ∈ S, ∃ h : H, ∃ i ∈ F, ∃ y ∈ P i, h • y = x)
    (hisom : ∀ h : H, Isometry (fun x : V => h • x)) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset V, (C : Set V) ⊆ S ∧
      ∀ x ∈ S, ∃ h : H, ∃ c ∈ C, dist x (h • c) < r := by
  have hQ : IsCompact (⋃ i ∈ F, P i) := F.finite_toSet.isCompact_biUnion hcompact
  obtain ⟨C,hC,hcov⟩ := finite_centers_of_compact hQ hr
  refine ⟨C,?_,?_⟩
  · intro c hc
    obtain ⟨i,hi,hci⟩ := Set.mem_iUnion₂.mp (hC hc)
    exact hPS i hi hci
  · intro x hx
    obtain ⟨h,i,hi,y,hy,rfl⟩ := hcover x hx
    obtain ⟨c,hc,hyc⟩ := hcov y (Set.mem_iUnion₂.mpr ⟨i,hi,hy⟩)
    exact ⟨h,c,hc,by simpa only [(hisom h).dist_eq] using hyc⟩

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*} [DecidableEq Y]

lemma point_exists (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    ∃ p : FinProbability Y, p.coeff = v.val ∧ p.coeff.support ∈ K.faces := by
  exact (show v.val ∈ {w | ∃ p : FinProbability Y, p.coeff=w ∧ p.coeff.support ∈ K.faces} from
    (onFinsupp_space K) ▸ v.property)

def pointProbability (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) : FinProbability Y :=
  Classical.choose (point_exists K v)

lemma pointProbability_coeff (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    (pointProbability K v).coeff = v.val :=
  (Classical.choose_spec (point_exists K v)).1

lemma pointProbability_face (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    (pointProbability K v).coeff.support ∈ K.faces :=
  (Classical.choose_spec (point_exists K v)).2

def supportPatch (K : PreAbstractSimplicialComplex Y) (W : Finset Y) : Set (Y →₀ ℝ) :=
  {v | v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∧ v.support ⊆ W}

lemma supportPatch_marked (K : PreAbstractSimplicialComplex Y) (W : Finset Y) :
    Cuts.IsMarked (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (supportPatch K W) := by
  intro v hv
  obtain ⟨p,hp,hpK⟩ := (onFinsupp_space K) ▸ hv.1
  subst v
  refine ⟨p.coeff.support.image (fun y => Finsupp.single y (1:ℝ)),
    ⟨p.coeff.support,hpK,rfl⟩,?_,?_⟩
  · rw [Finset.coe_image,p.mem_geometric_simplex]
  · intro w hw
    have hw' := hw
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet] at hw'
    exact ⟨(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      ⟨p.coeff.support,hpK,rfl⟩ hw,hw'.2.2.trans hv.2⟩

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite]

def ballSupport (c : FinProbability Y) (n : ℕ) (R : ℝ) : Finset Y :=
  c.coeff.support ∪ c.coeff.support.biUnion
    (neighborhood Γ (⌊R * Real.sqrt (n : ℝ)⌋₊+n))

lemma ballSupport_center (c : FinProbability Y) (n : ℕ) (R : ℝ) :
    c.coeff.support ⊆ ballSupport Γ c n R := Finset.subset_union_left

lemma ballSupport_contains (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
      (Γ.induce (σ : Set Y)).Connected)
    (c p : FinProbability Y) (hp : p.coeff.support ∈ K.faces)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ R) :
    p.coeff.support ⊆ ballSupport Γ c n R := by
  obtain ⟨σ,_,hs,hcard,hconn⟩ := hK _ hp
  exact hs.trans ((meeting_simplex_vertices Γ hΓ hn c p σ hcard hconn hs R hR hball).trans
    Finset.subset_union_right)

def originalTops (K : PreAbstractSimplicialComplex Y) (n : ℕ) : Set (Finset Y) :=
  {s | s ∈ K.faces ∧ s.card=n+1}

lemma onFinsupp_space_eq_affineRealization (K : PreAbstractSimplicialComplex Y) (n : ℕ)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      affineRealization (originalTops K n) := by
  ext v
  rw [onFinsupp_space]
  constructor
  · rintro ⟨p,rfl,hp⟩
    obtain ⟨σ,hσ,hs,hcard⟩ := hK _ hp
    exact Set.mem_iUnion₂.mpr ⟨σ,⟨hσ,hcard⟩,p.nonneg,by simpa using p.total,hs⟩
  · intro hv
    obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp hv
    rw [probabilitySet_eq] at hv
    obtain ⟨p,rfl,hp⟩ := hv
    exact ⟨p,rfl,(K.isRelLowerSet_faces hσ.1).2 hp p.coeff_support_nonempty⟩

lemma continuous_pointProbability (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1)
    (hconn : ∀ σ ∈ originalTops K n, (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    Continuous (pointProbability K) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let e : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space →
      affineRealization (originalTops K n) := fun v =>
    ⟨v.val,(onFinsupp_space_eq_affineRealization K n hK) ▸ v.property⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have hc := (continuous_affineProbability Γ hΓ hn (originalTops K n)
    (fun σ hσ => ⟨hσ.2,hconn σ hσ⟩)).comp he
  convert hc using 1
  funext v
  apply FinProbability.ext_coeff
  exact pointProbability_coeff K v

def centerDistance (hΓ : Γ.Connected) (K : PreAbstractSimplicialComplex Y)
    (n : ℕ) (c : FinProbability Y) (v : Y →₀ ℝ) : ℝ :=
  if hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
    @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c (pointProbability K ⟨v,hv⟩)
  else 0

omit [Γ.LocallyFinite] in
lemma centerDistance_apply (hΓ : Γ.Connected) (K : PreAbstractSimplicialComplex Y)
    (n : ℕ) (c p : FinProbability Y) (hp : p.coeff.support ∈ K.faces) :
    centerDistance Γ hΓ K n c p.coeff =
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p := by
  have hv : p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [onFinsupp_space]
    exact ⟨p,rfl,hp⟩
  simp only [centerDistance,dite_eq_left hv]
  congr 1
  apply FinProbability.ext_coeff
  exact pointProbability_coeff K ⟨p.coeff,hv⟩

lemma continuousOn_centerDistance (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1)
    (hconn : ∀ σ ∈ originalTops K n, (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) :
    ContinuousOn (centerDistance Γ hΓ K n c)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := (continuous_const (y := c)).dist (continuous_pointProbability Γ hΓ hn K hK hconn)
  convert hc using 1
  funext v
  change centerDistance Γ hΓ K n c v.val = _
  simp only [centerDistance,dite_eq_left v.property]
  rfl

end Sparse.GraphGeometry

namespace Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [MetricSpace Y]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

def branches (h : H) (i : C) : Finset (H × Index S) :=
  Finset.univ.image (fun l : ↥(potentialVertices : Finset (S i → ℝ)) => (h,⟨i,l⟩))

omit [Group H] [MulAction H Y] [DecidableEq Y] in
lemma mem_branches (h : H) (i : C) (j : H × Index S) :
    j ∈ branches S h i ↔ ∃ l : ↥(potentialVertices : Finset (S i → ℝ)), j=(h,⟨i,l⟩) := by
  simp [branches,eq_comm]

omit [DecidableEq Y] [MetricSpace Y] in
lemma inverse_support_iff (h : H) (p : FinProbability Y) (W : Finset Y) :
    (h⁻¹ • p).coeff.support ⊆ W ↔
      p.coeff.support ⊆ W.map (MulAction.toPerm h).toEmbedding := by
  have hh : p.coeff.support = (h⁻¹ • p).coeff.support.map (MulAction.toPerm h).toEmbedding := by
    rw [← smul_probability_support,smul_inv_smul]
  rw [hh,Finset.map_subset_map]

def translatedPatch (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) : Set (Y →₀ ℝ) :=
  GraphGeometry.supportPatch K ((S i).map (MulAction.toPerm h).toEmbedding)

omit [MetricSpace Y] in
lemma translatedPatch_marked (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) :
    Cuts.IsMarked (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (translatedPatch S K h i) := GraphGeometry.supportPatch_marked _ _

omit [MetricSpace Y] in
lemma translatedPatch_mem (K : PreAbstractSimplicialComplex Y) (h : H) (i : C)
    (p : FinProbability Y) :
    p.coeff ∈ translatedPatch S K h i ↔
      p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∧
        (h⁻¹ • p).coeff.support ⊆ S i := by
  exact and_congr_right fun _ => (inverse_support_iff h p (S i)).symm

variable [IsCancelSMul H Y] [Fintype C]

lemma spherePatch_mem (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i)
    (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) (p : FinProbability Y)
    {t : ℝ} (ht : 0<t) :
    p.coeff ∈ ((OrbitForms.cuts (H := H) (data S c n) ht).spherePatch
        (translatedPatch S K h i) (branches S h i)) ↔
      p.coeff ∈ translatedPatch S K h i ∧ FinProbability.rho n (h • c i) p=t := by
  change (p.coeff ∈ translatedPatch S K h i ∧
      ∀ j ∈ branches S h i, OrbitForms.form (data S c n) j p.coeff ≤ t) ∧
      (∃ j ∈ branches S h i, OrbitForms.form (data S c n) j p.coeff=t) ↔ _
  constructor
  · rintro ⟨⟨hp,hle⟩,j,hj,he⟩
    obtain ⟨l,rfl⟩ := (mem_branches S h i j).mp hj
    refine ⟨hp,(distance_eq_iff S c n hi hc h i p ((translatedPatch_mem S K h i p).mp hp).2 t).mpr ?_⟩
    exact ⟨fun l' => hle _ ((mem_branches S h i _).mpr ⟨l',rfl⟩),l,he⟩
  · rintro ⟨hp,he⟩
    obtain ⟨hle,l,hl⟩ := (distance_eq_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mp he
    refine ⟨⟨hp,?_⟩,(h,⟨i,l⟩),(mem_branches S h i _).mpr ⟨l,rfl⟩,hl⟩
    intro j hj
    obtain ⟨l',rfl⟩ := (mem_branches S h i j).mp hj
    exact hle l'

end Sparse.BallOrbitForms

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

section

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hn hK hact hi hm

omit [IsCancelSMul H Y] [Fintype C] in
lemma ballSupport_inverse (c : C → FinProbability Y) (h : H) (i : C)
    (p : FinProbability Y) (hp : p.coeff.support ∈ K.faces)
    {R : ℝ} (hR : 0≤R) (hball : FinProbability.rho n (h • c i) p ≤ R) :
    (h⁻¹ • p).coeff.support ⊆ ballSupport Γ (c i) n R := by
  subst mY
  let := graphMetric Γ hΓ
  have hp' : (h⁻¹ • p).coeff.support ∈ K.faces := by
    rw [smul_probability_support]
    exact hact h⁻¹ _ hp
  apply ballSupport_contains Γ hΓ hn K hK _ _ hp' hR
  have he := smul_probability_rho hi h⁻¹ n (h • c i) p
  rw [inv_smul_smul] at he
  rw [he]
  exact hball

lemma sphere_eq_patch (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (ht : 0<t) (htR : t≤R) :
    let S := fun i => ballSupport Γ (c i) n R
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩
        {v | centerDistance Γ hΓ K n (h • c i) v=t} =
      (OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht).spherePatch
        (BallOrbitForms.translatedPatch S K h i) (BallOrbitForms.branches S h i) := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  ext v
  constructor
  · rintro ⟨hv,he⟩
    change centerDistance Γ hΓ K n (h • c i) v = t at he
    let p := pointProbability K ⟨v,hv⟩
    have hp : p.coeff = v := pointProbability_coeff K _
    have hpK := pointProbability_face K ⟨v,hv⟩
    have he' : FinProbability.rho n (h • c i) p=t := by
      rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at he
      exact he
    rw [← hp]
    apply (BallOrbitForms.spherePatch_mem S c n hi (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mpr
    refine ⟨(BallOrbitForms.translatedPatch_mem S K h i p).mpr ⟨hp.symm ▸ hv,?_⟩,he'⟩
    exact ballSupport_inverse Γ hΓ rfl hn K hK hact hi c h i p hpK hR (he' ▸ htR)
  · intro hv
    have hvK : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1.1.1
    let p := pointProbability K ⟨v,hvK⟩
    have hp : p.coeff=v := pointProbability_coeff K _
    rw [← hp] at hv ⊢
    obtain ⟨_,he⟩ := (BallOrbitForms.spherePatch_mem S c n hi
      (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mp hv
    refine ⟨hp.symm ▸ hvK,?_⟩
    change centerDistance Γ hΓ K n (h • c i) p.coeff = t
    rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)]
    exact he

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

def realizationDistance (n : ℕ) (p q : Y →₀ ℝ) : ℝ :=
  if hp : p ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
    if hq : q ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n
        (pointProbability K ⟨p,hp⟩) (pointProbability K ⟨q,hq⟩)
    else 0
  else 0

omit [Γ.LocallyFinite] [MetricSpace Y] in
lemma realizationDistance_apply (n : ℕ) (p q : FinProbability Y)
    (hp : p.coeff.support ∈ K.faces) (hq : q.coeff.support ∈ K.faces) :
    realizationDistance Γ hΓ K n p.coeff q.coeff =
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n p q := by
  have hp' : p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (onFinsupp_space K).symm ▸ ⟨p,rfl,hp⟩
  have hq' : q.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (onFinsupp_space K).symm ▸ ⟨q,rfl,hq⟩
  simp only [realizationDistance,dite_eq_left hp',dite_eq_left hq']
  congr 1 <;> apply FinProbability.ext_coeff <;> exact pointProbability_coeff K _

omit [Γ.LocallyFinite] [MetricSpace Y] in
lemma realizationDistance_center_triangle (n : ℕ) (c : FinProbability Y)
    (p : Y →₀ ℝ) (hp : p ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space)
    (q : Y →₀ ℝ) (hq : q ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    realizationDistance Γ hΓ K n p q ≤ centerDistance Γ hΓ K n c p +
      centerDistance Γ hΓ K n c q := by
  let := graphMetric Γ hΓ
  simp only [realizationDistance,centerDistance,dite_eq_left hp,dite_eq_left hq]
  exact (FinProbability.rho_triangle n _ c _).trans_eq (by rw [FinProbability.rho_comm n _ c])

omit [DecidableEq Y] [Γ.LocallyFinite] in
include hm hn in

lemma exists_orbit_center_cover
    (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    {r : ℝ} (hr : 0<r) :
    ∃ C : Finset (FinProbability Y), (∀ c ∈ C, c.coeff.support ∈ K.faces) ∧
      ∀ p : FinProbability Y, p.coeff.support ∈ K.faces →
        ∃ h : H, ∃ c ∈ C, FinProbability.rho n p (h • c) < r := by
  subst mY
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let S : Set (FinProbability Y) := {p | p.coeff.support ∈ K.faces}
  let P : Finset Y → Set (FinProbability Y) := fun s => {p | p.coeff.support ⊆ s}
  obtain ⟨C,hC,hcov⟩ := exists_finite_orbit_centers (H := H) S P F
    (fun s _ => isCompact_probability_simplex s n hn (graphMetric_discrete Γ hΓ))
    (fun s hs p hp => (K.isRelLowerSet_faces (hF s hs)).2 hp p.coeff_support_nonempty)
    (by
      intro p hp
      obtain ⟨h,τ,hτ,he⟩ := hrep p.coeff.support hp
      refine ⟨h,τ,hτ,h⁻¹ • p,?_,smul_inv_smul h p⟩
      change (h⁻¹ • p).coeff.support ⊆ τ
      rw [BallOrbitForms.inverse_support_iff]
      exact he.subset)
    (fun h => Isometry.of_dist_eq (fun p q => smul_probability_rho hi h n p q)) hr
  exact ⟨C,hC,hcov⟩

end

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

include hact in
lemma space_push (h : H) (v : Y →₀ ℝ)
    (hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    OrbitForms.push h v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  obtain ⟨p,rfl,hp⟩ := (onFinsupp_space K) ▸ hv
  rw [BallOrbitForms.push_coeff,onFinsupp_space]
  refine ⟨h • p,rfl,?_⟩
  rw [smul_probability_support]
  exact hact h _ hp

include hact in
lemma centerDistance_push (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
    (hi : ∀ h : H, @Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
      (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y => h • y))
    (n : ℕ) (h : H) (c : FinProbability Y) (v : Y →₀ ℝ)
    (hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    centerDistance Γ hΓ K n (h • c) (OrbitForms.push h v) =
      centerDistance Γ hΓ K n c v := by
  let := graphMetric Γ hΓ
  obtain ⟨p,rfl,hp⟩ := (onFinsupp_space K) ▸ hv
  have hhp : (h • p).coeff.support ∈ K.faces := by
    rw [smul_probability_support]
    exact hact h _ hp
  rw [BallOrbitForms.push_coeff,centerDistance_apply Γ hΓ K n _ _ hhp,
    centerDistance_apply Γ hΓ K n _ _ hp]
  exact smul_probability_rho hi h n c p

end Sparse.GraphGeometry

namespace Sparse.OrbitForms

open scoped BassTrace.Sparse

variable {H Y X : Type*} [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X]

def MarkedEquivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    {T : Cuts.SubdivisionFamily X K} (P : Cuts.MarkedFamily T) : Prop :=
  ∀ (k : H) (x : X) v, v ∈ P.val x → push k v ∈ P.val (k • x)

end Sparse.OrbitForms

end BassTrace

end

end OAI
