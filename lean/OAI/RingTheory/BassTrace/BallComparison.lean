import OAI.RingTheory.BassTrace.MeasurableSlices

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

def OrbitForms.SeparatingFiltration.admissibleStep
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    {j : ℕ} (hj : j<n) : Cuts.AdmissibleStep ρ R (Q.pair (j+1)).T (Q.pair (j+1)).P where
  next := (Q.pair j).T
  finer := Q.finer j hj
  oldMarked := fun x => (Q.finer j hj x).preserves_marked ((Q.pair (j+1)).P.marked x)
  zero := (Q.pair j).P
  subset := Q.nested j hj
  dimensionDrop := Q.drop j hj
  diameter := Q.diameter j hj

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {Y : Type*} [DecidableEq Y] [Countable Y]

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

variable (K : PreAbstractSimplicialComplex Y)

lemma measurable_realization : MeasurableSet
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  have he : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      ⋃ s∈K.faces, convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
    ext p
    rw [Geometry.SimplicialComplex.mem_space_iff]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨_,⟨s,hs,rfl⟩,hp⟩
      exact ⟨s,hs,hp⟩
    · rintro ⟨s,hs,hp⟩
      exact ⟨simplexVertices s,⟨s,hs,rfl⟩,hp⟩
  rw [he]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ =>
    ((simplexVertices s).finite_toSet.isCompact_convexHull ℝ).isClosed.measurableSet

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable {n : ℕ} (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in
lemma measurable_centerDistance (c : FinProbability Y) :
    Measurable (centerDistance Γ hΓ K n c) := by
  have hc := continuousOn_centerDistance Γ hΓ hn K
    (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,-⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
    (fun σ hσ => by
      obtain ⟨τ,hτ,hστ,hcard,hconn⟩ := hK σ hσ.1
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,hσ.2])
      exact he.symm ▸ hconn) c
  have hm := hc.measurable_piecewise (continuous_const (y := (0 : ℝ))).continuousOn (measurable_realization K)
  convert hm using 1
  funext p
  by_cases hp : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space
  · simp only [Set.piecewise, hp,ite_eq_left]
  · simp [Set.piecewise,centerDistance,hp]

def ballWindow (c : FinProbability Y) (J : Set ℝ) : Set (Y →₀ ℝ) :=
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩
    centerDistance Γ hΓ K n c ⁻¹' J

include hn hK in
lemma measurable_ballWindow (c : FinProbability Y) (J : Set ℝ) (hJ : MeasurableSet J) :
    MeasurableSet (ballWindow K Γ hΓ (n := n) c J) :=
  (measurable_realization K).inter (hJ.preimage (measurable_centerDistance K Γ hΓ hn hK c))

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (n : ℕ)

omit [Countable Y] in
include hact hi in
lemma ballWindow_push (c : FinProbability Y) (J : Set ℝ) (h : H) :
    OrbitForms.push h '' ballWindow K Γ hΓ (n := n) c J =
      ballWindow K Γ hΓ (n := n) (h•c) J := by
  ext p
  constructor
  · rintro ⟨q,⟨hq,hqr⟩,rfl⟩
    refine ⟨space_push K hact h q hq,?_⟩
    simpa only [Set.mem_preimage,centerDistance_push K hact Γ hΓ hi n h c q hq] using hqr
  · rintro ⟨hp,hpr⟩
    have hq := space_push K hact h⁻¹ p hp
    refine ⟨OrbitForms.push h⁻¹ p,⟨hq,?_⟩,?_⟩
    · have he := centerDistance_push K hact Γ hΓ hi n h⁻¹ (h•c) p hp
      rw [inv_smul_smul] at he
      simpa only [Set.mem_preimage,he] using hpr
    · simpa only [inv_inv] using OrbitForms.push_inv_push h⁻¹ p

omit [Countable Y] in
lemma original_marked_subset_space
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (x : X) :
    Q.P.val x⊆(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  intro p hp
  exact (Q.T.val x).space_eq ▸ ((Q.P.marked x).subset_space hp)

omit [Countable Y] in
lemma localOriginalArea_ballWindow
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (c : FinProbability Y) (J : Set ℝ) (x : X) :
    localOriginalArea Γ Q σ j (ballWindow K Γ hΓ (n := n) c J) x =
      localOriginalArea Γ Q σ j (centerDistance Γ hΓ K n c ⁻¹' J) x := by
  unfold localOriginalArea
  congr 2
  ext p
  simp only [ballWindow,Set.mem_inter_iff]
  constructor
  · tauto
  · rintro ⟨hp,hi,hr⟩
    exact ⟨hp,hi,original_marked_subset_space K Q x hp,hr⟩

omit [Countable Y] in
include hact hi in
lemma replacement_ballWindow (P Z : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (c : FinProbability Y) (B : Set X) (t : ℝ) (x : X) :
    Cuts.replacementSet (P.P.val x) (Z.P.val x)
      (fun i : H×Unit => {v | centerDistance Γ hΓ K n (i.1•c) v<t})
      (fun i : H×Unit => {v | centerDistance Γ hΓ K n (i.1•c) v=t})
      (fun i : H×Unit => (fun x=>i.1⁻¹•x)⁻¹' B) x =
    (Z.P.val x \ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c (Iio t)) h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c {t}) h x) := by
  have hw (J : Set ℝ) (p : Y →₀ ℝ)
      (hp : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      p∈Cuts.activatedUnion (fun i : H×Unit => centerDistance Γ hΓ K n (i.1•c) ⁻¹' J)
        (fun i : H×Unit => (fun x=>i.1⁻¹•x)⁻¹' B) x ↔
      p∈⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c J) h x := by
    simp only [Cuts.activatedUnion,activeWindow,ballWindow_push K hact Γ hΓ hi n,
      Set.mem_iUnion,Prod.exists,Set.mem_preimage]
    constructor
    · rintro ⟨h,u,hh⟩
      refine ⟨h,?_⟩
      split_ifs at hh ⊢ with hx
      · exact ⟨hp,hh⟩
      · exact hh
    · rintro ⟨h,hh⟩
      refine ⟨h,(),?_⟩
      split_ifs at hh ⊢ with hx
      · exact hh.2
      · exact hh
  ext p
  simp only [Cuts.replacementSet,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
  constructor
  · rintro (⟨hz,hzout⟩ | ⟨hp,hpin⟩)
    · exact Or.inl ⟨hz,fun hh=>hzout ((hw (Iio t) p (original_marked_subset_space K Z x hz)).mpr hh)⟩
    · exact Or.inr ⟨hp,(hw {t} p (original_marked_subset_space K P x hp)).mp hpin⟩
  · rintro (⟨hz,hzout⟩ | ⟨hp,hpin⟩)
    · exact Or.inl ⟨hz,fun hh=>hzout ((hw (Iio t) p (original_marked_subset_space K Z x hz)).mp hh)⟩
    · exact Or.inr ⟨hp,(hw {t} p (original_marked_subset_space K P x hp)).mpr hpin⟩

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable {n : ℕ} (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK hact hi in

theorem ae_exists_ball_step {R : ℝ} (hR : 0<R)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B) :
    ∀ᵐ t : ℝ, 0<t → t≤R →
      ∃ A : OrbitForms.EquivariantStep (realizationDistance Γ hΓ K n) R (Q.pair (j+1)),
        ∀ x,A.result.P.val x =
          ((Q.pair j).P.val x \ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c (Iio t)) h x) ∪
          ((Q.pair (j+1)).P.val x ∩ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c {t}) h x) := by
  let := graphMetric Γ hΓ
  let S (_ : Unit) := ballSupport Γ c n R
  let d := BallOrbitForms.data S (fun _ : Unit=>c) n
  have hfaces : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces.Countable :=
    (Set.to_countable K.faces).image (fun s=>simplexVertices s)
  have hb := (Q.pair (j+1)).T.countable_exceptional_levels hfaces (fun k : H×BallOrbitForms.Index S => fun v=>OrbitForms.form d k v)
  have hae : ∀ᵐ t : ℝ,∀ x F,F∈((Q.pair (j+1)).T.val x).complex.faces →
      ∀ k y,y∈F → OrbitForms.form d k y≠t := ae_iff.mpr (hb.measure_zero volume)
  filter_upwards [hae] with t htgen
  intro ht htR
  obtain ⟨A,hA,hZ,hval⟩ := exists_ball_replacement Γ hΓ rfl hn K hK hact hi
    (Q.pair (j+1)).T (Q.pair (j+1)).P hR ht htR (Q.admissibleStep hj)
    (Q.pair j).equivariant (Q.pair (j+1)).markedEquivariant (Q.pair j).markedEquivariant
    (fun _ :Unit=>c) (fun _ :Unit=>B) (fun _=>hB) (by
      intro x F hF k
      obtain ⟨v,hv⟩ := ((Q.pair (j+1)).T.val x).complex.nonempty_of_mem_faces hF
      exact ⟨v,hv,htgen x F hF k v hv⟩)
  refine ⟨⟨A,hA,hZ⟩,fun x=>?_⟩
  change A.zero.val x=_
  rw [hval x]
  exact replacement_ballWindow K hact Γ hΓ hi n (Q.pair (j+1)) (Q.pair j) c B t x

end Sparse.GraphGeometry

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

omit [DecidableEq Y] [TopologicalSpace X] in
lemma activeWindow_mono {U V : Set (Y →₀ ℝ)} (hUV : U⊆V) (B : Set X) (h : H) (x : X) :
    activeWindow B U h x⊆activeWindow B V h x := by
  unfold activeWindow
  split_ifs
  · exact Set.image_mono hUV
  · exact Set.Subset.refl _

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})

local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ

variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem ae_open_ball_comparison (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x))) :
    ∀ᵐ t : ℝ,0<t → t≤R →
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair j) σ j
        {v | centerDistance Γ hΓ K n c v<t} x ∂μ) ≤
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair (j+1)) σ j
        {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  have hKn (s) (hs : s∈K.faces) : s.card≤n+1 := by
    obtain ⟨τ,hτ,hst,hcard,-⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hcard
  have hconn (σ : SourceTop K n) : (Γ.induce (σ.val : Set Y)).Connected := by
    obtain ⟨τ,hτ,hst,hcard,hct⟩ := hK σ.val σ.property.1
    have he : σ.val=τ := Finset.eq_of_subset_of_card_le hst (by rw [hcard,σ.property.2])
    exact he.symm ▸ hct
  let reps := OrbitAreas.orbitReps (H := H) (T := SourceTop K n)
  have hfinite := normalizedArea_filtration_lt_top Γ μ reps (fun σ _=>hconn σ) Q hKn hj.le
  filter_upwards [ae_exists_ball_step K hact.out Γ hΓ hi hn hK hR Q hj c B hB] with t htgen
  intro ht htR
  obtain ⟨A,hnew⟩ := htgen ht htR
  have hfinite' := OrbitForms.normalizedArea_step_lt_top Γ μ reps (fun σ _=>hconn σ) Q hKn hj A
  have hgain := normalizedArea_surgery_gain (n := n) Γ hΓaut (Q.pair (j+1)) (Q.pair j) A.result
    μ hμ j B hB.isOpen.measurableSet
    (ballWindow K Γ hΓ (n := n) c (Iio t)) (ballWindow K Γ hΓ (n := n) c {t})
    (by
      intro x h
      unfold activeWindow
      split_ifs
      · rw [ballWindow_push K hact.out Γ hΓ hi n]
        exact measurable_ballWindow K Γ hΓ hn hK (h•c) (Iio t) measurableSet_Iio
      · exact MeasurableSet.empty)
    (by
      intro x h k hhk
      have hsub : ballWindow K Γ hΓ (n := n) c (Iio t)⊆ballWindow K Γ hΓ (n := n) c (Iic R) :=
        fun _ hp=>⟨hp.1,hp.2.le.trans htR⟩
      exact (hdisj x hhk).mono (activeWindow_mono hsub B h x) (activeWindow_mono hsub B k x)) hnew
  have hle := nearMinimum_local_comparison hfinite
    (ennreal_nearMinimum_of_real hfinite.ne hfinite'.ne hε (hmin j hj A)) hgain
  simpa only [localOriginalArea_ballWindow,Set.preimage,Set.mem_Iio,Set.mem_singleton_iff] using hle

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in

lemma ae_local_ball_closed_eq_open
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (j : ℕ) (c : FinProbability Y) :
    ∀ᵐ t : ℝ,∀ (σ : SourceTop K n) x,
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤t} x =
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v<t} x := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  let : Countable (SourceTop K n) :=
    inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
  apply ae_all_iff.mpr
  intro σ
  let f (x : X) := Q.P.val x∩sourceInterior σ.val
  have hf : IsLocallyConstant f := Q.P.localConstancy_inter (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩ _ intrinsicInterior_subset
  let : Finite (Set.range f) := hf.range_finite.to_subtype
  let m := originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
  have ha (A : Set.range f) : ∀ᵐ t : ℝ,
      m (A.val∩{v | centerDistance Γ hΓ K n c v≤t}) =
      m (A.val∩{v | centerDistance Γ hΓ K n c v<t}) := by
    exact ae_iff.mpr ((countable_ball_area_jumps m A.val
      (measurable_centerDistance K Γ hΓ hn hK c)).measure_zero volume)
  filter_upwards [ae_all_iff.mpr ha] with t ht
  intro x
  simpa only [localOriginalArea_eq_measure,f,m] using ht ⟨f x,Set.mem_range_self x⟩

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

def ballMass
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (j : ℕ) (c : FinProbability Y) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Q σ j
    {v | centerDistance Γ hΓ K n c v≤t} x ∂μ

lemma ballMass_mono
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (j : ℕ) (c : FinProbability Y) :
    Monotone (ballMass (n := n) Γ hΓ Q μ B j c) := by
  intro s t hst
  unfold ballMass
  apply lintegral_mono
  intro x
  apply ENNReal.tsum_le_tsum
  intro σ
  simp only [localOriginalArea_eq_measure]
  exact measure_mono fun _ hp=>⟨hp.1,hp.2.trans hst⟩

end Sparse.GraphGeometry

end BassTrace

end

end OAI
