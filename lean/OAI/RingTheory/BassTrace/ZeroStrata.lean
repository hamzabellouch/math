import OAI.RingTheory.BassTrace.BallMass

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {Y : Type*} [DecidableEq Y]

lemma affineSpan_simplex_constraints (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈affineSpan ℝ (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))) :
    coefficientSum p=1 ∧ ∀ y∉s,p y=0 := by
  rw [affineSpan_convexHull] at hp
  refine affineSpan_induction (p := fun p : Y →₀ ℝ=>
    coefficientSum p=1 ∧ ∀ y∉s,p y=0) hp ?_ ?_
  · intro q hq
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨by simp,?_⟩
    intro z hz
    simp [show y≠z from fun he=>hz (he ▸ hy)]
  · intro a u v w hu hv hw
    change coefficientSum (a•(u-v)+w)=1 ∧ ∀ y∉s,(a•(u-v)+w) y=0
    constructor
    · simp [map_add,map_smul,map_sub,hu.1,hv.1,hw.1]
    · intro y hy
      simp [hu.2 y hy,hv.2 y hy,hw.2 y hy]

lemma mem_sourceInterior_of_positive (s : Finset Y) (p : FinProbability Y)
    (hs : p.coeff.support⊆s) (hp : ∀ y∈s,0<p.coeff y) :
    p.coeff∈sourceInterior s := by
  let C := convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))
  have hC : C=probabilitySet s := by
    dsimp [C,simplexVertices]
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet]
  have hpC : p.coeff∈C := hC ▸ ⟨p.nonneg,by simpa using p.total,hs⟩
  let q : affineSpan ℝ C := ⟨p.coeff,(subset_affineSpan ℝ C hpC)⟩
  let U : Set (affineSpan ℝ C) := ⋂ y : s,
    (fun v : affineSpan ℝ C=>v.val y.val) ⁻¹' Ioi 0
  have hU : IsOpen U := isOpen_iInter_of_finite fun y=>isOpen_Ioi.preimage
    ((coordinateCLM y.val).continuous.comp continuous_subtype_val)
  have hq : q∈U := Set.mem_iInter.mpr fun y=>hp y.val y.property
  have hUC : U⊆(Subtype.val ⁻¹' C) := by
    intro v hv
    have ha := affineSpan_simplex_constraints s v.property
    change v.val∈C
    apply (Set.ext_iff.mp hC v.val).mpr
    refine ⟨?_,ha.1,?_⟩
    · intro y
      by_cases hy : y∈s
      · exact (Set.mem_iInter.mp hv ⟨y,hy⟩).le
      · rw [ha.2 y hy]
    · intro y hy
      by_contra h
      exact Finsupp.mem_support_iff.mp hy (ha.2 y h)
  exact ⟨q,mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hq) hUC),rfl⟩

lemma probability_mem_own_sourceInterior (p : FinProbability Y) :
    p.coeff∈sourceInterior p.coeff.support :=
  mem_sourceInterior_of_positive _ p subset_rfl fun y hy=>
    lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy))

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

open GraphGeometry

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

include hK in
lemma zero_mem_sourceTop_interior (x : X) {v : Y →₀ ℝ}
    (hv : v∈(Q.pair 0).P.val x) : ∃ σ : SourceTop K n,v∈sourceInterior σ.val := by
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hv
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hs := pointProbability_face K ⟨v,hvK⟩
  have hf : simplexVertices p.coeff.support∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := ⟨_,hs,rfl⟩
  have hmem : v∈convexHull ℝ (simplexVertices p.coeff.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  have hl := (Q.point x).card_lower_of_mem_zero (i := n) le_rfl hv
    (show simplexVertices p.coeff.support∈((Q.point x).T n).faces by
      change _∈((Q.pair n).T.val x).complex.faces
      rw [Q.top]; exact hf)
    (show convexHull ℝ (simplexVertices p.coeff.support : Set (Y →₀ ℝ))⊆(Q.point x).Z n by
      change _⊆(Q.pair n).P.val x
      rw [Q.top_space]
      exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space hf) hmem
  have hlow : n+1≤p.coeff.support.card := hl.trans Finset.card_image_le
  have hcard : p.coeff.support.card=n+1 := le_antisymm (hK _ hs) hlow
  exact ⟨⟨p.coeff.support,hs,hcard⟩,hp ▸ probability_mem_own_sourceInterior p⟩

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma count_chart_image {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (E : Set (Y →₀ ℝ)) (hE : ∀ p∈E,p.support⊆s) :
    Measure.count (simplexCoordinates s hs '' E)=Measure.count E := by
  have he : simplexEmbed s hs '' (simplexCoordinates s hs '' E)=E := by
    ext p
    constructor
    · rintro ⟨q,⟨v,hv,rfl⟩,rfl⟩
      rwa [simplexEmbed_coordinates s hs (hE v hv)]
    · intro hp
      exact ⟨simplexCoordinates s hs p,⟨p,hp,rfl⟩,simplexEmbed_coordinates s hs (hE p hp)⟩
  rw [← Measure.count_injective_image (simplexEmbed_injective s hs),he]

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})

include hK in
lemma zero_count_ball_le (x : X) (c : FinProbability Y) (b : ℝ) :
    Measure.count ((Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c v≤b})≤
      ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c b x := by
  have hd : ∀ s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨τ,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hh : (Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c v≤b}⊆
      ⋃ σ : SourceTop K n,(Q.pair 0).P.val x∩
        (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b}) := by
    rintro v ⟨hv,hb⟩
    obtain ⟨σ,hσ⟩ := zero_mem_sourceTop_interior Q hd x hv
    exact Set.mem_iUnion.mpr ⟨σ,hv,hσ,hb⟩
  calc
    _ ≤ _ := measure_mono hh
    _ ≤ ∑' σ : SourceTop K n,Measure.count ((Q.pair 0).P.val x∩
        (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b})) := measure_iUnion_le _
    _ = _ := by
      unfold ballIntegrand
      apply tsum_congr
      intro σ
      rw [localOriginalArea_zero_eq_count Γ hK,count_chart_image]
      exact fun p hp=>support_of_mem_sourceInterior _ hp.2.1

end

section

variable {Y : Type*} [DecidableEq Y]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected) (hn : 0<n)

include hn in
lemma exists_finite_simplex_ball_cover (σ : SourceTop K n) {r : ℝ} (hr : 0<r) :
    ∃ C : Finset (FinProbability Y),
      (∀ c∈C,c.coeff.support⊆σ.val) ∧
      ∀ v∈convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)),
        ∃ c∈C,centerDistance Γ hΓ K n c v≤r := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let S : Set (FinProbability Y) := {p | p.coeff.support⊆σ.val}
  have hSc : IsCompact S := isCompact_probability_simplex σ.val n hn (graphMetric_discrete Γ hΓ)
  have hcover : S⊆⋃ p∈S,Metric.ball p r := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨p,hp,Metric.mem_ball_self hr⟩
  obtain ⟨T,hTS,hT,hcoverT⟩ := hSc.elim_finite_subcover_image
    (fun _ _=>Metric.isOpen_ball) hcover
  refine ⟨hT.toFinset,fun c hc=>hTS (hT.mem_toFinset.mp hc),?_⟩
  intro v hv
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      ⟨σ.val,σ.property.1,rfl⟩ hv
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hps : p.coeff.support⊆σ.val := by
    have hh := hv
    rw [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet,← hp] at hh
    exact hh.2.2
  obtain ⟨c,hc,hpc⟩ := Set.mem_iUnion₂.mp (hcoverT hps)
  refine ⟨c,hT.mem_toFinset.mpr hc,?_⟩
  rw [← hp,centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩)]
  exact (FinProbability.rho_comm n p c) ▸ hpc.le

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
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

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

include hi hn hK hΓaut in
lemma expected_zero_count_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n) (σ : SourceTop K n) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2)
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (∫⁻ x,Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))) ∂μ).toReal≤C*ε := by
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp : 0<4*(D : ℝ)^2 := by positivity
  have hrp : 0<2*(D : ℝ)^2 := by positivity
  have hrR : 2*(D : ℝ)^2≤4*(D : ℝ)^2 := by nlinarith [sq_nonneg (D : ℝ)]
  obtain ⟨T,hT,hcover⟩ := exists_finite_simplex_ball_cover Γ hΓ hn σ hrp
  have hc : ∀ c∈T,c.coeff.support.card≤n+1 := fun c hc=>
    (Finset.card_le_card (hT c hc)).trans_eq σ.property.2
  have hh : ∀ c : T,∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2)
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal≤C*ε :=
    fun c=>global_zero_ball_mass_bound Γ hΓ hΓaut hi hn hK μ hμ hRp c.val
      (hc c.val c.property) _ hrp.le hrR D hD hdeg (ballVolume_strict_margin D n hD hlarge)
  choose C hC hbound using hh
  refine ⟨∑ c : T,C c,Finset.sum_nonneg (fun c _=>hC c),?_⟩
  intro ε hε Q hmin
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hf c : ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c (2*(D : ℝ)^2)<⊤ :=
    ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ univ 0 hdim c _ hrp.le
  have hp x : Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))≤
      ∑ c : T,ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c.val (2*(D : ℝ)^2) x := by
    have hsub : (Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))⊆
        ⋃ c : T,(Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c.val v≤2*(D : ℝ)^2} := by
      rintro v ⟨hv,hs⟩
      obtain ⟨c,hc,hcv⟩ := hcover v hs
      exact Set.mem_iUnion.mpr ⟨⟨c,hc⟩,hv,hcv⟩
    exact (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun c _=>zero_count_ball_le Γ hΓ hK Q x c.val _))
  have hint : (∫⁻ x,Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))) ∂μ)≤
      ∑ c : T,ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2) := by
    apply (lintegral_mono hp).trans_eq
    rw [lintegral_finsetSum _ (fun c _=>(ballIntegrand_locallyConstant Γ hΓ hn hK
      (Q.pair 0) 0 c.val _ hrp.le).continuous.measurable)]
    apply Finset.sum_congr rfl
    intro c _
    simp only [ballMass,Measure.restrict_univ,ballIntegrand]
  calc
    _ ≤ (∑ c : T,ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal :=
      ENNReal.toReal_mono (by simp [ne_of_lt (hf _)]) hint
    _ = ∑ c : T,(ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal :=
      ENNReal.toReal_sum (fun c _=>(hf c.val).ne)
    _ ≤ ∑ c : T,C c*ε := Finset.sum_le_sum fun c _=>hbound c ε hε Q hmin
    _ = (∑ c : T,C c)*ε := (Finset.sum_mul ..).symm

end Sparse.GraphGeometry

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

include hK in
lemma zero_inter_simplex_finite (σ : SourceTop K n) (x : X) :
    ((Q.pair 0).P.val x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))).Finite := by
  let L := Cuts.restrictComplex (Cuts.geometricRestriction ((Q.pair 0).T.val x).complex
    ((Q.pair 0).P.val x)) (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))
  have hs : simplexVertices σ.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces :=
    ⟨σ.val,σ.property.1,rfl⟩
  have hfin : L.faces.Finite := (((Q.pair 0).T.val x).finite _ hs).subset
    (fun t ht=>⟨ht.1.1,ht.2⟩)
  have hf : (⋃ t∈L.faces,(t : Set (Y →₀ ℝ))).Finite :=
    hfin.biUnion (fun t _=>t.finite_toSet)
  apply hf.subset
  intro v hv
  have hvL : v∈L.space := by
    change v∈(Cuts.restrictComplex (Cuts.geometricRestriction ((Q.pair 0).T.val x).complex
      ((Q.pair 0).P.val x)) (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).space
    rw [(Q.pair 0).P.trace_space _ hs]
    exact hv
  obtain ⟨t,ht,hvt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hvL
  have hc : t.card≤0+1 := (Q.point x).dimension_bound
    (by rintro _ ⟨s,hs,rfl⟩; exact Finset.card_image_le.trans (hK s hs))
    (Nat.zero_le n) ht.1.1 ht.1.2
  obtain ⟨w,rfl⟩ := Finset.card_eq_one.mp (by
    exact Nat.le_antisymm hc (L.nonempty_of_mem_faces ht).card_pos)
  have he : v=w := by simpa using hvt
  exact Set.mem_iUnion₂.mpr ⟨{w},ht,by simp [he]⟩

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
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

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

include hi hn hK hΓaut in

theorem exists_sparse_zero_strata (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n)
    (F : Finset (Finset Y)) (hF : ∀ s∈F,s∈K.faces)
    (hrep : ∀ s∈K.faces,∃ h : H,∃ τ∈F,s=τ.map (MulAction.toPerm h).toEmbedding) :
    ∃ C : SourceTop K n → ℝ,(∀ σ,0≤C σ) ∧ ∀ ε : ℝ,0<ε →
      ∃ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      ∀ σ : SourceTop K n,
        (∫ x,(Measure.count ((Q.pair 0).P.val x∩
          convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε := by
  have hall := expected_zero_count_bound Γ hΓ hΓaut hi hn hK μ hμ D hD hdeg hlarge
  choose C hC hbound using hall
  refine ⟨C,hC,?_⟩
  intro ε hε
  let := graphMetric Γ hΓ
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp : 0<4*(D : ℝ)^2 := by positivity
  obtain ⟨Q,hQ⟩ := exists_normalized_nearMinimal Γ hΓ rfl hn K hK hact.out hi
    F hF hrep μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) hRp hε
  refine ⟨Q,?_⟩
  intro σ
  have hmeas : Measurable (fun x=>Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))) :=
    (((Q.pair 0).P.localConstancy_inter (simplexVertices σ.val) ⟨_,σ.property.1,rfl⟩
      _ subset_rfl).comp (fun A=>Measure.count A)).continuous.measurable
  have hd : ∀ s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨τ,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hfinite' x : Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))<⊤ :=
    Measure.count_apply_lt_top.mpr (zero_inter_simplex_finite Q hd σ x)
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall hfinite')]
  exact hbound σ ε hε.le Q hQ

end Sparse.GraphGeometry

end BassTrace

end

end OAI
