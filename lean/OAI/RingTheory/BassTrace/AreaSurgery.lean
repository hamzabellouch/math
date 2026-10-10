import OAI.RingTheory.BassTrace.OrbitAreas

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal

lemma measure_surgery_countable_gain {E A : Type*} [MeasurableSpace E] [Countable A]
    (μ : Measure E) (P Z : Set E) (U S : A → Set E)
    (hU : ∀ a,MeasurableSet (U a))
    (hd : Pairwise (fun a b => Disjoint (U a) (U b))) :
    μ ((Z \ ⋃ a,U a) ∪ (P ∩ ⋃ a,S a)) + ∑' a,μ (Z ∩ U a) ≤
      μ Z + ∑' a,μ (P ∩ S a) := by
  have hc : μ (Z ∩ ⋃ a,U a)=∑' a,μ (Z∩U a) := by
    calc
      μ (Z ∩ ⋃ a,U a) = (μ.restrict Z) (⋃ a,U a) := by
        rw [Measure.restrict_apply (MeasurableSet.iUnion hU),Set.inter_comm]
      _ = ∑' a,(μ.restrict Z) (U a) := measure_iUnion hd hU
      _ = _ := by
        apply tsum_congr
        intro a
        rw [Measure.restrict_apply (hU a),Set.inter_comm]
  rw [← hc]
  apply (measure_surgery_gain μ P Z _ _ (MeasurableSet.iUnion hU)).trans
  apply add_le_add_right
  rw [Set.inter_iUnion]
  exact measure_iUnion_le _

lemma countable_ball_area_jumps {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (Z : Set E) {f : E → ℝ} (hf : Measurable f) :
    {t : ℝ | μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t})}.Countable := by
  have hh := countable_meas_le_ne_meas_lt (μ.restrict Z) (fun p => (-f p : ℝ))
  have hsub : {t : ℝ | μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t})} ⊆
      Neg.neg ⁻¹' {t : ℝ | (μ.restrict Z) {p | t≤ -f p} ≠
        (μ.restrict Z) {p | t < -f p}} := by
    intro t ht
    change μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t}) at ht
    change (μ.restrict Z) {p | -t≤ -f p} ≠ (μ.restrict Z) {p | -t < -f p}
    simpa only [neg_le_neg_iff,neg_lt_neg_iff,
      Measure.restrict_apply (measurableSet_le hf measurable_const),
      Measure.restrict_apply (measurableSet_lt hf measurable_const),Set.inter_comm] using ht
  exact (hh.preimage neg_injective).mono hsub

lemma nearMinimum_local_comparison {I I' M N ε : ℝ≥0∞}
    (hI : I<∞) (hmin : I≤I'+ε) (hgain : I'+M≤I+N) : M≤N+ε := by
  have hh : I+M≤I+(N+ε) := by
    calc
      I+M ≤ (I'+ε)+M := add_le_add_left hmin M
      _ = (I'+M)+ε := by ac_rfl
      _ ≤ (I+N)+ε := add_le_add_left hgain ε
      _ = I+(N+ε) := by ac_rfl
  exact (ENNReal.add_le_add_iff_left hI.ne).mp hh

lemma normalized_integrated_gain {X T : Type*} [MeasurableSpace X]
    (μ : Measure X) (reps : Finset T) (w : T → ℝ≥0∞)
    (old new removed inserted : T → X → ℝ≥0∞)
    (hnew : ∀ σ∈reps,Measurable (new σ))
    (hold : ∀ σ∈reps,Measurable (old σ))
    (hgain : ∀ σ∈reps, ∀ x,new σ x+removed σ x≤old σ x+inserted σ x) :
    (∑ σ∈reps,w σ*∫⁻ x,new σ x ∂μ) + (∑ σ∈reps,w σ*∫⁻ x,removed σ x ∂μ) ≤
      (∑ σ∈reps,w σ*∫⁻ x,old σ x ∂μ) + (∑ σ∈reps,w σ*∫⁻ x,inserted σ x ∂μ) := by
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ hσ
  rw [← mul_add,← mul_add]
  apply mul_le_mul_right
  rw [← lintegral_add_left (hnew σ hσ) _, ← lintegral_add_left (hold σ hσ) _]
  exact lintegral_mono (hgain σ hσ)

lemma ennreal_nearMinimum_of_real {I I' : ℝ≥0∞} {ε : ℝ}
    (hI : I≠∞) (hI' : I'≠∞) (hε : 0≤ε) (hmin : I.toReal≤I'.toReal+ε) :
    I≤I'+ENNReal.ofReal ε := by
  apply (ENNReal.toReal_le_toReal hI (ENNReal.add_ne_top.mpr ⟨hI',ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hI' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε]
  exact hmin

end

open Finset Set MeasureTheory

open scoped Pointwise Classical BassTrace.Sparse ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

omit hact in
lemma markedPair_image (Q : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (h : H) (x : X) :
    Q.P.val (h • x)=OrbitForms.push h '' Q.P.val x := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨OrbitForms.push h⁻¹ p,?_,?_⟩
    · simpa only [inv_smul_smul] using Q.markedEquivariant h⁻¹ (h • x) p hp
    · simpa only [inv_inv] using OrbitForms.push_inv_push h⁻¹ p
  · rintro _ ⟨p,hp,rfl⟩
    exact Q.markedEquivariant h x p hp

def localOriginalArea (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (x : X) : ℝ≥0∞ :=
  simplexArea (simplexGraph Γ σ.val σ.property.2) j
    (simplexCoordinates σ.val σ.property.2 '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)))

omit hact in
lemma localOriginalArea_locallyConstant (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) :
    IsLocallyConstant (localOriginalArea Γ Q σ j W) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ (Set.inter_subset_left.trans intrinsicInterior_subset) j

include hact in
lemma localOriginalArea_covariant (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (h : H) (x : X) :
    localOriginalArea Γ Q (h • σ) j (OrbitForms.push h '' W) (h • x) =
      localOriginalArea Γ Q σ j W x := by
  have hi : sourceInterior (h • σ).val=OrbitForms.push h '' sourceInterior σ.val := by
    change sourceInterior (h • σ.val)=_
    rw [smul_finset_eq_map]
    exact sourceInterior_relabel (MulAction.toPerm h) σ.val
  have he : Q.P.val (h • x) ∩ (sourceInterior (h • σ).val ∩ OrbitForms.push h '' W) =
      OrbitForms.push h '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)) := by
    rw [markedPair_image Q h x,hi,Set.image_inter (OrbitForms.push h).injective,
      Set.image_inter (OrbitForms.push h).injective]
  unfold localOriginalArea
  rw [he]
  change simplexArea (simplexGraph Γ (h • σ.val) _) j
    (simplexCoordinates (h • σ.val) _ ''
      (OrbitForms.push h '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)))) = _
  simpa only [← smul_finset_eq_map,OrbitForms.push] using originalSimplexArea_relabel (MulAction.toPerm h) σ.val σ.property.2 Γ Γ
    (hΓ h) j _ (fun _ hp => intrinsicInterior_subset hp.2.1)

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

omit hact in
lemma localOriginalArea_eq_measure (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ j W x =
      originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
        ((Q.P.val x ∩ sourceInterior σ.val) ∩ W) := by
  rw [originalAreaMeasure_apply _ _ _ _ _
    (fun p hp => support_of_mem_sourceInterior σ.val hp.1.2),Set.inter_assoc]
  rfl

omit hact in
lemma localOriginalArea_empty (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (x : X) :
    localOriginalArea Γ Q σ j ∅ x=0 := by
  rw [localOriginalArea_eq_measure]
  simp

def activeWindow (B : Set X) (W : Set (Y →₀ ℝ)) (h : H) (x : X) : Set (Y →₀ ℝ) :=
  if h⁻¹ • x∈B then OrbitForms.push h '' W else ∅

include hact in
lemma active_area_eq_orbitActivated (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (B : Set X) (W : Set (Y →₀ ℝ)) (h : H) (x : X) :
    localOriginalArea Γ Q σ j (activeWindow B W h x) x =
      OrbitAreas.orbitActivated B (fun σ x => localOriginalArea Γ Q σ j W x) σ h x := by
  by_cases hx : h⁻¹ • x∈B
  · simp only [activeWindow,hx,ite_eq_left,OrbitAreas.orbitActivated,Set.indicator_of_mem hx]
    simpa only [smul_inv_smul] using
      localOriginalArea_covariant Γ hΓ Q (h⁻¹ • σ) j W h (h⁻¹ • x)
  · simp only [activeWindow,hx,OrbitAreas.orbitActivated,Set.indicator_of_notMem hx]
    exact localOriginalArea_empty Γ Q σ j x

omit hact in
lemma localArea_surgery_countable_gain [Countable H] (Γ : SimpleGraph Y)
    (P Z Z' : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (B : Set X) (U S : Set (Y →₀ ℝ)) (x : X)
    (hU : ∀ h : H, @MeasurableSet _ (borel (Y →₀ ℝ)) (activeWindow B U h x))
    (hd : Pairwise (fun h k : H => Disjoint (activeWindow B U h x) (activeWindow B U k x)))
    (hnew : Z'.P.val x = (Z.P.val x \ ⋃ h : H,activeWindow B U h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B S h x)) :
    originalArea Γ Z' σ j x + ∑' h : H,localOriginalArea Γ Z σ j (activeWindow B U h x) x ≤
      originalArea Γ Z σ j x + ∑' h : H,localOriginalArea Γ P σ j (activeWindow B S h x) x := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  simp only [originalArea_eq_measure,localOriginalArea_eq_measure]
  have he : Z'.P.val x ∩ sourceInterior σ.val =
      ((Z.P.val x ∩ sourceInterior σ.val) \ ⋃ h : H,activeWindow B U h x) ∪
      ((P.P.val x ∩ sourceInterior σ.val) ∩ ⋃ h : H,activeWindow B S h x) := by
    rw [hnew]
    ext p
    simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_sdiff]
    tauto
  rw [he]
  exact measure_surgery_countable_gain _ _ _ _ _ hU hd

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [Countable H] [Countable Y] [IsCancelSMul H Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})

local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ

variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

lemma weighted_activated_originalArea (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (j : ℕ) (B : Set X) (hB : MeasurableSet B) (W : Set (Y →₀ ℝ)) :
    (∑ σ∈OrbitAreas.orbitReps (H := H) (T := SourceTop K n),
      (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹ *
        ∫⁻ x,∑' h : H,OrbitAreas.orbitActivated B
          (fun σ x => localOriginalArea Γ Q σ j W x) σ h x ∂μ) =
      ∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Q σ j W x ∂μ := by
  have hs (σ : SourceTop K n) : MulAction.stabilizer H σ.val=MulAction.stabilizer H σ :=
    (sourceTop_stabilizer_eq K n hact.out σ).symm
  simp_rw [hs]
  rw [OrbitAreas.sum_orbitReps]
  exact OrbitAreas.normalized_activated_integral μ hμ B hB _
    (fun σ => (localOriginalArea_locallyConstant Γ Q σ j W).continuous.measurable)

lemma normalizedArea_surgery_gain (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (P Z Z' : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (j : ℕ) (B : Set X) (hB : MeasurableSet B) (U S : Set (Y →₀ ℝ))
    (hU : ∀ (x : X) (h : H), @MeasurableSet _ (borel (Y →₀ ℝ)) (activeWindow B U h x))
    (hd : ∀ x, Pairwise (fun h k : H => Disjoint (activeWindow B U h x) (activeWindow B U k x)))
    (hnew : ∀ x,Z'.P.val x = (Z.P.val x \ ⋃ h : H,activeWindow B U h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B S h x)) :
    normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) Z' j +
        (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Z σ j U x ∂μ) ≤
      normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) Z j +
        (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ P σ j S x ∂μ) := by
  have hg := normalized_integrated_gain μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n))
    (fun σ => (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹)
    (fun σ x => originalArea Γ Z σ j x) (fun σ x => originalArea Γ Z' σ j x)
    (fun σ x => ∑' h : H,OrbitAreas.orbitActivated B
      (fun σ x => localOriginalArea Γ Z σ j U x) σ h x)
    (fun σ x => ∑' h : H,OrbitAreas.orbitActivated B
      (fun σ x => localOriginalArea Γ P σ j S x) σ h x)
    (fun σ _ => (originalArea_locallyConstant Γ Z' σ j).continuous.measurable)
    (fun σ _ => (originalArea_locallyConstant Γ Z σ j).continuous.measurable)
    (fun σ _ x => by
      simp_rw [← active_area_eq_orbitActivated Γ hΓ]
      exact localArea_surgery_countable_gain Γ P Z Z' σ j B U S x (hU x) (hd x) (hnew x))
  rw [weighted_activated_originalArea Γ Z μ hμ j B hB U,
    weighted_activated_originalArea Γ P μ hμ j B hB S] at hg
  exact hg

end BassTrace.Sparse

end

end OAI
