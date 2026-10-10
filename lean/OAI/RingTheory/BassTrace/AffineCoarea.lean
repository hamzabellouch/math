import OAI.RingTheory.BassTrace.AreaSurgery

namespace OAI

/-! Affine coarea from product measure and one-dimensional Lebesgue scaling. The transverse
measure may be s-finite; orthonormal coordinates specialize this to affine polyhedral area. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

lemma lintegral_affine_change (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    (∫⁻ t : ℝ, f t) = ENNReal.ofReal |a| * ∫⁻ s : ℝ, f (a * s + c) := by
  calc
    (∫⁻ t : ℝ, f t) = ∫⁻ t : ℝ, f (t + c) :=
      (lintegral_add_right_eq_self f c).symm
    _ = ENNReal.ofReal |a| * ∫⁻ s : ℝ, f (a * s + c) := by
      conv_lhs => rw [← Real.smul_map_volume_mul_left ha]
      have hh : Measurable (fun x : ℝ => f (x + c)) :=
        hf.comp (measurable_id.add_const c)
      rw [lintegral_smul_measure, lintegral_map hh (measurable_const_mul a)]
      rfl

section Product

variable {F : Type*} [MeasurableSpace F] (ν : Measure F) [SFinite ν]

def productSlice (Q : Set (ℝ × F)) (a c t : ℝ) : Set F :=
  {z | ((t - c) / a, z) ∈ Q}

lemma measurable_productSlice {Q : Set (ℝ × F)} (hQ : MeasurableSet Q) (a c : ℝ) :
    Measurable (fun t : ℝ => ν (productSlice Q a c t)) := by
  exact (measurable_measure_prodMk_left hQ).comp ((measurable_id.sub_const c).div_const a)

lemma affine_product_coarea {Q : Set (ℝ × F)} (hQ : MeasurableSet Q)
    {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, ν (productSlice Q a c t)) =
      ENNReal.ofReal a * (volume.prod ν)
        (Q ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) := by
  classical
  let g : ℝ → ℝ≥0∞ := (Ioo r b).indicator (fun t => ν (productSlice Q a c t))
  have hg : Measurable g := (measurable_productSlice ν hQ a c).indicator measurableSet_Ioo
  have hs : MeasurableSet (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) := by
    exact hQ.inter ((measurableSet_lt measurable_const
      ((measurable_fst.const_mul a).add_const c)).inter
      (measurableSet_lt ((measurable_fst.const_mul a).add_const c) measurable_const))
  rw [← lintegral_indicator measurableSet_Ioo]
  change (∫⁻ t, g t) = _
  rw [lintegral_affine_change g hg (ne_of_gt ha) c, abs_of_pos ha, Measure.prod_apply hs]
  congr 1
  apply lintegral_congr
  intro s
  have he : (a * s + c - c) / a = s := by field_simp; ring
  by_cases h : r < a * s + c ∧ a * s + c < b
  · have hset : Prod.mk s ⁻¹' (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) =
        {z | (s,z) ∈ Q} := by ext z; simp [h]
    have hmem : a * s + c ∈ Ioo r b := h
    simp only [g, Set.indicator_of_mem hmem, productSlice, he, hset]
  · have hset : Prod.mk s ⁻¹' (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) = ∅ := by
      ext z; simp [h]
    have hmem : a * s + c ∉ Ioo r b := h
    simp only [g, Set.indicator_of_notMem hmem, hset, measure_empty]

lemma affine_product_coarea_le {Q : Set (ℝ × F)} (hQ : MeasurableSet Q)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, ν (productSlice Q a c t)) ≤
      (volume.prod ν) (Q ∩ {p | a * p.1 + c ≤ b}) := by
  rw [affine_product_coarea ν hQ ha]
  calc
    _ ≤ 1 * (volume.prod ν) (Q ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) :=
      by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal ha1
    _ ≤ _ := by
      rw [one_mul]
      exact measure_mono (fun p hp => ⟨hp.1, hp.2.2.le⟩)

end Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped InnerProductSpace

noncomputable def normalParamIsometry (u : E) (hu : ‖u‖ = 1) :
    WithLp 2 (ℝ × (ℝ ∙ u)ᗮ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.toSpanUnitSingleton u hu)
    (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ)).trans
    (ℝ ∙ u).orthogonalDecomposition.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalParamIsometry_apply (u : E) (hu : ‖u‖ = 1)
    (p : ℝ × (ℝ ∙ u)ᗮ) :
    normalParamIsometry u hu (WithLp.toLp 2 p) = p.1 • u + (p.2 : E) := by
  simp [normalParamIsometry]

lemma normalParam_measurePreserving (u : E) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun p : ℝ × (ℝ ∙ u)ᗮ => p.1 • u + (p.2 : E))
      (volume.prod volume) volume := by
  have h := (normalParamIsometry u hu).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (ℝ ∙ u)ᗮ)
  convert! h using 1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma inner_normalParam (u : E) (hu : ‖u‖ = 1) (p : ℝ × (ℝ ∙ u)ᗮ) :
    ⟪u, p.1 • u + (p.2 : E)⟫_ℝ = p.1 := by
  rw [inner_add_right, inner_smul_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property,
    real_inner_self_eq_norm_sq, hu]
  ring

noncomputable def euclideanSliceArea (Q : Set E) (u : E) (a c t : ℝ) : ℝ≥0∞ :=
  volume {z : (ℝ ∙ u)ᗮ | ((t - c) / a) • u + (z : E) ∈ Q}

lemma euclidean_affine_coarea {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, euclideanSliceArea Q u a c t) =
      ENNReal.ofReal a * volume
        (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
  let φ : ℝ × (ℝ ∙ u)ᗮ → E := fun p => p.1 • u + (p.2 : E)
  have hφ : MeasurePreserving φ (volume.prod volume) volume := normalParam_measurePreserving u hu
  have hset : MeasurableSet
      (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
    have hf : Measurable (fun p => a * ⟪u, p⟫_ℝ + c) := by fun_prop
    exact hQ.inter ((measurableSet_lt measurable_const hf).inter
      (measurableSet_lt hf measurable_const))
  have hpre :
      φ ⁻¹' (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) =
      (φ ⁻¹' Q) ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, φ,
      inner_normalParam u hu p]
  calc
    _ = ENNReal.ofReal a * (volume.prod volume)
        ((φ ⁻¹' Q) ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) :=
      affine_product_coarea volume (hφ.measurable hQ) ha c r b
    _ = _ := by rw [← hpre, hφ.measure_preimage hset.nullMeasurableSet]

lemma euclidean_affine_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, euclideanSliceArea Q u a c t) ≤
      volume (Q ∩ {p | a * ⟪u, p⟫_ℝ + c ≤ b}) := by
  rw [euclidean_affine_coarea hQ u hu ha]
  calc
    _ ≤ 1 * volume (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
      gcongr
      simpa using ENNReal.ofReal_le_ofReal ha1
    _ ≤ _ := by
      rw [one_mul]
      exact measure_mono (fun p hp => ⟨hp.1, hp.2.2.le⟩)

end BassTrace.Sparse

end OAI
