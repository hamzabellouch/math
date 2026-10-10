import OAI.RingTheory.BassTrace.AffineCoarea

namespace OAI

/-! Actual Euclidean Hausdorff area, so slices and lower-dimensional interfaces
are measured in the common ambient space, with Mathlib's exact normalization. -/

namespace BassTrace.Sparse

section

open MeasureTheory Set

open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma euclideanArea_zero_finset (s : Finset E) :
    μHE[0] (s : Set E) = s.card := by
  rw [Measure.euclideanHausdorffMeasure_zero,← sum_measure_singleton]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
lemma orthogonal_unit_rank (u : E) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = Module.finrank ℝ E - 1 := by
  have hne : u ≠ 0 := by intro h; simp [h] at hu
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne] at h
  omega

lemma euclideanSliceArea_eq_area (Q : Set E) (u : E) (hu : ‖u‖ = 1)
    {a : ℝ} (ha : a ≠ 0) (c t : ℝ) :
    euclideanSliceArea Q u a c t =
      μHE[Module.finrank ℝ E - 1] (Q ∩ {p | a * ⟪u,p⟫_ℝ + c = t}) := by
  let φ : (ℝ ∙ u)ᗮ → E := fun z => ((t-c)/a) • u + (z : E)
  have hφ : Isometry φ := (isometry_add_left (((t-c)/a) • u)).comp isometry_subtype_coe
  have himage : φ '' {z | φ z ∈ Q} = Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t} := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨hz,?_⟩
      dsimp [φ]
      rw [inner_normalParam u hu (((t-c)/a),z)]
      field_simp
      ring
    · rintro ⟨hp,ht⟩
      change a * ⟪u,p⟫_ℝ+c=t at ht
      have hpu : ⟪u,p⟫_ℝ = (t-c)/a := by apply (eq_div_iff ha).mpr; linarith
      have hz : p - ((t-c)/a) • u ∈ (ℝ ∙ u)ᗮ := by
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,hpu]
        ring
      refine ⟨⟨p - ((t-c)/a) • u,hz⟩,?_,?_⟩
      · dsimp [φ]
        simpa only [add_sub_cancel] using hp
      · dsimp [φ]
        abel
  rw [← himage,hφ.euclideanHausdorffMeasure_image]
  rw [← orthogonal_unit_rank u hu,InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rfl

lemma euclidean_area_affine_coarea {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t})) =
      ENNReal.ofReal a * μHE[Module.finrank ℝ E]
        (Q ∩ {p | r < a * ⟪u,p⟫_ℝ+c ∧ a * ⟪u,p⟫_ℝ+c < b}) := by
  simp_rw [← euclideanSliceArea_eq_area Q u hu ha.ne',
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact euclidean_affine_coarea hQ u hu ha c r b

lemma euclidean_area_affine_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t})) ≤
      μHE[Module.finrank ℝ E] (Q ∩ {p | a * ⟪u,p⟫_ℝ+c ≤ b}) := by
  simp_rw [← euclideanSliceArea_eq_area Q u hu ha.ne',
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact euclidean_affine_coarea_le hQ u hu ha ha1 c r b

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma euclidean_area_constant_slices (Q : Set E) (d : ℕ) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d] (Q ∩ { _p : E | c=t})) = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne c)] with t ht
  have he : { _p : E | c=t} = ∅ := by ext p; simp [Ne.symm ht]
  simp only [he,inter_empty,measure_empty,Pi.zero_apply]

lemma euclidean_area_gradient_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (g : E) (hg : ‖g‖ ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | ⟪g,p⟫_ℝ+c=t})) ≤
      μHE[Module.finrank ℝ E] (Q ∩ {p | ⟪g,p⟫_ℝ+c ≤ b}) := by
  by_cases hzero : g = 0
  · subst g
    simp only [inner_zero_left,zero_add]
    rw [euclidean_area_constant_slices]
    exact bot_le
  · let u := (‖g‖⁻¹ : ℝ) • g
    have ha : 0 < ‖g‖ := norm_pos_iff.mpr hzero
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ha.ne']
    have he (p : E) : ‖g‖ * ⟪u,p⟫_ℝ = ⟪g,p⟫_ℝ := by
      dsimp [u]
      rw [inner_smul_left]
      simp [ha.ne']
    simpa only [he] using euclidean_area_affine_coarea_le hQ u hu ha hg c r b

lemma measurable_euclidean_area_slices {Q : Set E} (hQ : MeasurableSet Q)
    (g : E) (c : ℝ) : Measurable (fun t : ℝ =>
      μHE[Module.finrank ℝ E - 1] (Q ∩ {p | ⟪g,p⟫_ℝ+c=t})) := by
  by_cases hz : g = 0
  · subst g
    have he : (fun t : ℝ => μHE[Module.finrank ℝ E - 1]
        (Q ∩ {p : E | ⟪(0:E),p⟫_ℝ+c=t})) =
        fun t => if t=c then μHE[Module.finrank ℝ E - 1] Q else 0 := by
      funext t
      by_cases ht : t=c
      · simp [ht]
      · simp [ht,Ne.symm ht]
    rw [he]
    exact Measurable.ite (measurableSet_singleton c) measurable_const measurable_const
  · let u := (‖g‖⁻¹ : ℝ) • g
    have ha : 0 < ‖g‖ := norm_pos_iff.mpr hz
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ha.ne']
    have he (p : E) : ‖g‖ * ⟪u,p⟫_ℝ = ⟪g,p⟫_ℝ := by
      dsimp [u]
      rw [inner_smul_left]
      simp [ha.ne']
    let φ : ℝ × (ℝ ∙ u)ᗮ → E := fun p => p.1 • u + (p.2 : E)
    have hφ : Continuous φ := by fun_prop
    have hm := measurable_productSlice (volume : Measure (ℝ ∙ u)ᗮ)
      (hQ.preimage hφ.measurable) ‖g‖ c
    convert hm using 1
    funext t
    change _ = euclideanSliceArea Q u ‖g‖ c t
    rw [euclideanSliceArea_eq_area Q u hu ha.ne']
    simp_rw [he]

lemma euclidean_area_finite_piece_coarea {I : Type*} [Fintype I]
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hdisj : Pairwise fun i j => Disjoint (Q i) (Q j)) (f : E → ℝ)
    (g : I → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : I → ℝ)
    (hbranch : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[Module.finrank ℝ E] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  have hunion (t : ℝ) : ((⋃ i, Q i) ∩ {p | f p=t}) =
      ⋃ i, Q i ∩ {p | ⟪g i,p⟫_ℝ+c i=t} := by
    ext p
    simp only [mem_inter_iff,mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨i,hi⟩,ht⟩
      exact ⟨i,hi,(hbranch i p hi).symm.trans ht⟩
    · rintro ⟨i,hi,ht⟩
      exact ⟨⟨i,hi⟩,(hbranch i p hi).trans ht⟩
  have hble : ((⋃ i, Q i) ∩ {p | f p ≤ b}) =
      ⋃ i, Q i ∩ {p | ⟪g i,p⟫_ℝ+c i ≤ b} := by
    ext p
    simp only [mem_inter_iff,mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨i,hi⟩,ht⟩
      exact ⟨i,hi,(hbranch i p hi) ▸ ht⟩
    · rintro ⟨i,hi,ht⟩
      exact ⟨⟨i,hi⟩,(hbranch i p hi).symm ▸ ht⟩
  calc
    _ ≤ ∫⁻ t in Ioo r b, ∑ i, μHE[Module.finrank ℝ E - 1]
        (Q i ∩ {p | ⟪g i,p⟫_ℝ+c i=t}) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [hunion]
      simpa only [tsum_fintype] using measure_iUnion_le (μ := μHE[Module.finrank ℝ E - 1])
        (fun i => Q i ∩ {p | ⟪g i,p⟫_ℝ+c i=t})
    _ = ∑ i, ∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
        (Q i ∩ {p | ⟪g i,p⟫_ℝ+c i=t}) := by
      apply lintegral_finsetSum
      intro i _
      exact measurable_euclidean_area_slices (hQ i) (g i) (c i)
    _ ≤ ∑ i, μHE[Module.finrank ℝ E] (Q i ∩ {p | ⟪g i,p⟫_ℝ+c i ≤ b}) := by
      apply Finset.sum_le_sum
      intro i _
      exact euclidean_area_gradient_coarea_le (hQ i) (g i) (hg i) (c i) r b
    _ = _ := by
      rw [hble,measure_iUnion]
      · exact (tsum_fintype _).symm
      · intro i j hij
        exact (hdisj hij).mono inter_subset_left inter_subset_left
      · intro i
        exact (hQ i).inter (measurableSet_le (by fun_prop) measurable_const)

end

section

open MeasureTheory Set

open scoped ENNReal InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in

lemma exists_restricted_gradient (e : F →ᵃⁱ[ℝ] E) (g : E) (c : ℝ) :
    ∃ g' : F, ‖g'‖ ≤ ‖g‖ ∧ ∀ x,
      ⟪g,e x⟫_ℝ+c = ⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
  let l : F →L[ℝ] ℝ := (innerSL ℝ g).comp e.linearIsometry.toContinuousLinearMap
  let g' := (InnerProductSpace.toDual ℝ F).symm l
  have hg' (x : F) : ⟪g',x⟫_ℝ = ⟪g,e.linearIsometry x⟫_ℝ :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨g',?_,?_⟩
  · calc ‖g'‖ = ‖l‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map l
         _ ≤ ‖g‖ := by
           apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
           intro x
           change ‖⟪g,e.linearIsometry x⟫_ℝ‖ ≤ ‖g‖*‖x‖
           simpa only [e.linearIsometry.norm_map] using norm_inner_le_norm g (e.linearIsometry x)
  · intro x
    have he : e x = e.linearIsometry x + e 0 := by
      have hh := e.map_vadd (0:F) x
      simpa only [vadd_eq_add,add_zero] using hh
    rw [he,inner_add_right,hg']
    ring

omit [FiniteDimensional ℝ E] in

lemma euclidean_area_embedded_coarea {Q : Set F} (hQ : MeasurableSet Q)
    (e : F →ᵃⁱ[ℝ] E) (f : E → ℝ) (g : F) (hg : ‖g‖ ≤ 1) (c : ℝ)
    (hbranch : ∀ x ∈ Q, f (e x) = ⟪g,x⟫_ℝ+c) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ F - 1]
      ((e '' Q) ∩ {p | f p=t})) ≤
      μHE[Module.finrank ℝ F] ((e '' Q) ∩ {p | f p ≤ b}) := by
  have hslice (t : ℝ) : (e '' Q) ∩ {p | f p=t} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c=t}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,(hbranch x hx).symm.trans ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hbranch x hx).trans ht⟩
  have hball : (e '' Q) ∩ {p | f p ≤ b} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c ≤ b}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,by simpa only [Set.mem_ofPred_eq,← hbranch x hx] using ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,by simpa only [Set.mem_ofPred_eq,hbranch x hx] using ht⟩
  simp_rw [hslice,hball,e.isometry.euclideanHausdorffMeasure_image]
  exact euclidean_area_gradient_coarea_le hQ g hg c r b

omit [FiniteDimensional ℝ E] in
lemma measurable_embedded_slices {Q : Set F} (hQ : MeasurableSet Q)
    (e : F →ᵃⁱ[ℝ] E) (f : E → ℝ) (g : F) (c : ℝ)
    (hbranch : ∀ x ∈ Q, f (e x) = ⟪g,x⟫_ℝ+c) :
    Measurable (fun t : ℝ => μHE[Module.finrank ℝ F - 1]
      ((e '' Q) ∩ {p | f p=t})) := by
  have hslice (t : ℝ) : (e '' Q) ∩ {p | f p=t} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c=t}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,(hbranch x hx).symm.trans ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hbranch x hx).trans ht⟩
  simp_rw [hslice,e.isometry.euclideanHausdorffMeasure_image]
  exact measurable_euclidean_area_slices hQ g c

omit [FiniteDimensional ℝ E] in

lemma euclidean_area_embedded_finite_coarea {I : Type*} [Fintype I]
    (Q : I → Set F) (hQ : ∀ i, MeasurableSet (Q i))
    (e : I → F →ᵃⁱ[ℝ] E)
    (hdisj : Pairwise fun i j => Disjoint (e i '' Q i) (e j '' Q j)) (f : E → ℝ)
    (g : I → F) (hg : ∀ i, ‖g i‖ ≤ 1) (c : I → ℝ)
    (hbranch : ∀ i x, x ∈ Q i → f (e i x) = ⟪g i,x⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ F - 1]
      ((⋃ i, e i '' Q i) ∩ {p | f p=t})) ≤
      μHE[Module.finrank ℝ F] ((⋃ i, e i '' Q i) ∩ {p | f p ≤ b}) := by
  classical
  have hslice (t : ℝ) : ((⋃ i, e i '' Q i) ∩ {p | f p=t}) =
      ⋃ i, (e i '' Q i) ∩ {p | f p=t} := Set.iUnion_inter _ _
  have hball : ((⋃ i, e i '' Q i) ∩ {p | f p ≤ b}) =
      ⋃ i, (e i '' Q i) ∩ {p | f p ≤ b} := Set.iUnion_inter _ _
  have hmeas (i : I) : MeasurableSet ((e i '' Q i) ∩ {p | f p ≤ b}) := by
    have he : (e i '' Q i) ∩ {p | f p ≤ b} =
        e i '' (Q i ∩ {x | ⟪g i,x⟫_ℝ+c i ≤ b}) := by
      ext p
      constructor
      · rintro ⟨⟨x,hx,rfl⟩,ht⟩
        exact ⟨x,⟨hx,by simpa only [Set.mem_ofPred_eq,← hbranch i x hx] using ht⟩,rfl⟩
      · rintro ⟨x,⟨hx,ht⟩,rfl⟩
        exact ⟨⟨x,hx,rfl⟩,by simpa only [Set.mem_ofPred_eq,hbranch i x hx] using ht⟩
    rw [he]
    exact (e i).isometry.isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
      ((hQ i).inter (measurableSet_le (by fun_prop) measurable_const))
  calc
    _ ≤ ∫⁻ t in Ioo r b, ∑ i, μHE[Module.finrank ℝ F - 1]
        ((e i '' Q i) ∩ {p | f p=t}) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [hslice]
      simpa only [tsum_fintype] using measure_iUnion_le (μ := μHE[Module.finrank ℝ F - 1])
        (fun i => (e i '' Q i) ∩ {p | f p=t})
    _ = ∑ i, ∫⁻ t in Ioo r b, μHE[Module.finrank ℝ F - 1]
        ((e i '' Q i) ∩ {p | f p=t}) := by
      apply lintegral_finsetSum
      intro i _
      exact measurable_embedded_slices (hQ i) (e i) f (g i) (c i) (hbranch i)
    _ ≤ ∑ i, μHE[Module.finrank ℝ F] ((e i '' Q i) ∩ {p | f p ≤ b}) := by
      apply Finset.sum_le_sum
      intro i _
      exact euclidean_area_embedded_coarea (hQ i) (e i) f (g i) (hg i) (c i) (hbranch i) r b
    _ = _ := by
      rw [hball,measure_iUnion]
      · exact (tsum_fintype _).symm
      · intro i j hij
        exact (hdisj hij).mono inter_subset_left inter_subset_left
      · exact hmeas

end

open MeasureTheory Set Finset

open scoped ENNReal InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma extend_subspace_dimension (S : Submodule ℝ E) (d : ℕ)
    (hS : Module.finrank ℝ S ≤ d) (hd : d ≤ Module.finrank ℝ E) :
    ∃ W : Submodule ℝ E, S ≤ W ∧ Module.finrank ℝ W = d := by
  induction d, hS using Nat.le_induction with
  | base => exact ⟨S,le_rfl,rfl⟩
  | succ k hk ih =>
    obtain ⟨W,hSW,hW⟩ := ih (by omega)
    obtain ⟨v,hv⟩ := W.exists_of_finrank_lt (by omega)
    have hvW : v ∉ W := by simpa using hv 1 one_ne_zero
    exact ⟨W ⊔ Submodule.span ℝ {v},hSW.trans le_sup_left,by
      rw [Submodule.finrank_sup_span_singleton hvW,hW]⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma simplex_in_affine_isometry (s : Finset E) (hs : s.Nonempty) (d : ℕ)
    (hsd : s.card ≤ d+1) (hd : d ≤ Module.finrank ℝ E) :
    ∃ e : EuclideanSpace ℝ (Fin d) →ᵃⁱ[ℝ] E,
      convexHull ℝ (s : Set E) ⊆ Set.range e := by
  have hc : Fintype.card s = (s.card-1)+1 := by
    rw [Fintype.card_coe]; have := Finset.card_pos.mpr hs; omega
  have hdim := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
  rw [Subtype.range_coe_subtype] at hdim
  obtain ⟨W,hW,hWd⟩ := extend_subspace_dimension (vectorSpan ℝ (s : Set E)) d
    (hdim.trans (by omega)) hd
  obtain ⟨c,hc⟩ := hs
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hWd)
  let l : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] E := W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let e : EuclideanSpace ℝ (Fin d) →ᵃⁱ[ℝ] E :=
    (AffineIsometryEquiv.vaddConst ℝ c).toAffineIsometry.comp l.toAffineIsometry
  refine ⟨e,?_⟩
  intro p hp
  have hspan : p-c ∈ W := by
    apply hW
    have hsp : vectorSpan ℝ (convexHull ℝ (s : Set E)) = vectorSpan ℝ (s : Set E) := by
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    rw [← hsp]
    exact vsub_mem_vectorSpan ℝ hp (subset_convexHull ℝ (s : Set E) hc)
  refine ⟨b.repr ⟨p-c,hspan⟩,?_⟩
  change (↑(b.repr.symm (b.repr ⟨p-c,hspan⟩)) : E)+c=p
  rw [b.repr.symm_apply_apply]
  simp

lemma simplex_piece_coarea (s : Finset E) (d : ℕ) (hsd : s.card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E) {Q : Set E} (hQ : MeasurableSet Q)
    (hQs : Q ⊆ convexHull ℝ (s : Set E)) (f : E → ℝ) (g : E) (hg : ‖g‖ ≤ 1)
    (c : ℝ) (hf : ∀ p ∈ Q, f p=⟪g,p⟫_ℝ+c) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] (Q ∩ {p | f p=t})) ≤
      μHE[d] (Q ∩ {p | f p ≤ b}) := by
  by_cases hs : s.Nonempty
  · obtain ⟨e,he⟩ := simplex_in_affine_isometry s hs d hsd hd
    have hQr : Q ⊆ Set.range e := hQs.trans he
    have heQ : e '' (e ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
    obtain ⟨g',hg',hb⟩ := exists_restricted_gradient e g c
    have hbranch : ∀ x ∈ e ⁻¹' Q, f (e x)=⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
      intro x hx; rw [hf _ hx,hb]
    have hh := euclidean_area_embedded_coarea (e.continuous.measurable hQ)
      e f g' (hg'.trans hg) (⟪g,e 0⟫_ℝ+c) hbranch r b
    simpa only [heQ,finrank_euclideanSpace_fin] using hh
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hQe : Q=∅ := by apply Set.eq_empty_of_subset_empty; simpa [he] using hQs
    simp [hQe]

lemma measurable_simplex_piece_slices (s : Finset E) (d : ℕ) (hsd : s.card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E) {Q : Set E} (hQ : MeasurableSet Q)
    (hQs : Q ⊆ convexHull ℝ (s : Set E)) (f : E → ℝ) (g : E)
    (c : ℝ) (hf : ∀ p ∈ Q, f p=⟪g,p⟫_ℝ+c) :
    Measurable (fun t : ℝ => μHE[d-1] (Q ∩ {p | f p=t})) := by
  by_cases hs : s.Nonempty
  · obtain ⟨e,he⟩ := simplex_in_affine_isometry s hs d hsd hd
    have hQr : Q ⊆ Set.range e := hQs.trans he
    have heQ : e '' (e ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
    obtain ⟨g',_,hb⟩ := exists_restricted_gradient e g c
    have hbranch : ∀ x ∈ e ⁻¹' Q, f (e x)=⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
      intro x hx; rw [hf _ hx,hb]
    have hh := measurable_embedded_slices (e.continuous.measurable hQ)
      e f g' (⟪g,e 0⟫_ℝ+c) hbranch
    simpa only [heQ,finrank_euclideanSpace_fin] using hh
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hQe : Q=∅ := by apply Set.eq_empty_of_subset_empty; simpa [he] using hQs
    simp only [hQe,Set.empty_inter,measure_empty]
    exact measurable_const

lemma finite_polyhedral_coarea {k : ℕ} (s : Fin k → Finset E) (d : ℕ)
    (hs : ∀ i, (s i).card ≤ d+1) (hd : d ≤ Module.finrank ℝ E)
    (Q : Fin k → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E)) (f : E → ℝ)
    (g : Fin k → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : Fin k → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p=⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  let W := disjointed Q
  have hW (i : Fin k) : MeasurableSet (W i) :=
    disjointedRec (fun _ j ht => ht.diff (hQ j)) (hQ i)
  have hsub (i : Fin k) : W i ⊆ Q i := disjointed_subset Q i
  have hcover : (⋃ i, W i) = ⋃ i, Q i := iUnion_disjointed
  have hdisj : Pairwise fun i j => Disjoint (W i) (W j) := disjoint_disjointed Q
  have hslice (t : ℝ) : ((⋃ i,W i) ∩ {p | f p=t}) =
      ⋃ i, W i ∩ {p | f p=t} := Set.iUnion_inter _ _
  have hball : ((⋃ i,W i) ∩ {p | f p ≤ b}) =
      ⋃ i, W i ∩ {p | f p ≤ b} := Set.iUnion_inter _ _
  have hm (i : Fin k) : MeasurableSet (W i ∩ {p | f p ≤ b}) := by
    have he : W i ∩ {p | f p ≤ b} = W i ∩ {p | ⟪g i,p⟫_ℝ+c i ≤ b} := by
      ext p; constructor <;> rintro ⟨hp,ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,← hf i p (hsub i hp)] using ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,hf i p (hsub i hp)] using ht⟩
    rw [he]
    exact (hW i).inter (measurableSet_le (by fun_prop) measurable_const)
  rw [← hcover]
  calc
    _ ≤ ∫⁻ t in Ioo r b, ∑ i, μHE[d-1] (W i ∩ {p | f p=t}) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [hslice]
      simpa only [tsum_fintype] using measure_iUnion_le (μ := μHE[d-1])
        (fun i => W i ∩ {p | f p=t})
    _ = ∑ i, ∫⁻ t in Ioo r b, μHE[d-1] (W i ∩ {p | f p=t}) := by
      apply lintegral_finsetSum
      intro i _
      exact measurable_simplex_piece_slices (s i) d (hs i) hd (hW i)
        ((hsub i).trans (hQs i)) f (g i) (c i) (fun p hp => hf i p (hsub i hp))
    _ ≤ ∑ i, μHE[d] (W i ∩ {p | f p ≤ b}) := by
      apply Finset.sum_le_sum
      intro i _
      exact simplex_piece_coarea (s i) d (hs i) hd (hW i)
        ((hsub i).trans (hQs i)) f (g i) (hg i) (c i) (fun p hp => hf i p (hsub i hp)) r b
    _ = _ := by
      rw [hball,measure_iUnion]
      · exact (tsum_fintype _).symm
      · intro i j hij
        exact (hdisj hij).mono inter_subset_left inter_subset_left
      · exact hm

lemma finite_affine_coarea {I : Type*} [Fintype I]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : I → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : I → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (⋃ j, Q (e j)) = ⋃ i, Q i := e.surjective.iUnion_comp Q
  rw [← he]
  exact finite_polyhedral_coarea (fun j => s (e j)) d (fun j => hs (e j)) hd
    (fun j => Q (e j)) (fun j => hQ (e j)) (fun j => hQs (e j)) f
    (fun j => g (e j)) (fun j => hg (e j)) (fun j => c (e j))
    (fun j => hf (e j)) r b

lemma finite_max_coarea {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (g : I → J → E) (hg : ∀ i j, ‖g i j‖ ≤ 1) (c : I → J → ℝ)
    (f : E → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = Finset.univ.sup' Finset.univ_nonempty
      (fun j => ⟪g i j,p⟫_ℝ+c i j)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  let W (a : I × J) := Q a.1 ∩ ⋂ j, {p | ⟪g a.1 j,p⟫_ℝ+c a.1 j ≤
    ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2}
  have hW (a : I × J) : MeasurableSet (W a) := by
    exact (hQ a.1).inter (MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) (by fun_prop))
  have hWQ (a : I × J) : W a ⊆ Q a.1 := inter_subset_left
  have hcover : (⋃ a, W a) = ⋃ i, Q i := by
    apply Set.Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro a
      exact (hWQ a).trans (subset_iUnion Q a.1)
    · intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => ⟪g i j,p⟫_ℝ+c i j)
      apply Set.mem_iUnion.mpr
      refine ⟨(i,j),hi,Set.mem_iInter.mpr ?_⟩
      intro l
      change ⟪g i l,p⟫_ℝ+c i l ≤ ⟪g i j,p⟫_ℝ+c i j
      rw [← hj]
      exact Finset.le_sup' (fun j => ⟪g i j,p⟫_ℝ+c i j) (Finset.mem_univ l)
  have hbranch (a : I × J) (p : E) (hp : p ∈ W a) :
      f p = ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2 := by
    rw [hf a.1 p hp.1]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => Set.mem_iInter.mp hp.2 j)
    · exact Finset.le_sup' (fun j => ⟪g a.1 j,p⟫_ℝ+c a.1 j) (Finset.mem_univ a.2)
  rw [← hcover]
  exact finite_affine_coarea (fun a => s a.1) d (fun a => hs a.1) hd W hW
    (fun a => (hWQ a).trans (hQs a.1)) f (fun a => g a.1 a.2)
    (fun a => hg a.1 a.2) (fun a => c a.1 a.2) hbranch r b

lemma measurable_finite_polyhedral_slices {k : ℕ}
    (s : Fin k → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : Fin k → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : Fin k → E) (c : Fin k → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  let W := disjointed Q
  have hW (i : Fin k) : MeasurableSet (W i) :=
    disjointedRec (fun _ j ht => ht.diff (hQ j)) (hQ i)
  have hsub (i : Fin k) : W i ⊆ Q i := disjointed_subset Q i
  have hcover : (⋃ i, W i) = ⋃ i, Q i := iUnion_disjointed
  have hdisj : Pairwise fun i j => Disjoint (W i) (W j) := disjoint_disjointed Q
  have hm (i : Fin k) (t : ℝ) : MeasurableSet (W i ∩ {p | f p=t}) := by
    have he : W i ∩ {p | f p=t} = W i ∩ {p | ⟪g i,p⟫_ℝ+c i=t} := by
      ext p
      constructor <;> rintro ⟨hp,ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,← hf i p (hsub i hp)] using ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,hf i p (hsub i hp)] using ht⟩
    rw [he]
    exact (hW i).inter (measurableSet_eq_fun (by fun_prop) measurable_const)
  have he (t : ℝ) : μHE[d-1] ((⋃ i,Q i) ∩ {p | f p=t}) =
      ∑ i, μHE[d-1] (W i ∩ {p | f p=t}) := by
    rw [← hcover,Set.iUnion_inter,measure_iUnion]
    · exact tsum_fintype _
    · intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    · intro i
      exact hm i t
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  exact measurable_simplex_piece_slices (s i) d (hs i) hd (hW i)
    ((hsub i).trans (hQs i)) f (g i) (c i) (fun p hp => hf i p (hsub i hp))

lemma measurable_finite_affine_slices {I : Type*} [Fintype I]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : I → E) (c : I → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (⋃ j, Q (e j)) = ⋃ i, Q i := e.surjective.iUnion_comp Q
  rw [← he]
  exact measurable_finite_polyhedral_slices (fun j => s (e j)) d (fun j => hs (e j)) hd
    (fun j => Q (e j)) (fun j => hQ (e j)) (fun j => hQs (e j)) f
    (fun j => g (e j)) (fun j => c (e j)) (fun j => hf (e j))

lemma measurable_finite_max_slices {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (g : I → J → E) (c : I → J → ℝ) (f : E → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = Finset.univ.sup' Finset.univ_nonempty
      (fun j => ⟪g i j,p⟫_ℝ+c i j)) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  classical
  let W (a : I × J) := Q a.1 ∩ ⋂ j, {p | ⟪g a.1 j,p⟫_ℝ+c a.1 j ≤
    ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2}
  have hW (a : I × J) : MeasurableSet (W a) := by
    exact (hQ a.1).inter (MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) (by fun_prop))
  have hWQ (a : I × J) : W a ⊆ Q a.1 := inter_subset_left
  have hcover : (⋃ a, W a) = ⋃ i, Q i := by
    apply Set.Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro a
      exact (hWQ a).trans (subset_iUnion Q a.1)
    · intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => ⟪g i j,p⟫_ℝ+c i j)
      apply Set.mem_iUnion.mpr
      refine ⟨(i,j),hi,Set.mem_iInter.mpr ?_⟩
      intro l
      change ⟪g i l,p⟫_ℝ+c i l ≤ ⟪g i j,p⟫_ℝ+c i j
      rw [← hj]
      exact Finset.le_sup' (fun j => ⟪g i j,p⟫_ℝ+c i j) (Finset.mem_univ l)
  have hbranch (a : I × J) (p : E) (hp : p ∈ W a) :
      f p = ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2 := by
    rw [hf a.1 p hp.1]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => Set.mem_iInter.mp hp.2 j)
    · exact Finset.le_sup' (fun j => ⟪g a.1 j,p⟫_ℝ+c a.1 j) (Finset.mem_univ a.2)
  rw [← hcover]
  exact measurable_finite_affine_slices (fun a => s a.1) d (fun a => hs a.1) hd W hW
    (fun a => (hWQ a).trans (hQs a.1)) f (fun a => g a.1 a.2)
    (fun a => c a.1 a.2) hbranch

end

end BassTrace.Sparse

end OAI
