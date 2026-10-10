import OAI.RingTheory.BassTrace.TreeDeterminants

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open MeasureTheory Set Finset

open scoped ENNReal

section

def treeMatrixEquiv {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realTreeIncidence T hT))
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))),
     Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))⟩

def independentCoordinates (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p := fun i => p i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    ((treeMatrixEquiv T hT).symm.toLinearMap.comp (independentCoordinates n))

@[simp] lemma treeCoordinates_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : treeCoordinates T hT (treeParam T hT x) = x := by
  change (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
    ((treeMatrixEquiv T hT).symm ((treeMatrixEquiv T hT) x.ofLp)) = x
  simp

lemma treeParam_treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (p : Fin (n+1) → ℝ) (hp : ∑ i,p i=1) : treeParam T hT (treeCoordinates T hT p) = p := by
  obtain ⟨x,rfl⟩ := (show p ∈ Set.range (treeParam T hT) by rw [range_treeParam]; exact hp)
  rw [treeCoordinates_treeParam]

lemma treeParam_preimage_eq_image {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    treeParam T hT ⁻¹' Q = treeCoordinates T hT '' Q := by
  ext x
  constructor
  · intro hx
    exact ⟨treeParam T hT x,hx,treeCoordinates_treeParam T hT x⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,treeParam_treeCoordinates T hT p (hQ hp)] using hp

lemma convex_sum_one (n : ℕ) : Convex ℝ {p : Fin (n+1) → ℝ | ∑ i,p i=1} := by
  intro x hx y hy a b _ _ hab
  change ∑ i,(a • x + b • y) i = 1
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  change ∑ i,x i=1 at hx
  change ∑ i,y i=1 at hy
  rw [hx,hy]
  simpa using hab

lemma treeParam_preimage_simplex {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1) :
    treeParam T hT ⁻¹' convexHull ℝ (s : Set (Fin (n+1) → ℝ)) =
      convexHull ℝ (treeCoordinates T hT '' (s : Set (Fin (n+1) → ℝ))) := by
  rw [treeParam_preimage_eq_image T hT _ (convexHull_min (by exact hs) (convex_sum_one n))]
  exact (treeCoordinates T hT).toAffineMap.image_convexHull _

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma euclideanArea_eq_zero_of_dimH_lt {Q : Set E} {d : ℕ}
    (h : dimH Q < (d : ℝ≥0∞)) : μHE[d] Q = 0 := by
  have hh : μH[(d : ℝ)] Q = 0 := by
    apply hausdorffMeasure_of_dimH_lt (d := (d : NNReal))
    simpa using h
  rw [Measure.euclideanHausdorffMeasure_def,Measure.smul_apply,hh,smul_zero]

lemma euclideanArea_simplex_eq_zero (s : Finset E) {d : ℕ} (hsd : s.card ≤ d) :
    μHE[d] (convexHull ℝ (s : Set E)) = 0 := by
  classical
  by_cases hs : s.Nonempty
  · have hpos : 0 < s.card := Finset.card_pos.mpr hs
    have hc : Fintype.card s = (s.card-1)+1 := by
      rw [Fintype.card_coe]
      have h := Finset.card_pos.mpr hs
      omega
    have hr := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
    rw [Subtype.range_coe_subtype] at hr
    change Module.finrank ℝ (vectorSpan ℝ (s : Set E)) ≤ s.card-1 at hr
    apply euclideanArea_eq_zero_of_dimH_lt
    rw [Real.Convex.dimH_eq_finrank_vectorSpan (convex_convexHull ℝ (s : Set E))
      (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs))]
    have hspan : vectorSpan ℝ (convexHull ℝ (s : Set E)) = vectorSpan ℝ (s : Set E) := by
      rw [← direction_affineSpan, affineSpan_convexHull,direction_affineSpan]
    rw [hspan]
    exact_mod_cast (show Module.finrank ℝ (vectorSpan ℝ (s : Set E)) < d by omega)
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

lemma euclideanArea_simplex_lt_top (s : Finset E) {d : ℕ} (hsd : s.card ≤ d+1) :
    μHE[d] (convexHull ℝ (s : Set E)) < ∞ := by
  classical
  by_cases hs : s.Nonempty
  · let Q := convexHull ℝ (s : Set E)
    let W := vectorSpan ℝ Q
    have hspan : W = vectorSpan ℝ (s : Set E) := by
      dsimp [W,Q]
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    have hdim : Module.finrank ℝ W ≤ d := by
      rw [hspan]
      have hc : Fintype.card s = (s.card-1)+1 := by
        rw [Fintype.card_coe]
        have := Finset.card_pos.mpr hs
        omega
      have hr := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
      rw [Subtype.range_coe_subtype] at hr
      exact hr.trans (by omega)
    have hQcv : Convex ℝ Q := convex_convexHull ℝ _
    have hQne : Q.Nonempty := convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    rcases lt_or_eq_of_le hdim with hlt|heq
    · rw [euclideanArea_eq_zero_of_dimH_lt (by
        rw [Real.Convex.dimH_eq_finrank_vectorSpan hQcv hQne]
        exact_mod_cast hlt)]
      exact ENNReal.zero_lt_top
    · obtain ⟨c,hc⟩ := hQne
      let f : W → E := fun w => (w : E)+c
      have hf : Isometry f := by
        apply Isometry.of_dist_eq
        intro u v
        simp only [f,dist_add_right,Subtype.dist_eq]
      have hQr : Q ⊆ Set.range f := by
        intro p hp
        refine ⟨⟨p-c,vsub_mem_vectorSpan ℝ hp hc⟩,?_⟩
        dsimp [f]
        abel
      have hcompact : IsCompact (f ⁻¹' Q) :=
        hf.isClosedEmbedding.isCompact_preimage (s.finite_toSet.isCompact_convexHull (𝕜 := ℝ))
      have hh := hf.euclideanHausdorffMeasure_preimage (d := d) Q
      rw [Set.inter_eq_self_of_subset_left hQr] at hh
      rw [← hh,← heq,InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact hcompact.measure_lt_top
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

lemma treeArea_simplex_lt_top {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1)
    {j : ℕ} (hc : s.card ≤ j+1) :
    treeArea T hT j (convexHull ℝ (s : Set (Fin (n+1) → ℝ))) < ∞ := by
  classical
  unfold treeArea
  rw [treeParam_preimage_simplex T hT s hs]
  rw [← Finset.coe_image]
  exact euclideanArea_simplex_lt_top _ ((Finset.card_image_le).trans hc)

lemma treeArea_simplex_eq_zero {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1)
    {j : ℕ} (hc : s.card ≤ j) :
    treeArea T hT j (convexHull ℝ (s : Set (Fin (n+1) → ℝ))) = 0 := by
  classical
  unfold treeArea
  rw [treeParam_preimage_simplex T hT s hs]
  rw [← Finset.coe_image]
  exact euclideanArea_simplex_eq_zero _ ((Finset.card_image_le).trans hc)

lemma simplexArea_simplex_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1)
    {j : ℕ} (hc : s.card ≤ j+1) :
    simplexArea Γ j (convexHull ℝ (s : Set (Fin (n+1) → ℝ))) < ∞ := by
  classical
  let := nonempty_spanningTree hΓ
  unfold simplexArea
  apply ENNReal.div_lt_top
  · exact ne_of_lt (ENNReal.sum_lt_top.mpr fun T _ => treeArea_simplex_lt_top T.val T.property.2 s hs hc)
  · exact_mod_cast Fintype.card_ne_zero

lemma simplexArea_simplex_eq_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1)
    {j : ℕ} (hc : s.card ≤ j) :
    simplexArea Γ j (convexHull ℝ (s : Set (Fin (n+1) → ℝ))) = 0 := by
  classical
  simp only [simplexArea, treeArea_simplex_eq_zero _ _ s hs hc, Finset.sum_const_zero,
    ENNReal.zero_div]

lemma treeArea_iUnion_le {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I : Type*} (s : Finset I) (Q : I → Set (Fin (n+1) → ℝ)) (j : ℕ) :
    treeArea T hT j (⋃ i ∈ s, Q i) ≤ ∑ i ∈ s, treeArea T hT j (Q i) := by
  simp only [treeArea,Set.preimage_iUnion]
  exact measure_biUnion_finset_le s _

lemma treeArea_polyhedral_lt_top {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (F : Finset (Finset (Fin (n+1) → ℝ))) {j : ℕ}
    (hs : ∀ s ∈ F, ∀ p ∈ s, ∑ i,p i=1) (hc : ∀ s ∈ F, s.card ≤ j+1)
    {Q : Set (Fin (n+1) → ℝ)}
    (hQ : Q ⊆ ⋃ s ∈ F, convexHull ℝ (s : Set (Fin (n+1) → ℝ))) :
    treeArea T hT j Q < ∞ := by
  exact lt_of_le_of_lt ((treeArea_mono T hT j hQ).trans (treeArea_iUnion_le T hT F _ j))
    (ENNReal.sum_lt_top.mpr fun s h => treeArea_simplex_lt_top T hT s (hs s h) (hc s h))

lemma simplexArea_polyhedral_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (F : Finset (Finset (Fin (n+1) → ℝ))) {j : ℕ}
    (hs : ∀ s ∈ F, ∀ p ∈ s, ∑ i,p i=1) (hc : ∀ s ∈ F, s.card ≤ j+1)
    {Q : Set (Fin (n+1) → ℝ)}
    (hQ : Q ⊆ ⋃ s ∈ F, convexHull ℝ (s : Set (Fin (n+1) → ℝ))) :
    simplexArea Γ j Q < ∞ := by
  classical
  let := nonempty_spanningTree hΓ
  unfold simplexArea
  apply ENNReal.div_lt_top
  · exact ne_of_lt (ENNReal.sum_lt_top.mpr fun T _ => treeArea_polyhedral_lt_top T.val T.property.2 F hs hc hQ)
  · exact_mod_cast Fintype.card_ne_zero

end BassTrace.Sparse

end

end OAI
