import OAI.RingTheory.BassTrace.SimplexVolume

namespace OAI

/-! An oriented incidence matrix of a tree, with its root row deleted, is unimodular,
independently of a planar structure or ordering of children. -/

namespace BassTrace.Sparse

section

open SimpleGraph

noncomputable def treeEdgeEquiv {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Fin n ≃ Γ.edgeSet := by
  classical
  apply Fintype.equivOfCardEq
  have h := hΓ.card_edgeFinset
  rw [Γ.edgeFinset_card, Fintype.card_fin] at h
  simp only [Fintype.card_fin]
  omega

def rootCoordinate {n : ℕ} (v : Fin (n+1)) : Fin n → ℤ :=
  fun i => if i.succ=v then 1 else 0

lemma rootCoordinate_zero (n : ℕ) : rootCoordinate (0 : Fin (n+1)) = 0 := by
  ext i
  simp [rootCoordinate]

lemma rootCoordinate_succ {n : ℕ} (v : Fin n) :
    rootCoordinate v.succ = Pi.single v 1 := by
  ext i
  simp [rootCoordinate,Pi.single_apply,eq_comm]

noncomputable def treeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i -
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i

lemma adjacent_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (huv : Γ.Adj u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  classical
  let e : Γ.edgeSet := ⟨s(u,v),huv⟩
  let j := (treeEdgeEquiv Γ hΓ).symm e
  have hj : treeEdgeEquiv Γ hΓ j = e := (treeEdgeEquiv Γ hΓ).apply_symm_apply e
  have hc := Submodule.subset_span (R := ℤ) (Set.mem_range_self
    (f := (treeIncidence Γ hΓ).col) j)
  have he : s(e.val.out.1,e.val.out.2) = s(u,v) := e.val.out_eq
  rcases Sym2.eq_iff.mp he with h | h
  · have heq : rootCoordinate u - rootCoordinate v = (treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact hc
  · have heq : rootCoordinate u - rootCoordinate v = -(treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact Submodule.neg_mem _ hc

lemma walk_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (p : Γ.Walk u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have h := Submodule.add_mem _ (adjacent_difference_mem_span Γ hΓ huv) ih
    convert h using 1
    abel

lemma treeIncidence_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hsingle (i : Fin n) : Pi.single i (1 : ℤ) ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
    obtain ⟨p⟩ := hΓ.connected.preconnected i.succ 0
    simpa only [rootCoordinate_zero,sub_zero,rootCoordinate_succ] using
      walk_difference_mem_span Γ hΓ p
  have hx : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ (x i) (hsingle i))

theorem treeIncidence_isUnit_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : IsUnit (treeIncidence Γ hΓ).det := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply (LinearMap.range_eq_top (f := (treeIncidence Γ hΓ).mulVecLin)).mp
  rw [Matrix.range_mulVecLin,treeIncidence_span]

theorem treeIncidence_abs_real_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : |((treeIncidence Γ hΓ).map (Int.castRingHom ℝ)).det| = 1 := by
  classical
  change |((treeIncidence Γ hΓ).map (fun x => (x : ℝ))).det| = 1
  rw [← Int.cast_det]
  rcases Int.isUnit_iff.mp (treeIncidence_isUnit_det Γ hΓ) with h | h <;> simp [h]

open MeasureTheory Set

noncomputable def realTreeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℝ :=
  (treeIncidence Γ hΓ).map (Int.castRingHom ℝ)

lemma realTreeIncidence_det_ne_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : (realTreeIncidence Γ hΓ).det ≠ 0 := by
  intro h
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [h,abs_zero] at hh
  exact zero_ne_one hh

theorem treeChart_measurePreserving {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : MeasurePreserving (Matrix.toLin' (realTreeIncidence Γ hΓ)) := by
  refine ⟨(Matrix.toLin' (realTreeIncidence Γ hΓ)).continuous_of_finiteDimensional.measurable,?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (realTreeIncidence_det_ne_zero Γ hΓ)]
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [abs_inv,hh,inv_one,ENNReal.ofReal_one,one_smul]

noncomputable def treeGradient {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j =>
    (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) - ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) /
      Real.sqrt n)

lemma treeGradient_norm_le_one {n : ℕ} (hn : 0 < n)
    (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ)
    (hℓ : ∀ u v, Γ.Adj u v → |ℓ u - ℓ v| ≤ 1) :
    ‖treeGradient Γ hΓ ℓ‖ ≤ 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, ((treeGradient Γ hΓ ℓ).ofLp i)^2 ≤ ∑ _i : Fin n, (1 : ℝ) / n := by
      apply Finset.sum_le_sum
      intro j _
      dsimp [treeGradient]
      rw [div_pow,Real.sq_sqrt hnR.le]
      apply div_le_div_of_nonneg_right _ hnR.le
      have hj := hℓ ((treeEdgeEquiv Γ hΓ j).val.out.1)
        ((treeEdgeEquiv Γ hΓ j).val.out.2)
        (by
          change s((treeEdgeEquiv Γ hΓ j).val.out.1,
            (treeEdgeEquiv Γ hΓ j).val.out.2) ∈ Γ.edgeSet
          have he : s((treeEdgeEquiv Γ hΓ j).val.out.1,
            (treeEdgeEquiv Γ hΓ j).val.out.2) = (treeEdgeEquiv Γ hΓ j).val :=
              (treeEdgeEquiv Γ hΓ j).val.out_eq
          rw [he]
          exact (treeEdgeEquiv Γ hΓ j).property)
      simpa only [sq_abs,one_pow] using
        (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hj
    _ = 1^2 := by simp [ne_of_gt hnR]

lemma rootCoordinate_potential {n : ℕ} (ℓ : Fin (n+1) → ℝ) (v : Fin (n+1)) :
    (∑ i, (ℓ i.succ - ℓ 0) * (rootCoordinate v i : ℝ)) = ℓ v - ℓ 0 := by
  induction v using Fin.cases with
  | zero => simp [rootCoordinate_zero]
  | succ v => simp [rootCoordinate_succ,Pi.single_apply]

lemma treeChart_potential {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    (∑ i, (ℓ i.succ - ℓ 0) * ((Matrix.toLin' (realTreeIncidence Γ hΓ)) x) i) /
      Real.sqrt n =
    ∑ j, (treeGradient Γ hΓ ℓ).ofLp j * x j := by
  simp only [Matrix.toLin'_apply,Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [realTreeIncidence,Matrix.map_apply,treeIncidence,map_sub]
  have hcol (j : Fin n) :
      (∑ i, (ℓ i.succ - ℓ 0) *
        (((rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i : ℝ) -
          (rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i : ℝ)) * x j)) =
      (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) -
        ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) * x j := by
    simp only [← mul_assoc,← Finset.sum_mul,mul_sub,Finset.sum_sub_distrib,
      rootCoordinate_potential]
    ring
  change (∑ j, ∑ i, (ℓ i.succ - ℓ 0) *
    (((rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i : ℝ) -
      (rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i : ℝ)) * x j)) /
        Real.sqrt n = _
  simp_rw [hcol]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [treeGradient]
  ring

noncomputable def treeSolidSimplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Set (Fin n → ℝ) :=
  (Matrix.toLin' (realTreeIncidence Γ hΓ)) ⁻¹' standardSolidSimplex n

lemma treeSolidSimplex_volume {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : volume (treeSolidSimplex Γ hΓ) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [treeSolidSimplex, (treeChart_measurePreserving Γ hΓ).measure_preimage
    (measurableSet_standardSolidSimplex n).nullMeasurableSet,
    volume_standardSolidSimplex]

end

open MeasureTheory Set Finset

open scoped ENNReal

noncomputable section

def barycentricParam {n : ℕ} (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases (1-∑ i, x i) x

@[simp] lemma barycentricParam_zero {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x 0 = 1-∑ i, x i := rfl

@[simp] lemma barycentricParam_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    barycentricParam x i.succ = x i := rfl

lemma sum_barycentricParam {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, barycentricParam x i = 1 := by
  rw [Fin.sum_univ_succ]
  simp

lemma barycentricParam_injective (n : ℕ) :
    Function.Injective (@barycentricParam n) := by
  intro x y h
  funext i
  exact congrFun h i.succ

lemma range_barycentricParam (n : ℕ) :
    Set.range (@barycentricParam n) = {p | ∑ i, p i = 1} := by
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact sum_barycentricParam x
  · intro hp
    refine ⟨fun i => p i.succ,?_⟩
    funext v
    induction v using Fin.cases with
    | zero =>
      change 1 - ∑ i : Fin n, p i.succ = p 0
      change ∑ i, p i = 1 at hp
      rw [Fin.sum_univ_succ] at hp
      linarith
    | succ v => rfl

lemma continuous_barycentricParam (n : ℕ) : Continuous (@barycentricParam n) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_const.sub (continuous_finsetSum _ fun _ _ => continuous_apply _)
  | succ i => exact continuous_apply i

def treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : Fin (n+1) → ℝ :=
  barycentricParam (Matrix.toLin' (realTreeIncidence T hT) x.ofLp)

lemma treeParam_injective {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Function.Injective (treeParam T hT) := by
  intro x y h
  apply WithLp.ofLp_injective
  have he := barycentricParam_injective n h
  apply Matrix.mulVec_injective_iff_isUnit.mpr _ he
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))

lemma range_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Set.range (treeParam T hT) = {p | ∑ i, p i = 1} := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) =>
      Matrix.toLin' (realTreeIncidence T hT) x.ofLp) := by
    apply Function.Surjective.comp _ (WithLp.ofLp_surjective 2)
    exact Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))
  rw [← range_barycentricParam n]
  exact hsurj.range_comp _

lemma continuous_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Continuous (treeParam T hT) :=
  (continuous_barycentricParam n).comp
    ((Matrix.toLin' (realTreeIncidence T hT)).continuous_of_finiteDimensional.comp (PiLp.continuous_ofLp _ _))

def treeArea {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  μHE[j] ((treeParam T hT) ⁻¹' Q)

lemma treeArea_mono {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (h : Q ⊆ W) :
    treeArea T hT j Q ≤ treeArea T hT j W := measure_mono (Set.preimage_mono h)

lemma treeArea_union {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (hW : MeasurableSet W) (hdisj : Disjoint Q W) :
    treeArea T hT j (Q ∪ W) = treeArea T hT j Q + treeArea T hT j W := by
  exact measure_union (hdisj.preimage _) ((continuous_treeParam T hT).measurable hW)

def fullBarycentricSimplex (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

lemma barycentricParam_mem_simplex {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x ∈ fullBarycentricSimplex n ↔ x ∈ standardSolidSimplex n := by
  simp only [fullBarycentricSimplex,Set.mem_ofPred_eq,sum_barycentricParam,and_true]
  constructor
  · intro h
    exact ⟨fun i => h i.succ,by have hh := h 0; dsimp at hh; linarith⟩
  · rintro ⟨hx,hs⟩ i
    induction i using Fin.cases with
    | zero => change 0 ≤ 1-∑ i,x i; linarith
    | succ i => exact hx i

lemma treeArea_top_simplex {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    treeArea T hT n (fullBarycentricSimplex n) = ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  have he : (treeParam T hT) ⁻¹' fullBarycentricSimplex n =
      WithLp.ofLp ⁻¹' treeSolidSimplex T hT := by
    ext x
    exact barycentricParam_mem_simplex _
  rw [treeArea,he,EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage]
  · exact treeSolidSimplex_volume T hT
  · exact ((measurableSet_standardSolidSimplex n).preimage
      (Matrix.toLin' (realTreeIncidence T hT)).continuous_of_finiteDimensional.measurable).nullMeasurableSet

lemma hausdorff_zero_eq_count {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : Set E) : μH[0] Q = Measure.count Q := by
  classical
  have hf (s : Finset E) : μH[0] (s : Set E) = (s.card : ℝ≥0∞) := by
    rw [← sum_measure_singleton]
    simp
  by_cases hQ : Q.Finite
  · rw [← hQ.coe_toFinset,hf,Measure.count_apply_finset]
  · rw [Measure.count_apply_infinite hQ]
    apply top_unique
    apply le_of_tendsto' ENNReal.tendsto_nat_nhds_top
    intro n
    obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hQ n
    calc
      (n : ℝ≥0∞) = μH[0] (s : Set E) := by rw [hf,hcard]
      _ ≤ μH[0] Q := measure_mono hs

lemma treeArea_zero {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i, p i=1}) :
    treeArea T hT 0 Q = Measure.count Q := by
  rw [treeArea,Measure.euclideanHausdorffMeasure_zero,hausdorff_zero_eq_count]
  rw [← Measure.count_injective_image (treeParam_injective T hT)]
  rw [Set.image_preimage_eq_inter_range,range_treeParam,Set.inter_eq_self_of_subset_left hQ]

def SpanningTree {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) :=
  {T : SimpleGraph (Fin (n+1)) // T ≤ Γ ∧ T.IsTree}

instance {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) : Fintype (SpanningTree Γ) := by
  classical
  unfold SpanningTree
  infer_instance

lemma nonempty_spanningTree {n : ℕ} {Γ : SimpleGraph (Fin (n+1))} (hΓ : Γ.Connected) :
    Nonempty (SpanningTree Γ) := by
  obtain ⟨T,hT,hTree⟩ := hΓ.exists_isTree_le
  exact ⟨⟨T,hT,hTree⟩⟩

def simplexArea {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  (∑ T : SpanningTree Γ, treeArea T.val T.property.2 j Q) / Fintype.card (SpanningTree Γ)

lemma simplexArea_mono {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (h : Q ⊆ W) :
    simplexArea Γ j Q ≤ simplexArea Γ j W := by
  apply ENNReal.div_le_div_right
  exact Finset.sum_le_sum fun T _ => treeArea_mono T.val T.property.2 j h

lemma simplexArea_top_simplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected) :
    simplexArea Γ n (fullBarycentricSimplex n) = ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  let := nonempty_spanningTree hΓ
  simp only [simplexArea,treeArea_top_simplex,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

lemma simplexArea_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i, p i=1}) :
    simplexArea Γ 0 Q = Measure.count Q := by
  let := nonempty_spanningTree hΓ
  simp only [simplexArea,treeArea_zero _ _ Q hQ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

end

end BassTrace.Sparse

end OAI
