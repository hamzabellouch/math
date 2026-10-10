import OAI.RepresentationTheory.RowColumn.Sectors
import OAI.LinearAlgebra.MatrixState.Whitening
import OAI.RepresentationTheory.RowColumn.Entropy

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
lemma hsVector_tensor_norm_sq (M : S → Matrix C C ℂ) :
    ‖hsVector (tensorMatrix M)‖^2 = ∏ i, ‖hsVector (M i)‖^2 := by
  rw [hsVector_norm_sq, tensorMatrix_star, tensorMatrix_mul, tensorMatrix_trace]
  simp_rw [← hsVector_inner, inner_self_eq_norm_sq_to_K]
  change (∏ i, ((‖hsVector (M i)‖ : ℝ) : ℂ)^2).re = _
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_prod, Complex.ofReal_re]

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma sectorTensor_hermitian (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).IsHermitian) :
    (sectorTensor odd k M).IsHermitian := by
  change star (sectorTensor odd k M) = sectorTensor odd k M
  rw [← sectorTensor_star]
  congr 1
  funext i
  exact hM i

lemma sectorTensor_positive (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (sectorTensor odd k M).PosSemidef :=
  (tensorMatrix_posSemidef M hM).submatrix _

lemma sectorTensor_root_square (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef)
    (he : ∀ i, M i ∈ evenAlgebra odd) :
    sectorTensor odd k (fun i => CFC.sqrt (M i)) ^ 2 = sectorTensor odd k M := by
  rw [pow_two, ← sectorTensor_mul odd k _ _ (fun i => sqrt_even odd (M i) (hM i) (he i))]
  congr 1
  funext i
  exact CFC.sqrt_mul_sqrt_self _ (hM i).nonneg

/-- The restriction is taken only after factoring the positive weighted
Hilbert--Schmidt norm. In particular no diagonal of a nonpositive product is
compared to the full trace. -/
lemma sector_unitary_sandwich_bound (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M N : S → Matrix C C ℂ) (U : Matrix C C ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hN : ∀ i, (N i).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) (_ : ∀ i, N i ∈ evenAlgebra odd)
    (heU : U ∈ evenAlgebra odd) :
    ‖hsVector (sectorTensor odd k (fun i => CFC.sqrt (M i)) *
      sectorTensor odd k (fun _ : S => U) *
      sectorTensor odd k (fun i => CFC.sqrt (N i)))‖^2 ≤
        ∏ i, (M i * U * N i * U.conjTranspose).trace.re := by
  rw [← sectorTensor_mul odd k _ _ (fun i => sqrt_even odd (M i) (hM i) (heM i))]
  rw [← sectorTensor_mul odd k _ _ (fun i => (evenAlgebra odd).mul_mem
    (sqrt_even odd (M i) (hM i) (heM i)) heU)]
  let e : Words (S := S) odd k ↪ (S → C) := ⟨Subtype.val, Subtype.val_injective⟩
  have hb := hsVector_submatrix_norm_sq_le e e
    (tensorMatrix (fun i => CFC.sqrt (M i) * U * CFC.sqrt (N i)))
  change ‖hsVector (sectorTensor odd k _)‖^2 ≤ _ at hb
  rw [hsVector_tensor_norm_sq] at hb
  convert hb using 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hsVector_sandwich_sq _ _ U
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M i))).isHermitian
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (N i))).isHermitian]
  rw [CFC.sq_sqrt (M i) (hM i).nonneg, CFC.sq_sqrt (N i) (hN i).nonneg]

/-- Use the intrinsic spectral order on the closed finite C*-algebra. Its
physical Hilbert--Schmidt structure and existing operator norm are unchanged. -/
lemma algebra_reconstruction_hilbert_bound
    {E H G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Group G]
    (A : StarSubalgebra ℂ (E →L[ℂ] E)) (u : G →* unitary A)
    (hspan : Submodule.span ℂ (Set.range fun g : G => (u g : A)) = ⊤)
    (B : A) (F : A →ₗ[ℂ] H) (R : ℝ) (hR : 0 ≤ R)
    (hU : ∀ g, ‖F (u g : A)‖ ≤ R) :
    ‖F B‖ ≤ 4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * R := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact UnitaryFrame.reconstruction_hilbert_bound (physicalTrace A) (algebraCore A)
    (core_inner_trace A) u hspan B F R hR hU

/-- Matrix form of an actual algebra element, with the unchanged physical
coordinate basis on the signed tensor sector. -/
def algebraMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) :
    A →ₗ[ℂ] Matrix I I ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.toAlgEquiv.toLinearMap.comp A.subtype.toLinearMap

def sandwichMap {I : Type*} [Fintype I] [DecidableEq I]
    (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (M N : Matrix I I ℂ) : A →ₗ[ℂ] EuclideanSpace ℂ (I × I) :=
  hsVector.comp ((LinearMap.mulRight ℂ N).comp ((LinearMap.mulLeft ℂ M).comp (algebraMatrix A)))

lemma sandwichMap_apply {I : Type*} [Fintype I] [DecidableEq I]
    (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (M N : Matrix I I ℂ) (a : A) :
    sandwichMap A M N a = hsVector (M * algebraMatrix A a * N) := rfl

lemma sector_unitary_matrix (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (U : unitary (evenAlgebra odd)) :
    algebraMatrix (sectorAlgebra (S := S) odd k)
      (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k) U).val = sectorTensor odd k (fun _ : S => U.val.val) := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm_apply_apply _

/-- Weighted reconstruction in the actual signed sector, with the exact
occupied-board entropy loss and singular quarter-root normalization. -/
theorem whitened_reconstruction_bound {L K : Type*} [Fintype L] [Fintype K]
    [DecidableEq L] [DecidableEq K] [Nonempty S]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ) (e : S ↪ L × K)
    (M : L → Matrix C C ℂ) (N : K → Matrix C C ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hN : ∀ j, (N j).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) (heN : ∀ j, N j ∈ evenAlgebra odd)
    (hMt : ∀ i, (M i).trace.re ≤ 1) (hNt : ∀ j, (N j).trace.re ≤ 1)
    (B : sectorAlgebra (S := S) odd k) :
    let p := uniformMarginal (fun i => (e i).1)
    let q := uniformMarginal (fun i => (e i).2)
    let M' := fun i => whitenState (stateMean p M) (M i)
    let N' := fun j => whitenState (stateMean q N) (N j)
    ‖hsVector (sectorTensor odd k (fun i => CFC.sqrt (M' (e i).1)) *
      algebraMatrix (sectorAlgebra (S := S) odd k) B *
      sectorTensor odd k (fun i => CFC.sqrt (N' (e i).2)))‖^2 ≤
      16 * (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2 * ‖B‖^2 *
        Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ) := by
  dsimp only
  let p := uniformMarginal (fun i => (e i).1)
  let q := uniformMarginal (fun i => (e i).2)
  let M' := fun i => whitenState (stateMean p M) (M i)
  let N' := fun j => whitenState (stateMean q N) (N j)
  let A := sectorAlgebra (S := S) odd k
  let R := Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ)
  let F := sandwichMap A (sectorTensor odd k (fun i => CFC.sqrt (M' (e i).1)))
    (sectorTensor odd k (fun i => CFC.sqrt (N' (e i).2)))
  have hp := uniformMarginal_nonneg (fun i => (e i).1)
  have hq := uniformMarginal_nonneg (fun i => (e i).2)
  have hMp : ∀ i, (M' i).PosSemidef := fun i => whitenState_positive _ _ (hM i)
  have hNp : ∀ j, (N' j).PosSemidef := fun j => whitenState_positive _ _ (hN j)
  have hMe : ∀ i, M' i ∈ evenAlgebra odd := fun i =>
    whitenState_even odd _ _ (stateMean_positive p M hp hM) (stateMean_even odd p M heM) (heM i)
  have hNe : ∀ j, N' j ∈ evenAlgebra odd := fun j =>
    whitenState_even odd _ _ (stateMean_positive q N hq hN) (stateMean_even odd q N heN) (heN j)
  have hu (U : unitary (evenAlgebra odd)) :
      ‖F (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k) U).val‖ ≤ Real.sqrt R := by
    apply Real.le_sqrt_of_sq_le
    change ‖hsVector (sectorTensor odd k (fun i => CFC.sqrt (M' (e i).1)) *
      algebraMatrix (sectorAlgebra (S := S) odd k)
        (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k) U).val *
      sectorTensor odd k (fun i => CFC.sqrt (N' (e i).2)))‖^2 ≤ R
    rw [sector_unitary_matrix]
    apply (sector_unitary_sandwich_bound odd k (fun i => M' (e i).1) (fun i => N' (e i).2)
      U.val.val (fun i => hMp _) (fun i => hNp _) (fun i => hMe _) (fun i => hNe _)
      U.val.property).trans
    apply occupied_product_of_mean_le e (fun i j => (M' i * U.val.val * N' j * U.val.val.conjTranspose).trace.re)
    · exact fun i j => local_overlap_nonneg _ _ _ (hMp i) (hNp j)
    · exact weighted_whitened_mean_le_one p q M N hp hq (sum_uniformMarginal _)
        (sum_uniformMarginal _) hM hN hMt hNt U.val.val
        ⟨congrArg Subtype.val U.property.1, congrArg Subtype.val U.property.2⟩
  have hh := algebra_reconstruction_hilbert_bound A
    (unitarySpanHom (R := ℂ) (sectorUnitary (S := S) odd k))
    (unitarySpanHom_spans (R := ℂ) (sectorUnitary (S := S) odd k)) B F
    (Real.sqrt R) (Real.sqrt_nonneg _) hu
  have hs := pow_le_pow_left₀ (norm_nonneg (F B)) hh 2
  change ‖F B‖^2 ≤ _
  calc
    _ ≤ (4 * (Module.finrank ℂ A : ℝ) * ‖B‖ * Real.sqrt R)^2 := hs
    _ = _ := by
      dsimp only [A, R]
      simp only [mul_pow, Real.sq_sqrt (le_of_lt (Real.exp_pos _))]
      ring

lemma filtered_trace_identity {I : Type*} [Fintype I] [DecidableEq I]
    (A B R T F G Q : Matrix I I ℂ)
    (hR : R.IsHermitian) (hT : T.IsHermitian)
    (hF : F.IsHermitian) (hG : G.IsHermitian) (hQ : Q.IsHermitian)
    (hA : F * R^2 * F = A) (hB : G * T^2 * G = B) :
    (A * Q * B * Q).trace.re = ‖hsVector (R * (F * Q * G) * T)‖^2 := by
  rw [hsVector_sandwich_sq R T _ hR hT]
  simp only [Matrix.conjTranspose_mul, hF.eq, hG.eq, hQ.eq]
  rw [← hA, ← hB]
  apply congrArg Complex.re
  calc
    _ = (F * (R^2 * F * Q * G * T^2 * G * Q)).trace := by simp only [mul_assoc]
    _ = ((R^2 * F * Q * G * T^2 * G * Q) * F).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open FiniteStarAlgebra Signed
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma algebraMatrix_mul (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a b : A) : algebraMatrix A (a*b) = algebraMatrix A a * algebraMatrix A b :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm.map_mul a.val b.val
lemma algebraMatrix_star (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) : algebraMatrix A (star a) = star (algebraMatrix A a) :=
  (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).symm.map_star' a.val
lemma algebraMatrix_hermitian (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) (ha : star a=a) : (algebraMatrix A a).IsHermitian := by
  change star (algebraMatrix A a)=_
  rw [← algebraMatrix_star, ha]
lemma algebraMatrix_trace (A : StarSubalgebra ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I))
    (a : A) : (algebraMatrix A a).trace = physicalTrace A a := by
  rw [← trace_toEuclideanCLM]
  change LinearMap.trace ℂ (EuclideanSpace ℂ I)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ)) ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm a.val)).toLinearMap = _
  rw [(Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply]
  rfl

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

lemma tensorMatrix_trace_re (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (tensorMatrix M).trace.re = ∏ i, (M i).trace.re := by
  have hs (i : S) : (CFC.sqrt (M i)).conjTranspose * CFC.sqrt (M i) = M i := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M i))).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ (hM i).nonneg
  have ht := hsVector_tensor_norm_sq (fun i => CFC.sqrt (M i))
  simp only [hsVector_norm_sq, tensorMatrix_star, tensorMatrix_mul, hs] at ht
  exact ht

lemma sectorTensor_trace_le (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (sectorTensor odd k M).trace.re ≤ (tensorMatrix M).trace.re := by
  let e : Words (S := S) odd k ↪ (S → C) := ⟨Subtype.val, Subtype.val_injective⟩
  have hh := finite_sum_embedding_le e (fun w => (tensorMatrix M w w).re)
    (fun w => ((tensorMatrix_posSemidef M hM).diag_nonneg (i := w)).1)
  simpa only [sectorTensor, Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.submatrix_apply, e, Function.Embedding.coeFn_mk] using hh

lemma sectorTensor_substate_trace (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : S → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef)
    (htr : ∀ i, (M i).trace.re ≤ 1) : (sectorTensor odd k M).trace.re ≤ 1 := by
  apply (sectorTensor_trace_le odd k M hM).trans
  rw [tensorMatrix_trace_re M hM]
  exact Finset.prod_le_one₀ (fun i _ => (hM i).trace_nonneg.1) (fun i _ => htr i)

def positiveTensor (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    sectorAlgebra (S := S) odd k :=
  ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (sectorTensor odd k (fun _ : S => M)),
    sectorTensor_mem_algebra odd k M hM.isHermitian he⟩

lemma positiveTensor_matrix (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    algebraMatrix (sectorAlgebra (S := S) odd k) (positiveTensor odd k M hM he) =
      sectorTensor odd k (fun _ : S => M) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm_apply_apply _

lemma positiveTensor_isPositive (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    (positiveTensor (S := S) odd k M hM he).val.IsPositive :=
  (toEuclideanCLM_positive_iff _).mpr (sectorTensor_positive odd k _ (fun _ : S => hM))

lemma positiveTensor_selfAdjoint (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    IsSelfAdjoint (positiveTensor (S := S) odd k M hM he) := by
  apply Subtype.ext
  exact (positiveTensor_isPositive odd k M hM he).isSelfAdjoint

lemma positiveTensor_trace_le_one (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) (htr : M.trace.re ≤ 1) :
    (physicalTrace (sectorAlgebra (S := S) odd k) (positiveTensor odd k M hM he)).re ≤ 1 := by
  rw [← algebraMatrix_trace, positiveTensor_matrix]
  exact sectorTensor_substate_trace odd k _ (fun _ : S => hM) (fun _ => htr)

lemma positiveTensor_quarter_four (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M : Matrix C C ℂ) (hM : M.PosSemidef) (he : M ∈ evenAlgebra odd) :
    positiveTensor (S := S) odd k (quarterRoot M) (quarter_positive M) (quarter_even odd M hM he) ^ 4 =
      positiveTensor odd k M hM he := by
  apply Subtype.ext
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (sectorTensor odd k (fun _ : S => quarterRoot M)))^4 = _
  rw [← map_pow]
  have hh := (sectorPowerHom (S := S) odd k).map_pow
    (⟨quarterRoot M, quarter_even odd M hM he⟩ : evenAlgebra odd) 4
  change sectorTensor odd k (fun _ : S => quarterRoot M ^ 4) =
    (sectorTensor odd k (fun _ : S => quarterRoot M)) ^ 4 at hh
  rw [← hh, quarter_four M hM]
  rfl

/-- The actual irreducible-dimension filter acts on fourth powers of both
mean-state tensors. Its quarter-root sandwich has squared norm at most 1/d. -/
theorem quarter_tensor_filter_bound (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (q : sectorAlgebra (S := S) odd k) (hqs : star q=q) (hqq : q*q=q)
    (hqc : ∀ a, q*a=a*q) (d : ℝ) (hd : 0<d)
    (hfilter : ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
      ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / d)
    (M N : Matrix C C ℂ) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (heM : M ∈ evenAlgebra odd) (heN : N ∈ evenAlgebra odd)
    (hMt : M.trace.re ≤ 1) (hNt : N.trace.re ≤ 1) :
    ‖positiveTensor odd k (quarterRoot M) (quarter_positive M) (quarter_even odd M hM heM) * q *
      positiveTensor odd k (quarterRoot N) (quarter_positive N) (quarter_even odd N hN heN)‖^2 ≤ 1/d := by
  apply filterNorm_sq q _ _ hqs hqq
    (positiveTensor_selfAdjoint odd k _ _ _) (positiveTensor_selfAdjoint odd k _ _ _)
    (hqc _) (hqc _) d hd
  · rw [positiveTensor_quarter_four odd k M hM heM]
    apply (hfilter _ (positiveTensor_isPositive odd k M hM heM)).trans
    exact div_le_div_of_nonneg_right (positiveTensor_trace_le_one odd k M hM heM hMt) hd.le
  · rw [positiveTensor_quarter_four odd k N hN heN]
    apply (hfilter _ (positiveTensor_isPositive odd k N hN heN)).trans
    exact div_le_div_of_nonneg_right (positiveTensor_trace_le_one odd k N hN heN hNt) hd.le

lemma sector_unwhiten_identity {L : Type*} [Fintype L] [DecidableEq L] [Nonempty S]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ) (line : S → L)
    (M : L → Matrix C C ℂ) (hM : ∀ i, (M i).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) :
    let p := uniformMarginal line
    let A := stateMean p M
    let M' := fun i => whitenState A (M i)
    sectorTensor odd k (fun _ : S => quarterRoot A) *
      sectorTensor odd k (fun x => CFC.sqrt (M' (line x))) ^ 2 *
      sectorTensor odd k (fun _ : S => quarterRoot A) =
      sectorTensor odd k (fun x => M (line x)) := by
  dsimp only
  let p := uniformMarginal line
  let A := stateMean p M
  let M' := fun i => whitenState A (M i)
  have hp := uniformMarginal_nonneg line
  have hA := stateMean_positive p M hp hM
  have heA := stateMean_even odd p M heM
  have hMp : ∀ i, (M' i).PosSemidef := fun i => whitenState_positive A (M i) (hM i)
  have hMe : ∀ i, M' i ∈ evenAlgebra odd := fun i => whitenState_even odd A (M i) hA heA (heM i)
  change sectorTensor odd k (fun _ : S => quarterRoot A) *
    sectorTensor odd k (fun x => CFC.sqrt (M' (line x))) ^ 2 *
    sectorTensor odd k (fun _ : S => quarterRoot A) = _
  rw [sectorTensor_root_square odd k _ (fun x => hMp _) (fun x => hMe _)]
  rw [← sectorTensor_mul odd k _ _ (fun _ => quarter_even odd A hA heA)]
  rw [← sectorTensor_mul odd k _ _ (fun x => (evenAlgebra odd).mul_mem
    (quarter_even odd A hA heA) (hMe _))]
  congr 1
  funext x
  exact unwhitenState p M hp hM (line x) (uniformMarginal_pos line x)

/-- The quantitative global bridge: two arbitrary admissible fibre-product
substates, on the actual signed sector and the actual central isotypic filter.
No invertibility, sector-surrogate, or postselection bound is assumed. -/
theorem sector_filtered_trace_bound {L K : Type*} [Fintype L] [Fintype K]
    [DecidableEq L] [DecidableEq K] [Nonempty S]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ) (e : S ↪ L × K)
    (q : sectorAlgebra (S := S) odd k) (hqs : star q=q) (hqq : q*q=q)
    (hqc : ∀ a, q*a=a*q) (d : ℝ) (hd : 0<d)
    (hfilter : ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
      ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / d)
    (M : L → Matrix C C ℂ) (N : K → Matrix C C ℂ)
    (hM : ∀ i, (M i).PosSemidef) (hN : ∀ j, (N j).PosSemidef)
    (heM : ∀ i, M i ∈ evenAlgebra odd) (heN : ∀ j, N j ∈ evenAlgebra odd)
    (hMt : ∀ i, (M i).trace.re ≤ 1) (hNt : ∀ j, (N j).trace.re ≤ 1) :
    (sectorTensor odd k (fun x => M (e x).1) * algebraMatrix (sectorAlgebra (S := S) odd k) q *
      sectorTensor odd k (fun x => N (e x).2) * algebraMatrix (sectorAlgebra (S := S) odd k) q).trace.re ≤
      16 * (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2 *
        Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ) / d := by
  let p := uniformMarginal (fun x => (e x).1)
  let r := uniformMarginal (fun x => (e x).2)
  let A := stateMean p M
  let B := stateMean r N
  let M' := fun i => whitenState A (M i)
  let N' := fun j => whitenState B (N j)
  have hp := uniformMarginal_nonneg (fun x => (e x).1)
  have hr := uniformMarginal_nonneg (fun x => (e x).2)
  have hA := stateMean_positive p M hp hM
  have hB := stateMean_positive r N hr hN
  have heA := stateMean_even odd p M heM
  have heB := stateMean_even odd r N heN
  let F := positiveTensor (S := S) odd k (quarterRoot A) (quarter_positive A) (quarter_even odd A hA heA)
  let G := positiveTensor (S := S) odd k (quarterRoot B) (quarter_positive B) (quarter_even odd B hB heB)
  have hnorm : ‖F*q*G‖^2 ≤ 1/d := quarter_tensor_filter_bound odd k q hqs hqq hqc d hd hfilter
    A B hA hB heA heB (stateMean_trace_le_one p M hp (sum_uniformMarginal _) hMt)
    (stateMean_trace_le_one r N hr (sum_uniformMarginal _) hNt)
  have hrec := whitened_reconstruction_bound odd k e M N hM hN heM heN hMt hNt (F*q*G)
  change ‖hsVector (sectorTensor odd k (fun x => CFC.sqrt (M' (e x).1)) *
    algebraMatrix (sectorAlgebra (S := S) odd k) (F*q*G) *
    sectorTensor odd k (fun x => CFC.sqrt (N' (e x).2)))‖^2 ≤ _ at hrec
  simp only [algebraMatrix_mul, F, G, positiveTensor_matrix] at hrec
  have hi := filtered_trace_identity
    (sectorTensor odd k (fun x => M (e x).1)) (sectorTensor odd k (fun x => N (e x).2))
    (sectorTensor odd k (fun x => CFC.sqrt (M' (e x).1)))
    (sectorTensor odd k (fun x => CFC.sqrt (N' (e x).2)))
    (sectorTensor odd k (fun _ : S => quarterRoot A))
    (sectorTensor odd k (fun _ : S => quarterRoot B))
    (algebraMatrix (sectorAlgebra (S := S) odd k) q)
    (sectorTensor_hermitian odd k _ (fun x => (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian))
    (sectorTensor_hermitian odd k _ (fun x => (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian))
    (sectorTensor_hermitian odd k _ (fun _ => (quarter_positive A).isHermitian))
    (sectorTensor_hermitian odd k _ (fun _ => (quarter_positive B).isHermitian))
    (algebraMatrix_hermitian _ q hqs)
    (sector_unwhiten_identity odd k (fun x => (e x).1) M hM heM)
    (sector_unwhiten_identity odd k (fun x => (e x).2) N hN heN)
  rw [hi]
  apply hrec.trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnorm
      (by positivity : 0 ≤ 16 * (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2))
    (le_of_lt (Real.exp_pos ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ)))
  convert hh using 1; ring

/-- The filter used above exists in the concrete tensor algebra, for every
actual irreducible that occurs. The identity condition on its isotypic carrier
will be applied to the explicit isometric hook embedding. -/
theorem exists_sector_isotypic_filter {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (ρ : Representation ℂ (Equiv.Perm S) V) [Representation.IsIrreducible ρ] :
    ∃ q : sectorAlgebra (S := S) odd k, star q=q ∧ q*q=q ∧ (∀ a, q*a=a*q) ∧
      (∀ x ∈ Isotypic.carrier ρ (Signed.representation (S := S) (odd := odd) (k := k)), q.val x=x) ∧
      ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
        ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / Module.finrank ℂ V :=
  exists_isotypic_filter ρ (Signed.representation (S := S) (odd := odd) (k := k))
    (Signed.representation_unitary (S := S) (odd := odd) (k := k)) (sectorAlgebra (S := S) odd k)
    (sectorAlgebra_commutes odd k)

end RowColumn.MatrixState

end
end

end OAI
