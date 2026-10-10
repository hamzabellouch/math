import OAI.RepresentationTheory.RowColumn.Dephasing
import OAI.RepresentationTheory.RowColumn.TensorFilter

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J B : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Rectangular coordinate inclusion for an actual injective index map. -/
def indexInclusion (e : J ↪ I) : Matrix I J ℂ := fun i j => if i=e j then 1 else 0

omit [Fintype J] in
lemma indexInclusion_star_mul (e : J ↪ I) : (indexInclusion e).conjTranspose * indexInclusion e=1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,indexInclusion,Matrix.one_apply]
  simp only [apply_ite,star_one,star_zero]
  rw [Finset.sum_eq_single (e i)]
  · simp only [ite_true,one_mul,e.injective.eq_iff]
    split_ifs <;> rfl
  · intro b _ hb
    simp [hb]
  · simp

def extendMatrix (e : J ↪ I) (A : Matrix J J ℂ) : Matrix I I ℂ := indexInclusion e * A * (indexInclusion e).conjTranspose

omit [Fintype I] in
lemma indexInclusion_mul (e : J ↪ I) (A : Matrix J J ℂ) (i j : J) :
    (indexInclusion e * A) (e i) j = A i j := by
  simp [Matrix.mul_apply,indexInclusion,e.injective.eq_iff]

omit [Fintype I] in
lemma extendMatrix_apply (e : J ↪ I) (A : Matrix J J ℂ) (i j : J) :
    extendMatrix e A (e i) (e j)=A i j := by
  simp only [extendMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,indexInclusion,
    apply_ite,star_one,star_zero,e.injective.eq_iff]
  simp

omit [Fintype I] [DecidableEq J] in
lemma extendMatrix_eq_zero_left (e : J ↪ I) (A : Matrix J J ℂ) (i : I) (hi : i ∉ Set.range e) (j : I) :
    extendMatrix e A i j=0 := by
  have hh : ∀ k, i≠e k := by intro k he; exact hi ⟨k,he.symm⟩
  simp [extendMatrix,Matrix.mul_apply,indexInclusion,hh]

omit [Fintype I] [DecidableEq J] in
lemma extendMatrix_eq_zero_right (e : J ↪ I) (A : Matrix J J ℂ) (i : I) (j : I) (hj : j ∉ Set.range e) :
    extendMatrix e A i j=0 := by
  have hh : ∀ k, j≠e k := by intro k he; exact hj ⟨k,he.symm⟩
  simp [extendMatrix,Matrix.mul_apply,indexInclusion,Matrix.conjTranspose_apply,hh]

omit [DecidableEq J] in
lemma extendMatrix_positive (e : J ↪ I) (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    (extendMatrix e A).PosSemidef := hA.mul_mul_conjTranspose_same _

lemma extendMatrix_trace (e : J ↪ I) (A : Matrix J J ℂ) :
    (extendMatrix e A).trace=A.trace := by
  rw [extendMatrix,Matrix.trace_mul_cycle,indexInclusion_star_mul,one_mul]

variable [Fintype B] [DecidableEq B]
def blockMask (b : I → B) (k : B) : Matrix I I ℂ := Matrix.diagonal (fun i => if b i=k then 1 else 0)
def pinchMatrix (b : I → B) (A : Matrix I I ℂ) : Matrix I I ℂ := ∑ k, blockMask b k * A * blockMask b k

omit [Fintype I] [Fintype B] in
lemma blockMask_hermitian (b : I → B) (k : B) : (blockMask b k).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  split_ifs <;> simp

lemma pinchMatrix_apply (b : I → B) (A : Matrix I I ℂ) (i j : I) :
    pinchMatrix b A i j = if b i=b j then A i j else 0 := by
  simp only [pinchMatrix,Matrix.sum_apply,blockMask,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [Finset.sum_eq_single (b i)]
  · simp only [ite_true,one_mul]
    by_cases h : b i=b j
    · simp [h]
    · simp [h,Ne.symm h]
  · intro k _ hk
    rw [ite_eq_right (Ne.symm hk),zero_mul,zero_mul]
  · simp

lemma pinchMatrix_positive (b : I → B) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    (pinchMatrix b A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply Finset.sum_nonneg
  intro k _
  have hh := hA.conjTranspose_mul_mul_same (blockMask b k)
  rw [(blockMask_hermitian b k).eq] at hh
  exact hh.nonneg

lemma pinchMatrix_trace (b : I → B) (A : Matrix I I ℂ) : (pinchMatrix b A).trace=A.trace := by
  unfold Matrix.trace Matrix.diag
  simp_rw [pinchMatrix_apply,ite_true]

lemma pinchMatrix_support (b : I → B) (A : Matrix I I ℂ) (i j : I) (h : b i ≠ b j) :
    pinchMatrix b A i j=0 := by rw [pinchMatrix_apply,ite_eq_right h]
end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma quadratic_eq_energy (A : Matrix I I ℂ) (x : I → ℂ) :
    quadratic A x = RowColumn.energy (Matrix.toEuclideanLin A) (WithLp.toLp 2 (star x)) := by
  unfold quadratic RowColumn.energy
  apply congrArg Complex.re
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, RCLike.inner_apply,
    Pi.star_apply, starRingEnd_apply, star_star, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma posSemidef_of_quadratic (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (h : ∀ x, 0 ≤ quadratic A x) : A.PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr hA, fun x => ?_⟩
  have hh := h (star (WithLp.ofLp x))
  rw [quadratic_eq_energy] at hh
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x ((Matrix.toEuclideanLin A) x)).re
  simpa only [star_star, WithLp.toLp_ofLp, RowColumn.energy] using hh

omit [DecidableEq I] in
lemma quadratic_smul (t : ℝ) (A : Matrix I I ℂ) (x : I → ℂ) :
    quadratic (t • A) x = t * quadratic A x := by
  unfold quadratic
  simp only [Matrix.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

omit [DecidableEq I] in
lemma quadratic_sub (A B : Matrix I I ℂ) (x : I → ℂ) :
    quadratic (A-B) x = quadratic A x-quadratic B x := by
  simp [quadratic, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq I] in
lemma quadratic_sum {D : Type*} [Fintype D] (A : D → Matrix I I ℂ) (x : I → ℂ) :
    quadratic (∑ d, A d) x = ∑ d, quadratic (A d) x := by
  simp only [quadratic, Matrix.sum_apply, Finset.sum_mul, Complex.re_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  exact Finset.sum_comm

lemma le_of_quadratic_le (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, quadratic A x ≤ quadratic B x) : A ≤ B := by
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef]
  exact posSemidef_of_quadratic (B-A) (hB.sub hA) (fun x => by rw [quadratic_sub]; exact sub_nonneg.mpr (h x))

lemma quadratic_pinch {B : Type*} [Fintype B] [DecidableEq B]
    (b : I → B) (A : Matrix I I ℂ) (x : I → ℂ) :
    quadratic (pinchMatrix b A) x = ∑ z : B, quadratic A (fun i => if b i=z then x i else 0) := by
  simp only [quadratic, pinchMatrix_apply, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (b i)]
  · by_cases h : b i=b j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

end RowColumn.MatrixState

namespace RowColumn.Signed
open RowColumn.MatrixState CubeShuffle.Specht
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}

/-- Matrix in the actual orthonormal word basis, with no change of representation. -/
def intertwinerMatrix (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) :
    Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm T.toLinearMap.toContinuousLinearMap

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_apply (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (w v : Words (S := S) odd k) :
    intertwinerMatrix line T w v=T (wordVector v) w := by
  rw [← matrix_wordVector odd k (intertwinerMatrix line T) w v]
  simp only [intertwinerMatrix, StarAlgEquiv.apply_symm_apply]
  rfl

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_positive (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    (intertwinerMatrix line T).PosSemidef := by
  rw [← toEuclideanCLM_positive_iff]
  rw [intertwinerMatrix, StarAlgEquiv.apply_symm_apply,
    ← ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact hT

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma parityPattern_eq_iff (w v : Words (S := S) odd k) :
    parityPattern w=parityPattern v ↔ ∀ i, odd (w.1 i) ↔ odd (v.1 i) := by
  simp [parityPattern, funext_iff]

omit [Fintype L] [DecidableEq L] in
lemma pinch_intertwiner_invariant (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (g : lineGroup line)
    (w v : Words (S := S) odd k) :
    pinchMatrix parityPattern (intertwinerMatrix line T) (actWord g.1 w) (actWord g.1 v) =
      pinchMatrix parityPattern (intertwinerMatrix line T) w v := by
  have hp : parityPattern (actWord g.1 w)=parityPattern (actWord g.1 v) ↔ parityPattern w=parityPattern v := by
    simp only [parityPattern_eq_iff, actWord_apply]
    constructor
    · intro h i; simpa using h (g.1 i)
    · intro h i; exact h _
  simp only [pinchMatrix_apply, hp]
  by_cases h : parityPattern w=parityPattern v
  · simp only [h, ite_true, intertwinerMatrix_apply]
    have hr := commuting_coefficient_relation line T g w v
    rw [oddPerm_parity_congr g.1 w v (parityPattern_eq_iff w v |>.mp h)] at hr
    have hs := congrArg (fun z => permSign (oddPerm g.1 v)*z) hr
    simpa only [← mul_assoc, permSign_sq, one_mul] using hs
  · simp only [h, ite_false]

omit [DecidableEq L] in
lemma intertwiner_le_pinch (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    intertwinerMatrix line T ≤
      (((Fintype.card S+1)^(Fintype.card L*Fintype.card C^2) : ℕ) : ℝ) •
        pinchMatrix parityPattern (intertwinerMatrix line T) := by
  have hM := intertwinerMatrix_positive line T hT
  apply le_of_quadratic_le _ _ hM.isHermitian
    ((pinchMatrix_positive parityPattern _ hM).smul (by positivity : (0 : ℝ) ≤ _)).isHermitian
  intro x
  rw [quadratic_smul, quadratic_pinch]
  simp only [quadratic_eq_energy]
  have he : Matrix.toEuclideanLin (intertwinerMatrix line T)=T.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap ((Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply T.toLinearMap.toContinuousLinearMap)
  rw [he]
  convert line_signed_parity_dephasing line T hT (WithLp.toLp 2 (star x)) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ext w
  simp only [parityMask, WithLp.ofLp_toLp, Pi.star_apply]
  split_ifs <;> simp

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] in
lemma extendMatrix_equiv (e : J ↪ I) (p : Equiv.Perm I) (q : Equiv.Perm J)
    (he : ∀ j, p (e j)=e (q j)) (A : Matrix J J ℂ)
    (hA : ∀ i j, A (q i) (q j)=A i j) (i j : I) :
    extendMatrix e A (p i) (p j)=extendMatrix e A i j := by
  have hh (x : I) (hx : x ∉ Set.range e) : p x ∉ Set.range e := by
    rintro ⟨k,hk⟩
    apply hx
    refine ⟨q.symm k, p.injective ?_⟩
    rw [he, Equiv.apply_symm_apply, hk]
  by_cases hi : i ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hj
      rw [he, he, extendMatrix_apply, extendMatrix_apply, hA]
    · rw [extendMatrix_eq_zero_right e A _ _ (hh j hj), extendMatrix_eq_zero_right e A _ _ hj]
  · rw [extendMatrix_eq_zero_left e A _ (hh i hi), extendMatrix_eq_zero_left e A _ hi]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma submatrix_mono (A B : Matrix I I ℂ) (h : A ≤ B) (e : J → I) :
    A.submatrix e e ≤ B.submatrix e e := by
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef] at h ⊢
  exact h.submatrix e

end RowColumn.MatrixState

namespace RowColumn.Signed
open RowColumn.MatrixState RowColumn.Postselection RowColumn.WordOrbits
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] (odd : C → Prop) [DecidablePred odd] (k : ℕ)

def wordInclusion : Words (S := S) odd k ↪ (S → C) := ⟨Subtype.val, Subtype.val_injective⟩

def extendedPinch (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) : Matrix (S → C) (S → C) ℂ :=
  extendMatrix (wordInclusion odd k) (pinchMatrix parityPattern (intertwinerMatrix line T))

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_positive (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    (extendedPinch odd k line T).PosSemidef :=
  extendMatrix_positive _ _ (pinchMatrix_positive _ _ (intertwinerMatrix_positive line T hT))

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_trace (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) :
    (extendedPinch odd k line T).trace = (intertwinerMatrix line T).trace := by
  rw [extendedPinch, extendMatrix_trace, pinchMatrix_trace]

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_invariant (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (p : Equiv.Perm S)
    (hp : ∀ i, line (p i)=line i) (w v : S → C) :
    extendedPinch odd k line T (w ∘ p) (v ∘ p)=extendedPinch odd k line T w v := by
  let g : lineGroup line := ⟨p⁻¹, (lineGroup line).inv_mem hp⟩
  apply extendMatrix_equiv (wordInclusion odd k) (reindexWord p) (wordsEquiv g.1)
  · intro j
    ext i
    change j.1 (p i) = j.1 ((p⁻¹)⁻¹ i)
    rw [inv_inv]
  · exact pinch_intertwiner_invariant line T g

omit [Fintype L] [DecidableEq L] in
lemma extendedPinch_support (line : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (w v : S → C)
    (h : ¬ ∀ i, odd (w i) ↔ odd (v i)) : extendedPinch odd k line T w v=0 := by
  by_cases hw : w ∈ Set.range (wordInclusion (S := S) odd k)
  · obtain ⟨w,rfl⟩ := hw
    by_cases hv : v ∈ Set.range (wordInclusion (S := S) odd k)
    · obtain ⟨v,rfl⟩ := hv
      rw [extendedPinch, extendMatrix_apply]
      apply pinchMatrix_support
      exact fun he => h ((parityPattern_eq_iff w v).mp he)
    · exact extendMatrix_eq_zero_right _ _ _ _ hv
  · exact extendMatrix_eq_zero_left _ _ _ hw _

/-- Finite positive even product-state majorant of the true signed line
commutant. Both parity bandwidth and the local-state normalization are retained. -/
theorem signed_line_postselection (line : S → L) (a₀ : S → C × C)
    (hn : 0 < Fintype.card S)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    intertwinerMatrix line T ≤
      ((((Fintype.card S+1)^(Fintype.card L*Fintype.card C^2) : ℕ) : ℝ) *
        (intertwinerMatrix line T).trace.re *
        (((Fintype.card S+1)^(Fintype.card (L × (C × C))) : ℕ) /
          (Fintype.card (Phases (L × (C × C)) (Fintype.card S)) : ℝ))) •
      (∑ q : Types (S := S) (A := L × (C × C)),
        ∑ θ : Phases (L × (C × C)) (Fintype.card S),
          sectorTensor odd k (fun i => lineState line a₀ odd q θ (line i))) := by
  let A := extendedPinch odd k line T
  let B := ∑ q : Types (S := S) (A := L × (C × C)),
    ∑ θ : Phases (L × (C × C)) (Fintype.card S),
      tensorMatrix (fun i : S => lineState line a₀ odd q θ (line i))
  let t : ℝ := (intertwinerMatrix line T).trace.re *
    (((Fintype.card S+1)^(Fintype.card (L × (C × C))) : ℕ) /
      (Fintype.card (Phases (L × (C × C)) (Fintype.card S)) : ℝ))
  have hA : A.PosSemidef := extendedPinch_positive odd k line T hT
  have ht : 0 ≤ t := mul_nonneg (by
    have hh := (intertwinerMatrix_positive line T hT).trace_nonneg
    exact hh.1) (by positivity)
  have hB : B.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro q _
    apply Finset.sum_nonneg
    intro θ _
    exact (tensorMatrix_posSemidef _ (fun i => lineState_positive line a₀ odd q θ (line i))).nonneg
  have hab : A ≤ t • B := by
    apply le_of_quadratic_le _ _ hA.isHermitian (hB.smul ht).isHermitian
    intro x
    simp only [quadratic_smul, B, quadratic_sum]
    have hh := positive_line_postselection line a₀ hn odd A hA
      (extendedPinch_invariant odd k line T) (extendedPinch_support odd k line T) x
    simpa only [A, extendedPinch_trace, t, mul_assoc] using hh
  have hsub := submatrix_mono A (t • B) hab (Subtype.val : Words (S := S) odd k → S → C)
  have hleft : A.submatrix Subtype.val Subtype.val=pinchMatrix parityPattern (intertwinerMatrix line T) := by
    ext w v
    exact extendMatrix_apply (wordInclusion odd k) _ w v
  rw [hleft] at hsub
  have hs := smul_le_smul_of_nonneg_left hsub
    (by positivity : (0 : ℝ) ≤ (((Fintype.card S+1)^(Fintype.card L*Fintype.card C^2) : ℕ) : ℝ))
  apply (intertwiner_le_pinch line T hT).trans
  convert hs using 1
  ext w v
  simp only [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.sum_apply, B, t,
    sectorTensor, smul_smul, mul_assoc]

end RowColumn.Signed

end
end

end OAI
