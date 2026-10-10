import OAI.RepresentationTheory.SpinAngle.Compression

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators



namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MatrixAnalysis TensorMatrix
variable {q : ℕ} [contextInstance30_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance31_23 : Fintype R] [contextInstance31_35 : DecidableEq R] [contextInstance31_51 : Fintype C] [contextInstance31_63 : DecidableEq C]

def row (W : Finset (R × C)) (w : W) : R := w.val.1
def column (W : Finset (R × C)) (w : W) : C := w.val.2

def phi (W : Finset (R × C)) : ℝ :=
  missingCellProductFactor (Fintype.card C) (missingInRow W)

def columnRoot (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun x : W => root (A x.val.2).matrix)
def meanRoot [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun _ : W => root (EvenDensity.mean A).matrix)
def meanInvRoot [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun _ : W => invRoot (EvenDensity.mean A).matrix)
def meanSupport [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :=
  tensor (fun _ : W => support (EvenDensity.mean A).matrix)
def rowRoot (W : Finset (R × C)) (B : R → EvenDensity q) :=
  tensor (fun x : W => root (B x.val.1).matrix)

lemma columnRoot_support
    {q : ℕ} [Nonempty (Fin q)] {R : Type*} {C : Type*}
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :
    columnRoot W A * meanSupport W A = columnRoot W A := by
  apply tensor_root_mul_support_of_le_smul
    (fun x : W => (A x.val.2).matrix) (fun _ : W => (EvenDensity.mean A).matrix)
    (fun x => (A x.val.2).nonneg) (fun _ => (EvenDensity.mean A).nonneg) (Fintype.card C)
  intro x
  rw [EvenDensity.mean_matrix]
  exact le_smul_average (fun j => (A j).toDensity) x.val.2

lemma meanRoot_eq
    {q : ℕ} [Nonempty (Fin q)] {R : Type*} {C : Type*}
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Nonempty C] (W : Finset (R × C)) (A : C → EvenDensity q) :
    meanRoot W A = root (tensor (fun _ : W => (EvenDensity.mean A).matrix)) :=
  tensor_root _ (fun _ => (EvenDensity.mean A).nonneg)

lemma meanRoot_commute_global [Nonempty C] (W : Finset (R × C))
    (D : TypeLabel q) (A : C → EvenDensity q) :
    Commute (meanRoot W A) (D.projection W) := by
  rw [meanRoot_eq]
  exact root_commute (D.density_commute (EvenDensity.mean A))

lemma meanRoot_commute_rows [Nonempty C] (W : Finset (R × C))
    (K : R → TypeLabel q) (A : C → EvenDensity q) :
    Commute (meanRoot W A) (TypeBlocks.projection (row W) K) := by
  rw [meanRoot_eq]
  exact root_commute (TypeBlocks.density_commute (row W) K (EvenDensity.mean A))

lemma global_norm [Nonempty C] (W : Finset (R × C)) (D : TypeLabel q)
    (A : C → EvenDensity q) :
    ‖D.projection W * meanRoot W A‖ ^ 2 ≤ Real.exp (-D.entropy) := by
  have hs : IsSelfAdjoint (meanRoot W A) :=
    tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)
  rw [Analytic.norm_projection_sqrt_sq _ _ (D.projection_isStarProjection W)
    hs (meanRoot_commute_global W D A)]
  change ‖(tensor (fun _ : W => root (EvenDensity.mean A).matrix) *
    tensor (fun _ : W => root (EvenDensity.mean A).matrix)) * D.projection W‖ ≤ _
  rw [tensor_root_square _ (fun _ => (EvenDensity.mean A).nonneg)]
  exact D.density_upper (EvenDensity.mean A)

lemma cell_norm
    {q : ℕ} [Nonempty (Fin q)] {R : Type*} {C : Type*}
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Nonempty C] (W : Finset (R × C))
    (A : C → EvenDensity q) (B : R → EvenDensity q) :
    ‖columnRoot W A * meanInvRoot W A * rowRoot W B‖ ^ 2 ≤ phi W := by
  unfold columnRoot meanInvRoot rowRoot
  rw [← tensor_mul, ← tensor_mul, EvenDensity.mean_matrix]
  exact normalized_board_bound W (fun c => (A c).toDensity) (fun r => (B r).toDensity)




theorem nonempty_columns [Nonempty C] (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q) :
    ‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) := by
  classical
  obtain ⟨ι,hι,w,A,hw,hsw,hH⟩ := TypeBlocks.density_mixture (column W) H
  obtain ⟨κ,hκ,z,B,hz,hsz,hK⟩ := TypeBlocks.density_mixture (row W) K
  let := hι
  let := hκ
  let M (i : ι) : EvenDensity q := EvenDensity.mean (A i)
  let r (i : ι) := columnRoot W (A i)
  let v (i : ι) := meanInvRoot W (A i)
  let t (i : ι) := meanRoot W (A i)
  let Q (i : ι) := meanSupport W (A i)
  let s (j : κ) := rowRoot W (B j)
  let P := D.projection W
  let PH := TypeBlocks.projection (column W) H
  let PK := TypeBlocks.projection (row W) K
  have hp : IsStarProjection P := D.projection_isStarProjection W
  have hh : IsStarProjection PH := TypeBlocks.projection_isStarProjection _ _
  have hk : IsStarProjection PK := TypeBlocks.projection_isStarProjection _ _
  have hrstar (i : ι) : star (r i) = r i :=
    (tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)).star_eq
  have hsstar (j : κ) : star (s j) = s j :=
    (tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)).star_eq
  have htstar (i : ι) : IsSelfAdjoint (t i) :=
    tensor_selfAdjoint _ (fun _ => root_selfAdjoint _)
  have hr (i : ι) : star (r i) * r i = tensor (fun x : W => (A i x.val.2).matrix) := by
    rw [hrstar]
    exact tensor_root_square _ (fun x => (A i x.val.2).nonneg)
  have hss (j : κ) : s j * star (s j) = tensor (fun x : W => (B j x.val.1).matrix) := by
    rw [hsstar]
    exact tensor_root_square _ (fun x => (B j x.val.1).nonneg)
  have hdomH : PH ≤ ∑ i, w i • (star (r i) * r i) := by
    simpa only [hr, PH, column] using hH
  have hdomK : PK ≤ ∑ j, z j • (s j * star (s j)) := by
    simpa only [hss, PK, row] using hK
  have hvt (i : ι) : v i * t i = Q i :=
    tensor_invRoot_mul_root _ (fun _ => (M i).nonneg)
  have hrQ (i : ι) : r i * Q i = r i := columnRoot_support W (A i)
  have htk (i : ι) : Commute (t i) PK := meanRoot_commute_rows W K (A i)
  have htp (i : ι) : Commute (t i) P := meanRoot_commute_global W D (A i)
  have hglobal (i : ι) : ‖P * t i‖ ^ 2 ≤ Real.exp (-D.entropy) := global_norm W D (A i)
  have hcell (i : ι) (j : κ) : ‖r i * v i * s j‖ ^ 2 ≤ phi W := cell_norm W (A i) (B j)
  have h := Analytic.three_projection_angle_of_density_mixtures PH PK P hh hk hp w z hw hz
    r v t Q s hdomH hdomK hvt hrQ htk htp (Real.exp (-D.entropy)) (phi W)
    (Real.exp_pos _).le (boardPhi_nonneg W) hglobal hcell
  rw [hsw,hsz] at h
  convert h using 2
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]
  ring
end SpinAngle.TypeAngle

namespace SpinAngle.TypeBlocks
open scoped BigOperators
variable {q : ℕ}
variable {τ J : Type*} [contextInstance157_23 : Fintype τ] [contextInstance157_35 : DecidableEq τ] [contextInstance157_51 : Fintype J] [contextInstance157_63 : DecidableEq J]

lemma dimension_pos {q : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (D : J → TypeLabel q) : 0 < dimension D :=
  Finset.prod_pos fun j _ => (D j).dimension_pos

lemma dimension_le {q : ℕ} {τ : Type*} {J : Type*}
    [Fintype τ] [DecidableEq τ] [Fintype J] [DecidableEq J] (f : τ → J) (D : J → TypeLabel q)
    (hsize : ∀ j, (D j).size = Fintype.card (Fiber f j)) :
    dimension D ≤ (Fintype.card τ + 1) ^ (Fintype.card J * (q*(q-1))) := by
  have h (j : J) : (D j).dimension ≤ (Fintype.card τ + 1) ^ (q*(q-1)) := by
    apply (D j).dimension_le.trans
    apply Nat.pow_le_pow_left
    rw [hsize]
    exact Nat.add_le_add_right (Fintype.card_subtype_le _) 1
  calc
    dimension D ≤ ∏ _j : J, (Fintype.card τ + 1) ^ (q*(q-1)) :=
      Finset.prod_le_prod₀ (fun j _ => Nat.zero_le _) (fun j _ => h j)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]; congr 1; exact Nat.mul_comm _ _
end SpinAngle.TypeBlocks

namespace SpinAngle.TypeAngle
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {q : ℕ} [contextInstance179_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance180_23 : Fintype R] [contextInstance180_35 : DecidableEq R] [contextInstance180_51 : Fintype C] [contextInstance180_63 : DecidableEq C]



theorem one_sided_type_angle (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q)
    (hD : D.size = W.card)
    (hH : ∀ j, (H j).size = Fintype.card (TypeBlocks.Fiber (column W) j))
    (hK : ∀ i, (K i).size = Fintype.card (TypeBlocks.Fiber (row W) i)) :
    (‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W)) ∧
    (min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy +
        (Fintype.card R * Fintype.card C - W.card : ℕ)) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ))) ∧
    TypeBlocks.dimension H * TypeBlocks.dimension K ≤
      (W.card + 1) ^ ((Fintype.card R + Fintype.card C) * q * (q-1)) := by
  classical
  have hangle : ‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) := by
    cases isEmpty_or_nonempty C with
    | inr h => exact nonempty_columns W D H K
    | inl h =>
      have hW : W = ∅ := Finset.eq_empty_of_isEmpty W
      have hd : D.entropy = 0 := D.entropy_eq_zero_of_size_zero (by simpa [hW] using hD)
      have hksize (i : R) : (K i).size = 0 := by simpa [hW] using hK i
      have hkentropy : TypeBlocks.entropy K = 0 := by
        simp only [TypeBlocks.entropy, fun i => (K i).entropy_eq_zero_of_size_zero (hksize i), Finset.sum_const_zero]
      have hphi : phi W = 1 := by simp [phi, missingCellProductFactor, missingCellFactor]
      have hdim : 1 ≤ (TypeBlocks.dimension K : ℝ) := by
        exact_mod_cast TypeBlocks.dimension_pos K
      have hnorm := Analytic.norm_three_projections_sq_le_one
        (TypeBlocks.projection (column W) H) (TypeBlocks.projection (row W) K) (D.projection W)
        (TypeBlocks.projection_isStarProjection _ _) (TypeBlocks.projection_isStarProjection _ _)
        (D.projection_isStarProjection W)
      have hhent : TypeBlocks.entropy H = 0 := by simp [TypeBlocks.entropy]
      have hhdim : TypeBlocks.dimension H = 1 := by simp [TypeBlocks.dimension]
      simpa only [hhent, hhdim, Nat.cast_one, hd, hkentropy, hphi, add_zero,
        sub_zero, Real.exp_zero, one_mul, mul_one, min_eq_left hdim] using hnorm
  refine ⟨hangle, ?_, ?_⟩
  · apply min_le_min_left
    have h := mul_le_mul_of_nonneg_left (boardPhi_le_exp_holes W)
      (mul_nonneg (mul_nonneg (Real.exp_pos (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy)).le (Nat.cast_nonneg (TypeBlocks.dimension H)))
        (Nat.cast_nonneg (TypeBlocks.dimension K)))
    convert h using 1 <;> simp only [phi, Real.exp_add] ; ring
  · have h := Nat.mul_le_mul (TypeBlocks.dimension_le (column W) H hH)
      (TypeBlocks.dimension_le (row W) K hK)
    rw [← pow_add] at h
    simpa only [Fintype.card_coe, show Fintype.card C * (q * (q-1)) + Fintype.card R * (q * (q-1)) =
        (Fintype.card R + Fintype.card C) * q * (q-1) by ring] using h
end SpinAngle.TypeAngle

end

end OAI
