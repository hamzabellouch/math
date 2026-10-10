import Mathlib
import OAI.RepresentationTheory.Unitary.Basic
import OAI.Analysis.Matrix.TensorMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma projector_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) :
    Matrix.trace (ρ.projector τ) = (ρ.dimension : ℂ) *
      Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
  simp only [projector,Matrix.trace_sum,Matrix.trace_smul,coefficient,smul_eq_mul]
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        ∑ g, Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by
      rw [ρ.character_sum_multiplicity τ]
      have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

lemma dimension_le_of_projector_one (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    [Nonempty n] (h : ρ.projector τ = 1) : ρ.dimension ≤ Fintype.card n := by
  have he := ρ.projector_trace τ
  rw [h,Matrix.trace_one] at he
  have he' : Fintype.card n = ρ.dimension *
    Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by exact_mod_cast he
  have hm : 0 < Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
    have hn := Fintype.card_pos (α := n)
    by_contra hh
    have hz := Nat.eq_zero_of_not_pos hh
    rw [hz,mul_zero] at he'
    omega
  rw [he']
  exact Nat.le_mul_of_pos_right _ hm

lemma projector_map (ρ : UnitaryIrrep Γ) {m : Type*} [Fintype m] [DecidableEq m]
    (e : Matrix n n ℂ →ₐ[ℂ] Matrix m m ℂ) (τ : Γ →* Matrix n n ℂ) :
    ρ.projector (e.toMonoidHom.comp τ) = e (ρ.projector τ) := by
  change (∑ g, ρ.coefficient g • e (τ g)) = e (∑ g, ρ.coefficient g • τ g)
  simp only [map_sum,map_smul]

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.SpectralBlock
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Level (r : n → ℝ) (v : ℝ) := {i : n // r i=v}

omit [DecidableEq n] in
lemma mul_restrict (r : n → ℝ) (v : ℝ) (A B : Matrix n n ℂ)
    (hA : ∀ i j, r i ≠ r j → A i j=0) :
    (A*B).submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) =
      A.submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) * B.submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) := by
  ext i j
  rw [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => r k=v)]
  have hz : ∑ k : {k : n // ¬ r k=v}, A i.val k.val * B k.val j.val = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hne : r i.val ≠ r k.val := by rw [i.property]; exact Ne.symm k.property
    rw [hA _ _ hne,zero_mul]
  rw [hz,add_zero]
  rfl

def representation (τ : Γ →* Matrix n n ℂ) (r : n → ℝ) (v : ℝ)
    (hτ : ∀ g i j, r i ≠ r j → τ g i j=0) : Γ →* Matrix (Level r v) (Level r v) ℂ where
  toFun g := (τ g).submatrix Subtype.val Subtype.val
  map_one' := by
    rw [map_one]
    ext i j
    simp [Matrix.one_apply,Subtype.val_inj]
  map_mul' g h := by
    rw [map_mul]
    exact mul_restrict r v (τ g) (τ h) (hτ g)

lemma projector_representation (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (r : n → ℝ) (v : ℝ) (hτ : ∀ g i j, r i ≠ r j → τ g i j=0) :
    ρ.projector (representation τ r v hτ) =
      (ρ.projector τ).submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) := by
  ext i j
  simp [UnitaryIrrep.projector,Matrix.sum_apply,representation]

omit [Fintype Γ] in
lemma offDiagonal_zero (τ : Γ →* Matrix n n ℂ) (r : n → ℝ)
    (hτ : ∀ g, τ g * Matrix.diagonal (fun i => (r i : ℂ)) =
      Matrix.diagonal (fun i => (r i : ℂ)) * τ g) :
    ∀ g i j, r i ≠ r j → τ g i j=0 := by
  intro g i j hij
  have he := congrArg (fun M : Matrix n n ℂ => M i j) (hτ g)
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at he
  by_contra hn
  apply hij
  exact Complex.ofReal_injective (mul_left_cancel₀ hn (he.trans (mul_comm _ _))).symm

lemma projector_on_level (P : Matrix n n ℂ) (r : n → ℝ) (v : ℝ) (hv : v ≠ 0)
    (hP : P * Matrix.diagonal (fun i => (r i : ℂ)) = Matrix.diagonal (fun i => (r i : ℂ))) :
    P.submatrix (Subtype.val : Level r v → n) (Subtype.val : Level r v → n) = 1 := by
  ext i j
  have he := congrArg (fun M : Matrix n n ℂ => M i.val j.val) hP
  simp only [Matrix.mul_diagonal,Matrix.diagonal_apply] at he
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  apply mul_right_cancel₀ hv'
  change P i.val j.val * (v : ℂ) = (1 : Matrix (Level r v) (Level r v) ℂ) i j * (v : ℂ)
  simpa only [i.property,j.property,Matrix.one_apply,Subtype.val_inj,ite_mul,one_mul,zero_mul] using he

omit [DecidableEq n] in
lemma level_card_le_trace (r : n → ℝ) (hr : ∀ i, 0 ≤ r i) (v : ℝ) :
    Fintype.card (Level r v) * v ≤ ∑ i, r i := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => r i=v)]
  have he : ∑ i : Level r v, r i.val = Fintype.card (Level r v) * v := by
    simp_rw [show ∀ i : Level r v, r i.val = v from fun i => i.property]
    simp
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hr i.val))

/- Positive spectral blocks supported on an actual character projector have
at least the actual irreducible dimension. No decomposition is assumed. -/
lemma dimension_mul_eigenvalue_le_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (r : n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hτ : ∀ g, τ g * Matrix.diagonal (fun i => (r i : ℂ)) =
      Matrix.diagonal (fun i => (r i : ℂ)) * τ g)
    (hP : ρ.projector τ * Matrix.diagonal (fun i => (r i : ℂ)) = Matrix.diagonal (fun i => (r i : ℂ)))
    (i : n) : (ρ.dimension : ℝ)*r i ≤ ∑ j, r j := by
  by_cases hi : r i=0
  · simp only [hi,mul_zero]
    exact Finset.sum_nonneg (fun j _ => hr j)
  · let : Nonempty (Level r (r i)) := ⟨⟨i,rfl⟩⟩
    have hzero := offDiagonal_zero τ r hτ
    have hproj : ρ.projector (representation τ r (r i) hzero) = 1 := by
      rw [projector_representation]
      exact projector_on_level _ _ _ hi hP
    have hc := ρ.dimension_le_of_projector_one (representation τ r (r i) hzero) hproj
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hr i)).trans
      (level_card_le_trace r hr (r i))
end CoordinateSweeps.SpectralBlock

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

/- Source06's dimension-normalized spectral estimate, for every genuine
finite group representation. A is supported on the actual central projection. -/
theorem supported_trace_domination (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (hcomm : ∀ g, τ g * A = A * τ g) (hP : ρ.projector τ * A = A) :
    (Matrix.trace A • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let e := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star U)).toAlgEquiv.toAlgHom
  let r := hA.isHermitian.eigenvalues
  let d : n → ℂ := RCLike.ofReal ∘ r
  let τ' : Γ →* Matrix n n ℂ := e.toMonoidHom.comp τ
  have hdiag : e A = Matrix.diagonal d := hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hcomm' (g : Γ) : τ' g * Matrix.diagonal d = Matrix.diagonal d * τ' g := by
    change e (τ g) * Matrix.diagonal d = Matrix.diagonal d * e (τ g)
    rw [← hdiag,← map_mul,← map_mul,hcomm g]
  have hP' : ρ.projector τ' * Matrix.diagonal d = Matrix.diagonal d := by
    rw [ρ.projector_map e τ,← hdiag,← map_mul,hP]
  have hi (i : n) : (ρ.dimension : ℝ)*r i ≤ ∑ j, r j :=
    SpectralBlock.dimension_mul_eigenvalue_le_trace ρ τ' r hA.eigenvalues_nonneg hcomm' hP' i
  have hd (i : n) : (0 : ℂ) ≤ Matrix.trace A - (ρ.dimension : ℂ)*d i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    change (0 : ℂ) ≤ (∑ j, (r j : ℂ)) - (ρ.dimension : ℂ)*(r i : ℂ)
    exact_mod_cast sub_nonneg.mpr (hi i)
  have hD := Matrix.PosSemidef.diagonal hd
  have h := hD.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ).conjTranspose = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hspec : (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ).conjTranspose = A := by
    simpa only [U,d,r,Function.comp_def,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem.symm
  have he : Matrix.diagonal (fun i => Matrix.trace A - (ρ.dimension : ℂ)*d i) =
      Matrix.trace A • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
  simpa only [he,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hU,hspec] using h

/- Compression of a positive invariant unit-trace operator to any isotypic
type is at most inverse irreducible dimension in operator order. -/
theorem invariant_projector_trace_domination (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (T : Matrix n n ℂ) (hT : T.PosSemidef)
    (hcomm : ∀ g, τ g*T=T*τ g) :
    (Matrix.trace T • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) •
      (ρ.projector τ * T * ρ.projector τ)).PosSemidef := by
  let P := ρ.projector τ
  have hP : P.conjTranspose=P := ρ.projector_hermitian τ hu
  have hP2 : P*P=P := ρ.projector_idempotent τ
  let A := P*T*P
  have hA : A.PosSemidef := by
    simpa only [hP] using hT.mul_mul_conjTranspose_same P
  have hAc (g : Γ) : τ g*A=A*τ g := by
    dsimp [A]
    calc
      _ = (τ g*P)*T*P := by noncomm_ring
      _ = (P*τ g)*T*P := by rw [ρ.projector_commute τ g]
      _ = P*(τ g*T)*P := by noncomm_ring
      _ = P*(T*τ g)*P := by rw [hcomm]
      _ = P*T*(τ g*P) := by noncomm_ring
      _ = P*T*(P*τ g) := by rw [ρ.projector_commute τ g]
      _ = _ := by noncomm_ring
  have hPA : P*A=A := by dsimp [A]; rw [← mul_assoc,← mul_assoc,hP2]
  have hbound := ρ.supported_trace_domination τ A hA hAc hPA
  have htrace : Matrix.trace A ≤ Matrix.trace T := by
    have hc := hT.mul_mul_conjTranspose_same (1-P)
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP] at hc
    have hh := hc.trace_nonneg
    have he : Matrix.trace ((1-P)*T*(1-P)) = Matrix.trace T-Matrix.trace A := by
      dsimp [A]
      have hx : (1-P)*(1-P) = 1-P := by
        calc
          _ = 1-P-P+P*P := by noncomm_ring
          _ = _ := by rw [hP2]; module
      rw [Matrix.trace_mul_cycle,hx,sub_mul,one_mul,Matrix.trace_sub]
      rw [Matrix.trace_mul_cycle P T P,hP2]

    rw [he] at hh
    exact sub_nonneg.mp hh
  have hpad := (Matrix.PosSemidef.one (n := n) (R := ℂ)).smul (sub_nonneg.mpr htrace)
  have h := hpad.add hbound
  change (Matrix.trace T • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • A).PosSemidef
  convert h using 1
  module
end CoordinateSweeps.UnitaryIrrep
namespace CoordinateSweeps.Overlap
open TensorBoard
variable {n Γ : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Group Γ] [Fintype Γ]

open scoped MatrixOrder in
lemma norm_le_trace (A : Matrix n n ℂ) (hA : A.PosSemidef) : ‖A‖ ≤ (Matrix.trace A).re := by
  have hh := PositiveTensor.trace_domination A hA
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (show A ≤ Matrix.trace A • (1 : Matrix n n ℂ) from sub_nonneg.mp hh.nonneg) hA.nonneg
  have htr := Complex.nonneg_iff.mp hA.trace_nonneg
  have he : ((Matrix.trace A).re : ℂ)=Matrix.trace A := by
    apply Complex.ext <;> simp [htr.2]
  rw [← he,norm_smul,Complex.norm_of_nonneg htr.1,norm_one,mul_one] at hn
  exact hn

lemma norm_sq_le_trace (A : Matrix n n ℂ) :
    ‖A‖^2 ≤ (Matrix.trace (A.conjTranspose*A)).re := by
  have hh := norm_le_trace _ (Matrix.posSemidef_conjTranspose_mul_self A)
  simpa only [Matrix.l2_opNorm_conjTranspose_mul_self,pow_two] using hh

omit [DecidableEq n] [Nonempty n] in
lemma projection_product_posSemidef (P Q : Matrix n n ℂ)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hQ : Q.PosSemidef) (hPQ : P*Q=Q*P) :
    (P*Q).PosSemidef := by
  have hh := hQ.mul_mul_conjTranspose_same P
  rwa [hP.eq,hPQ,mul_assoc,hP2,← hPQ] at hh

lemma overlap_norm_sq_le_trace (R Q P : Matrix n n ℂ)
    (hR : R.IsHermitian) (hR2 : R*R=R) (hQ : Q.IsHermitian) (hQ2 : Q*Q=Q)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hPQ : P*Q=Q*P) :
    ‖Q*P*R‖^2 ≤ (Matrix.trace (R*(Q*P))).re := by
  have hh := norm_sq_le_trace (Q*P*R)
  have he : (Q*P*R).conjTranspose*(Q*P*R)=R*Q*P*R := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hR.eq,hP.eq,hQ.eq]
    calc
      _ = R*P*(Q*Q)*P*R := by noncomm_ring
      _ = R*(P*Q)*P*R := by rw [hQ2]; noncomm_ring
      _ = R*Q*(P*P)*R := by rw [hPQ]; noncomm_ring
      _ = _ := by rw [hP2]
  rw [he,mul_assoc R Q P,Matrix.trace_mul_cycle R (Q*P) R,hR2] at hh
  simpa only [mul_assoc] using hh

/- Whitening of genuine isotypic trace domination. All projections and
commutations are explicit algebraic obligations; no spectral conclusion assumed. -/
omit [Nonempty n] in
lemma whitened_projector_domination (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹)
    (T A Q : Matrix n n ℂ) (hT : T.PosSemidef)
    (hcomm : ∀ g, τ g*T=T*τ g) (hA : A.IsHermitian)
    (hATA : A*T*A=1) (hAP : A*ρ.projector τ=ρ.projector τ*A)
    (hAQ : A*Q=Q*A) (hQ : Q.IsHermitian) (hQ2 : Q*Q=Q)
    (hPQ : ρ.projector τ*Q= Q*ρ.projector τ) :
    (Matrix.trace T • (A*Q*A) - (ρ.dimension : ℂ) • (Q*ρ.projector τ)).PosSemidef := by
  let P := ρ.projector τ
  change A*P=P*A at hAP
  change P*Q=Q*P at hPQ
  have hP2 : P*P=P := ρ.projector_idempotent τ
  have hh := ρ.invariant_projector_trace_domination τ hu T hT hcomm
  change (Matrix.trace T • (1 : Matrix n n ℂ) - (ρ.dimension : ℂ) • (P*T*P)).PosSemidef at hh
  have hk := (hh.mul_mul_conjTranspose_same Q).mul_mul_conjTranspose_same A
  simp only [hA.eq,hQ.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at hk
  have hAQP : A*(Q*P)=(Q*P)*A := by
    rw [← mul_assoc,hAQ,mul_assoc Q A P,hAP,← mul_assoc]
  have hPQA : (P*Q)*A=A*(P*Q) := by
    rw [mul_assoc,← hAQ,← mul_assoc P A Q,← hAP,mul_assoc]
  have ht : A*(Q*(P*T*P)*Q)*A=Q*P := by
    calc
      _ = (A*(Q*P))*T*((P*Q)*A) := by noncomm_ring
      _ = (Q*P)*(A*T*A)*(P*Q) := by rw [hAQP,hPQA]; noncomm_ring
      _ = Q*(P*P)*Q := by rw [hATA]; noncomm_ring
      _ = Q*(P*Q) := by rw [hP2,mul_assoc]
      _ = Q*(Q*P) := by rw [hPQ]
      _ = Q*P := by rw [← mul_assoc,hQ2]
  have he : A*(Q*1*Q)*A=A*Q*A := by rw [mul_one,hQ2]
  rw [he,ht] at hk
  exact hk

end CoordinateSweeps.Overlap

namespace CoordinateSweeps.Overlap
open TensorBoard
variable {n I J : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype I] [Fintype J]

omit [DecidableEq n] [Nonempty n] in
lemma trace_mixture_re (w : I → ℝ) (U : I → Matrix n n ℂ) (W : Matrix n n ℂ) :
    (Matrix.trace ((∑ i, (w i : ℂ) • U i)*W)).re = ∑ i, w i*(Matrix.trace (U i*W)).re := by
  simp only [Matrix.sum_mul,Matrix.smul_mul,Matrix.trace_sum,Matrix.trace_smul,Complex.re_sum,
    smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

omit [DecidableEq n] [Nonempty n] in
lemma trace_smul_re (t : ℝ) (W : Matrix n n ℂ) :
    (Matrix.trace ((t : ℂ) • W)).re=t*(Matrix.trace W).re := by
  simp [Matrix.trace_smul]

omit [DecidableEq n] [Nonempty n] in
lemma trace_four_swap (A Q U : Matrix n n ℂ) :
    Matrix.trace (A*Q*A*U)=Matrix.trace (A*U*A*Q) := by
  calc
    _ = Matrix.trace ((A*Q)*(A*U)) := congrArg Matrix.trace (by noncomm_ring)
    _ = Matrix.trace ((A*U)*(A*Q)) := Matrix.trace_mul_comm _ _
    _ = _ := congrArg Matrix.trace (by noncomm_ring)

/- Finite density mixtures plus genuine whitened isotypic domination give
the row-column overlap bound, before the harmless epsilon limit. -/
theorem finite_mixture_overlap (R Q P : Matrix n n ℂ)
    (hR : R.IsHermitian) (hR2 : R*R=R) (hQ : Q.IsHermitian) (hQ2 : Q*Q=Q)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hPQ : P*Q=Q*P)
    (u : I → ℝ) (v : J → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hsu : ∑ i, u i=1) (hsv : ∑ j, v j=1)
    (U : I → Matrix n n ℂ) (V : J → Matrix n n ℂ) (A : I → Matrix n n ℂ)
    (hU : ∀ i, (U i).PosSemidef) (hA : ∀ i, (A i).IsHermitian)
    (cr cc D t E : ℝ) (hcr : 0 ≤ cr) (hcc : 0 ≤ cc) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (hrow : ((cr : ℂ) • (∑ i, (u i : ℂ) • U i)-R).PosSemidef)
    (hcol : ((cc : ℂ) • (∑ j, (v j : ℂ) • V j)-Q).PosSemidef)
    (hwhite : ∀ i, ((t : ℂ) • (A i*Q*A i)-(D : ℂ) • (Q*P)).PosSemidef)
    (hpair : ∀ i j, (Matrix.trace (A i*U i*A i*V j)).re ≤ E) :
    D*‖Q*P*R‖^2 ≤ cr*cc*t*E := by
  have hQpos : Q.PosSemidef := by
    simpa only [hQ.eq,hQ2] using Matrix.posSemidef_conjTranspose_mul_self Q
  have hQP : (Q*P).PosSemidef := by
    rw [← hPQ]
    exact projection_product_posSemidef P Q hP hP2 hQpos hPQ
  have hlocal (i : I) : D*(Matrix.trace (U i*(Q*P))).re ≤ t*cc*E := by
    let W := A i*U i*A i
    have hW : W.PosSemidef := by
      simpa only [(hA i).eq] using (hU i).mul_mul_conjTranspose_same (A i)
    have hc := (Complex.le_def.mp (trace_mono_right hcol hW)).1
    rw [Matrix.smul_mul,trace_smul_re,trace_mixture_re] at hc
    have hpair' (j : J) : (Matrix.trace (V j*W)).re ≤ E := by
      rw [Matrix.trace_mul_comm]
      exact hpair i j
    have hc' : (Matrix.trace (W*Q)).re ≤ cc*E := by
      rw [Matrix.trace_mul_comm]
      apply hc.trans
      apply mul_le_mul_of_nonneg_left _ hcc
      calc
        _ ≤ ∑ j, v j*E := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hpair' j) (hv j))
        _ = E := by rw [← Finset.sum_mul,hsv,one_mul]
    have hw := (Complex.le_def.mp (trace_mono_right (hwhite i) (hU i))).1
    rw [Matrix.smul_mul,Matrix.smul_mul,trace_smul_re,trace_smul_re,
      trace_four_swap,Matrix.trace_mul_comm (Q*P)] at hw
    exact hw.trans (by simpa only [W,mul_assoc] using mul_le_mul_of_nonneg_left hc' ht)
  have hr := (Complex.le_def.mp (trace_mono_right hrow hQP)).1
  rw [Matrix.smul_mul,trace_smul_re,trace_mixture_re] at hr
  calc
    _ ≤ D*(Matrix.trace (R*(Q*P))).re := mul_le_mul_of_nonneg_left
      (overlap_norm_sq_le_trace R Q P hR hR2 hQ hQ2 hP hP2 hPQ) hD
    _ ≤ D*(cr*∑ i, u i*(Matrix.trace (U i*(Q*P))).re) := mul_le_mul_of_nonneg_left hr hD
    _ = cr*(∑ i, u i*(D*(Matrix.trace (U i*(Q*P))).re)) := by
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ cr*(∑ i, u i*(t*cc*E)) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlocal i) (hu i))) hcr
    _ = cr*cc*t*E := by rw [← Finset.sum_mul,hsu,one_mul]; ring

end CoordinateSweeps.Overlap

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
