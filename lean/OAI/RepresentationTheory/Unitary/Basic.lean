import Mathlib
import OAI.Analysis.Matrix.TensorMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
structure UnitaryIrrep (Γ : Type*) [Group Γ] where
  dimension : ℕ
  positive : 0 < dimension
  matrix : Γ →* Matrix (Fin dimension) (Fin dimension) ℂ
  unitary : ∀ g, (matrix g).conjTranspose * matrix g = 1
  irreducible : ∀ S : Submodule ℂ (Fin dimension → ℂ),
    (∀ g v, v ∈ S → (matrix g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤
end CoordinateSweeps
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

def asRepresentation : Representation ℂ Γ (Fin ρ.dimension → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ.matrix

@[simp] lemma asRepresentation_apply (g : Γ) (v : Fin ρ.dimension → ℂ) :
    ρ.asRepresentation g v=(ρ.matrix g).mulVec v := rfl

instance asRepresentation_irreducible : ρ.asRepresentation.IsIrreducible := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  have hn : (⊥ : Subrepresentation ρ.asRepresentation) ≠ ⊤ := by
    intro hh
    have h := congrArg Subrepresentation.toSubmodule hh
    exact bot_ne_top h
  refine { exists_pair_ne := ⟨⊥,⊤,hn⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases ρ.irreducible S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with hh | hh
  · exact Or.inl (Subrepresentation.toSubmodule_injective hh)
  · exact Or.inr (Subrepresentation.toSubmodule_injective hh)

lemma character_asRepresentation (g : Γ) :
    ρ.asRepresentation.character g=Matrix.trace (ρ.matrix g) :=
  Matrix.trace_toLin'_eq _

/- Schur's scalar-commutant statement with all irreducibility obligations
proved directly from the exact source realization. -/
theorem commuting_scalar (A : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ)
    (hA : ∀ g, A*ρ.matrix g=ρ.matrix g*A) : ∃ c : ℂ, A=c • (1 : Matrix _ _ ℂ) := by
  let F : Representation.IntertwiningMap ρ.asRepresentation ρ.asRepresentation :=
    { toLinearMap := Matrix.toLinAlgEquiv' A
      isIntertwining' := by
        intro g
        change Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' (ρ.matrix g)=
          Matrix.toLinAlgEquiv' (ρ.matrix g) * Matrix.toLinAlgEquiv' A
        rw [← map_mul,← map_mul,hA g] }
  obtain ⟨c,hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ.asRepresentation) |>.2 F
  refine ⟨c,?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  change c • (1 : Module.End ℂ (Fin ρ.dimension → ℂ))=Matrix.toLinAlgEquiv' A at hh
  simpa using hh.symm

variable [Fintype Γ]

/- Character normalization in exactly the unnormalized trace convention. -/
theorem character_norm :
    (Fintype.card Γ : ℂ)⁻¹ *
      ∑ g : Γ, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)=1 := by
  let : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)
  have : Nonempty (Representation.Equiv ρ.asRepresentation ρ.asRepresentation) :=
    ⟨Representation.Equiv.refl _⟩
  have h := Representation.char_orthonormal ρ.asRepresentation ρ.asRepresentation
  rw [ite_eq_left (show Nonempty (Representation.Equiv ρ.asRepresentation ρ.asRepresentation)
    from inferInstance)] at h
  simpa [character_asRepresentation, Nat.card_eq_fintype_card] using h

omit [Fintype Γ] in
lemma matrix_inv (g : Γ) : ρ.matrix g⁻¹=(ρ.matrix g).conjTranspose := by
  calc
    ρ.matrix g⁻¹=1*ρ.matrix g⁻¹ := (one_mul _).symm
    _ = ((ρ.matrix g).conjTranspose*ρ.matrix g)*ρ.matrix g⁻¹ := by rw [ρ.unitary g]
    _ = (ρ.matrix g).conjTranspose := by rw [mul_assoc,← map_mul,mul_inv_cancel,map_one,mul_one]

/- Coefficients of the central isotypic projector, in unnormalized trace
convention. They are derived from an actual irrep, not supplied as character
data satisfying unproved orthogonality equations. -/
def coefficient (g : Γ) : ℂ :=
  (ρ.dimension : ℂ)/(Fintype.card Γ : ℂ) * Matrix.trace (ρ.matrix g⁻¹)

lemma coefficient_conj (k g : Γ) : ρ.coefficient (k*g*k⁻¹)=ρ.coefficient g := by
  unfold coefficient
  congr 1
  have h := Representation.char_conj ρ.asRepresentation g⁻¹ k
  simpa [character_asRepresentation,mul_inv_rev,mul_assoc] using h

lemma coefficient_star (g : Γ) : star (ρ.coefficient g)=ρ.coefficient g⁻¹ := by
  simp only [coefficient,star_mul,star_div₀,star_natCast,inv_inv]
  rw [← Matrix.trace_conjTranspose,← ρ.matrix_inv,inv_inv,mul_comm]

variable {A : Type*} [Semiring A] [Algebra ℂ A]

def projector (τ : Γ →* A) : A := ∑ g, ρ.coefficient g • τ g

lemma projector_commute (τ : Γ →* A) (k : Γ) :
    τ k * ρ.projector τ=ρ.projector τ * τ k := by
  have hcoef (g : Γ) : ρ.coefficient (k*(g*k⁻¹))=ρ.coefficient g := by
    simpa only [mul_assoc] using ρ.coefficient_conj k g
  have hh := Equiv.sum_comp (MulAut.conj k).toEquiv
    (fun g => ρ.coefficient g • (τ g * τ k))
  simpa [projector,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    MulAut.conj_apply,hcoef,coefficient_conj,← map_mul,mul_assoc] using hh

/- The isotypic projector acts as identity in its own irreducible. -/
theorem projector_self : ρ.projector ρ.matrix=1 := by
  obtain ⟨c,hc⟩ := ρ.commuting_scalar (ρ.projector ρ.matrix)
    (fun g => (ρ.projector_commute ρ.matrix g).symm)
  have ht : Matrix.trace (ρ.projector ρ.matrix)=(ρ.dimension : ℂ) := by
    simp only [projector,Matrix.trace_sum,Matrix.trace_smul,coefficient]
    calc
      _ = (ρ.dimension : ℂ)*((Fintype.card Γ : ℂ)⁻¹ *
        ∑ g, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        ring
      _ = _ := by rw [ρ.character_norm,mul_one]
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  have hD : (ρ.dimension : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ρ.positive.ne'
  have hcone : c=1 := (mul_right_cancel₀ hD (by simpa using ht))
  simpa [hcone] using hc

lemma coefficient_convolution (k : Γ) :
    ∑ g, ρ.coefficient g * ρ.coefficient (g⁻¹*k)=ρ.coefficient k := by
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        Matrix.trace (ρ.matrix k⁻¹ * ρ.projector ρ.matrix) := by
      simp only [projector,Finset.mul_sum,mul_smul_comm,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,coefficient,mul_inv_rev,inv_inv,map_mul]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ = _ := by rw [ρ.projector_self,mul_one]; rfl

/- Idempotence in every genuine representation, including absent types. -/
theorem projector_idempotent (τ : Γ →* A) : ρ.projector τ * ρ.projector τ=ρ.projector τ := by
  calc
    _ = ∑ g, ∑ h, (ρ.coefficient g * ρ.coefficient h) • τ (g*h) := by
      change (∑ g, ρ.coefficient g • τ g) * (∑ h, ρ.coefficient h • τ h)=_
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [smul_mul_smul_comm,← map_mul]
    _ = ∑ g, ∑ k, (ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k := by
      apply Finset.sum_congr rfl
      intro g hg
      simpa using Equiv.sum_comp (Equiv.mulLeft g)
        (fun k => (ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k)
    _ = ∑ k, ∑ g, (ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k := Finset.sum_comm
    _ = ∑ k, (∑ g, ρ.coefficient g * ρ.coefficient (g⁻¹*k)) • τ k := by
      simp only [Finset.sum_smul]
    _ = _ := by simp only [projector,coefficient_convolution]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem projector_hermitian (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    (ρ.projector τ).conjTranspose=ρ.projector τ := by
  simp only [projector,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    coefficient_star,hu]
  exact Equiv.sum_comp (Equiv.inv Γ) (fun g => ρ.coefficient g • τ g)

theorem projector_posSemidef (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    (ρ.projector τ).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (ρ.projector τ)
  rwa [ρ.projector_hermitian τ hu,ρ.projector_idempotent] at h

end UnitaryIrrep
end CoordinateSweeps

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixRepresentation (τ : Γ →* Matrix n n ℂ) : Representation ℂ Γ (n → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp τ

omit [Fintype Γ] in
lemma matrixRepresentation_character (τ : Γ →* Matrix n n ℂ) (g : Γ) :
    (matrixRepresentation τ).character g=Matrix.trace (τ g) :=
  Matrix.trace_toLin'_eq _

lemma character_sum_multiplicity (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) :
    ∑ g, Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹)=
      (Fintype.card Γ : ℂ) *
        Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
  let : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)
  have hc := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    ρ.asRepresentation (matrixRepresentation τ)
  simp only [character_asRepresentation,matrixRepresentation_character,
    Nat.card_eq_fintype_card] at hc
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (Fintype.card Γ : ℂ) * ((Fintype.card Γ : ℂ)⁻¹ *
        ∑ g, Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hN,one_mul]
    _ = _ := by rw [hc]

lemma sum_trace_norm_sq (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    ∑ g, ‖Matrix.trace (τ g)‖^2=(Fintype.card Γ : ℝ) *
      Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ)) := by
  let : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero)
  have hc := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (matrixRepresentation τ) (matrixRepresentation τ)
  simp only [matrixRepresentation_character,Nat.card_eq_fintype_card] at hc
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcs : ∑ g, Matrix.trace (τ g)*Matrix.trace (τ g⁻¹)=
      (Fintype.card Γ : ℂ)*
        Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ)) := by
    rw [← hc,← mul_assoc,mul_inv_cancel₀ hN,one_mul]
  have hstar (g : Γ) : Matrix.trace (τ g⁻¹)=star (Matrix.trace (τ g)) := by
    rw [← hu,Matrix.trace_conjTranspose]
  simp only [hstar,Complex.star_def,Complex.mul_conj'] at hcs
  exact_mod_cast hcs

lemma irrep_sum_trace_norm_sq (ρ : UnitaryIrrep Γ) :
    ∑ g, ‖Matrix.trace (ρ.matrix g)‖^2=(Fintype.card Γ : ℝ) := by
  have hc := ρ.character_norm
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcs : ∑ g, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)=
      (Fintype.card Γ : ℂ) := by
    calc
      _ = (Fintype.card Γ : ℂ)*((Fintype.card Γ : ℂ)⁻¹ *
        ∑ g, Matrix.trace (ρ.matrix g)*Matrix.trace (ρ.matrix g⁻¹)) := by
          rw [← mul_assoc,mul_inv_cancel₀ hN,one_mul]
      _ = _ := by rw [hc,mul_one]
  simp only [ρ.matrix_inv,Matrix.trace_conjTranspose,Complex.star_def,Complex.mul_conj'] at hcs
  exact_mod_cast hcs

/- No decomposition/classification hypothesis is needed for this character
Cauchy--Schwarz bound. It applies also to absent types (multiplicity zero). -/
theorem multiplicity_sq_le_commutant (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)))^2 ≤
      Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ)) := by
  let m := Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ))
  let e := Module.finrank ℂ ((matrixRepresentation τ).IntertwiningMap (matrixRepresentation τ))
  have hs : (Fintype.card Γ : ℝ)*(m : ℝ) ≤
      ∑ g, ‖Matrix.trace (τ g)‖*‖Matrix.trace (ρ.matrix g)‖ := by
    have hh := norm_sum_le (Finset.univ : Finset Γ)
      (fun g => Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹))
    rw [ρ.character_sum_multiplicity τ] at hh
    simpa only [norm_mul,Complex.norm_natCast,ρ.matrix_inv,Matrix.trace_conjTranspose,
      norm_star,m] using hh
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Γ)
    (fun g => ‖Matrix.trace (τ g)‖) (fun g => ‖Matrix.trace (ρ.matrix g)‖)
  rw [sum_trace_norm_sq τ hu,ρ.irrep_sum_trace_norm_sq] at hcs
  have hN : (0 : ℝ)<Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs' : ((Fintype.card Γ : ℝ)*(m : ℝ))^2 ≤
      (∑ g, ‖Matrix.trace (τ g)‖*‖Matrix.trace (ρ.matrix g)‖)^2 :=
    pow_le_pow_left₀ (mul_nonneg hN.le hm) hs 2
  have heq : ((m : ℝ)^2)*(Fintype.card Γ : ℝ)^2 ≤
      (e : ℝ)*(Fintype.card Γ : ℝ)^2 := by
    dsimp [e] at ⊢
    nlinarith [hs'.trans hcs]
  have hh := (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp heq
  exact_mod_cast hh

end UnitaryIrrep
end CoordinateSweeps
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
namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

lemma central_sum_commute {A : Type*} [Semiring A] [Algebra ℂ A]
    (τ : Γ →* A) (f : Γ → ℂ) (hf : ∀ k g, f (k*g*k⁻¹)=f g) (k : Γ) :
    τ k*(∑ g, f g • τ g)=(∑ g, f g • τ g)*τ k := by
  have hcoef (g : Γ) : f (k*(g*k⁻¹))=f g := by simpa only [mul_assoc] using hf k g
  have hh := Equiv.sum_comp (MulAut.conj k).toEquiv (fun g => f g • (τ g*τ k))
  simpa [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    MulAut.conj_apply,hcoef,hf,← map_mul,mul_assoc] using hh

omit [Fintype Γ] in
lemma trace_conj (τ : Γ →* Matrix n n ℂ) (k g : Γ) :
    Matrix.trace (τ (k*g*k⁻¹))=Matrix.trace (τ g) := by
  rw [map_mul,map_mul,Matrix.trace_mul_cycle,← map_mul,inv_mul_cancel,map_one,one_mul]

lemma central_character_operator (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) :
    ∑ g, Matrix.trace (τ g⁻¹) • ρ.matrix g =
      ((Fintype.card Γ : ℂ) * Module.finrank ℂ
        (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) / ρ.dimension) •
          (1 : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) := by
  let S := ∑ g, Matrix.trace (τ g⁻¹) • ρ.matrix g
  have hcomm (k : Γ) : ρ.matrix k*S=S*ρ.matrix k :=
    central_sum_commute ρ.matrix _ (fun k g => by
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using trace_conj τ k g⁻¹) k
  obtain ⟨c,hc⟩ := ρ.commuting_scalar S (fun k => (hcomm k).symm)
  have hs : Matrix.trace S=(Fintype.card Γ : ℂ) * Module.finrank ℂ
        (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) := by
    dsimp [S]
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul,smul_eq_mul]
    have hh := Equiv.sum_comp (Equiv.inv Γ)
      (fun g => Matrix.trace (τ g)*Matrix.trace (ρ.matrix g⁻¹))
    simp only [Equiv.inv_apply,inv_inv] at hh
    rw [hh,ρ.character_sum_multiplicity τ]
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at hs
  have hD : (ρ.dimension : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ρ.positive.ne'
  have hce : c=(Fintype.card Γ : ℂ) * Module.finrank ℂ
        (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) / ρ.dimension :=
    (eq_div_iff hD).mpr hs
  exact hc.trans (congrArg (fun c : ℂ => c • (1 : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ)) hce)

/- Exact projected character, with the genuine Hom-space multiplicity. -/
theorem projector_twisted_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ) (k : Γ) :
    Matrix.trace (ρ.projector τ*τ k) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace (ρ.matrix k) := by
  let M : ℂ := Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ))
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hD : (ρ.dimension : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ρ.positive.ne'
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        ∑ g, Matrix.trace (ρ.matrix g⁻¹)*Matrix.trace (τ (g*k)) := by
      simp only [projector,Finset.sum_mul,smul_mul_assoc,Matrix.trace_sum,Matrix.trace_smul,
        smul_eq_mul,coefficient,Finset.mul_sum,map_mul]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        ∑ g, Matrix.trace (τ g⁻¹)*Matrix.trace (ρ.matrix (k*g)) := by
      congr 1
      have hh := Equiv.sum_comp ((Equiv.mulRight k).trans (Equiv.inv Γ))
        (fun g => Matrix.trace (τ g⁻¹)*Matrix.trace (ρ.matrix (k*g)))
      convert hh using 1
      apply Finset.sum_congr rfl
      intro g hg
      change Matrix.trace (ρ.matrix g⁻¹)*Matrix.trace (τ (g*k)) =
        Matrix.trace (τ ((g*k)⁻¹)⁻¹)*Matrix.trace (ρ.matrix (k*(g*k)⁻¹))
      simp only [inv_inv,mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul]
      ring
    _ = ((ρ.dimension : ℂ)/(Fintype.card Γ : ℂ)) *
        Matrix.trace (ρ.matrix k*(∑ g, Matrix.trace (τ g⁻¹) • ρ.matrix g)) := by
      simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,map_mul]
    _ = M*Matrix.trace (ρ.matrix k) := by
      rw [ρ.central_character_operator τ,Matrix.mul_smul,mul_one,Matrix.trace_smul,smul_eq_mul]
      change _*( ((Fintype.card Γ : ℂ)*M/(ρ.dimension : ℂ))*_)=_
      field_simp

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

/- The projected trace formula applies to actual elements of the group algebra,
not just to individual group elements. -/
theorem projector_lift_trace (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (x : MonoidAlgebra ℂ Γ) :
    Matrix.trace (ρ.projector τ*((MonoidAlgebra.lift ℂ _ Γ) τ x)) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace ((MonoidAlgebra.lift ℂ _ Γ) ρ.matrix x) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa using ρ.projector_twisted_trace τ g
  | add x y hx hy => simp only [map_add,mul_add,Matrix.trace_add,hx,hy]
  | smul c x hx => simp only [map_smul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,hx]; ring

/- Literal finite averages and their adjoints have the same group-algebra
word in every unitary representation. -/
def averageMatrix {Ω : Type*} [Fintype Ω] (τ : Γ →* Matrix n n ℂ)
    (w : Ω → ℂ) (g : Ω → Γ) : Matrix n n ℂ := ∑ ω, w ω • τ (g ω)

def averageAlgebra {Ω : Type*} [Fintype Ω] (w : Ω → ℂ) (g : Ω → Γ) :
    MonoidAlgebra ℂ Γ := ∑ ω, MonoidAlgebra.single (g ω) (w ω)

omit [Fintype Γ] in
lemma lift_averageAlgebra {Ω : Type*} [Fintype Ω] (τ : Γ →* Matrix n n ℂ)
    (w : Ω → ℂ) (g : Ω → Γ) :
    (MonoidAlgebra.lift ℂ _ Γ) τ (averageAlgebra w g)=averageMatrix τ w g := by
  simp only [averageAlgebra,map_sum,MonoidAlgebra.lift_single,averageMatrix]

omit [Fintype Γ] in
lemma averageMatrix_star {Ω : Type*} [Fintype Ω] (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) :
    (averageMatrix τ w g).conjTranspose = averageMatrix τ (fun ω => star (w ω))
      (fun ω => (g ω)⁻¹) := by
  simp only [averageMatrix,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,hu]

/- Exact unnormalized even moment trace on a genuine isotypic component. -/
theorem projected_average_moment {Ω : Type*} [Fintype Ω]
    (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) (q : ℕ) :
    Matrix.trace (ρ.projector τ*((averageMatrix τ w g).conjTranspose*averageMatrix τ w g)^q) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace (((averageMatrix ρ.matrix w g).conjTranspose*averageMatrix ρ.matrix w g)^q) := by
  have hr (k : Γ) : (ρ.matrix k).conjTranspose=ρ.matrix k⁻¹ := (ρ.matrix_inv k).symm
  have hh := ρ.projector_lift_trace τ
    ((averageAlgebra (fun ω => star (w ω)) (fun ω => (g ω)⁻¹)*averageAlgebra w g)^q)
  simpa only [map_pow,map_mul,lift_averageAlgebra,← averageMatrix_star τ hu,
    ← averageMatrix_star ρ.matrix hr] using hh

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ n : Type*} [Group Γ] [Fintype Γ] [Fintype n] [DecidableEq n]

lemma projector_commute_average {Ω : Type*} [Fintype Ω] (ρ : UnitaryIrrep Γ)
    (τ : Γ →* Matrix n n ℂ) (w : Ω → ℂ) (g : Ω → Γ) :
    ρ.projector τ*averageMatrix τ w g=averageMatrix τ w g*ρ.projector τ := by
  simp only [averageMatrix,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    ρ.projector_commute τ]

open scoped MatrixOrder in
lemma trace_positive_product {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A*B) := by
  obtain ⟨C,rfl⟩:=CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

lemma projector_complement_posSemidef (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) : (1-ρ.projector τ).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1-ρ.projector τ)
  convert h using 1
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,ρ.projector_hermitian τ hu]
  simp only [sub_mul,mul_sub,one_mul,mul_one,ρ.projector_idempotent]
  module

/- Genuine occurrence gives a lower bound for the encompassing unnormalized
moment, with its actual Hom multiplicity and no missing dimension factor. -/
theorem multiplicity_moment_le {Ω : Type*} [Fintype Ω]
    (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) (q : ℕ) :
    (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℝ) *
      (Matrix.trace (((averageMatrix ρ.matrix w g).conjTranspose*averageMatrix ρ.matrix w g)^q)).re ≤
        (Matrix.trace (((averageMatrix τ w g).conjTranspose*averageMatrix τ w g)^q)).re := by
  have hB := (Matrix.posSemidef_conjTranspose_mul_self (averageMatrix τ w g)).pow q
  have hh := trace_positive_product (ρ.projector_complement_posSemidef τ hu) hB
  rw [sub_mul,one_mul,Matrix.trace_sub,ρ.projected_average_moment τ hu w g q] at hh
  simpa only [Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
    sub_nonneg] using (Complex.nonneg_iff.mp hh).1

/- The Schatten moment of the projected average, rather than merely an
inserted projector in the trace, is exactly the same multiplicity formula. -/
theorem projected_operator_moment {Ω : Type*} [Fintype Ω]
    (ρ : UnitaryIrrep Γ) (τ : Γ →* Matrix n n ℂ)
    (hu : ∀ g, (τ g).conjTranspose=τ g⁻¹) (w : Ω → ℂ) (g : Ω → Γ) {q : ℕ} (hq : q ≠ 0) :
    Matrix.trace (((ρ.projector τ*averageMatrix τ w g).conjTranspose*
      (ρ.projector τ*averageMatrix τ w g))^q) =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation τ)) : ℂ) *
        Matrix.trace (((averageMatrix ρ.matrix w g).conjTranspose*averageMatrix ρ.matrix w g)^q) := by
  let P := ρ.projector τ
  let K := averageMatrix τ w g
  have hP2 : P*P=P := ρ.projector_idempotent τ
  have hPK : P*K=K*P := ρ.projector_commute_average τ w g
  have hPs : P.conjTranspose=P := ρ.projector_hermitian τ hu
  have hPa : P*K.conjTranspose=K.conjTranspose*P := by
    have hh := congrArg Matrix.conjTranspose hPK
    simpa only [Matrix.conjTranspose_mul,hPs] using hh.symm
  have he : (P*K).conjTranspose*(P*K)=P*(K.conjTranspose*K) := by
    rw [Matrix.conjTranspose_mul,hPs]
    calc
      _ = K.conjTranspose*(P*P)*K := by noncomm_ring
      _ = P*(K.conjTranspose*K) := by rw [hP2,← hPa,mul_assoc]
  have hc : Commute P (K.conjTranspose*K) := by
    show P*(K.conjTranspose*K)=(K.conjTranspose*K)*P
    rw [← mul_assoc,hPa,mul_assoc,hPK,← mul_assoc]
  change Matrix.trace (((P*K).conjTranspose*(P*K))^q)=_
  rw [he,hc.mul_pow,(show IsIdempotentElem P from hP2).pow_eq hq]
  exact ρ.projected_average_moment τ hu w g q

end CoordinateSweeps.UnitaryIrrep
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.UnitaryIrrep
variable {Γ Λ : Type*} [Group Γ] [Group Λ]

def pullback (ρ : UnitaryIrrep Λ) (e : Γ ≃* Λ) : UnitaryIrrep Γ where
  dimension := ρ.dimension
  positive := ρ.positive
  matrix := ρ.matrix.comp e.toMonoidHom
  unitary g := ρ.unitary (e g)
  irreducible S hS := ρ.irreducible S (by
    intro g v hv
    have hh := hS (e.symm g) v hv
    change (ρ.matrix (e (e.symm g))).mulVec v ∈ S at hh
    rwa [MulEquiv.apply_symm_apply] at hh)

end CoordinateSweeps.UnitaryIrrep
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.UnitaryRealization
variable {G J : Type*} [Group G] [Fintype G] [Fintype J] [DecidableEq J]

/- Gram averaging produces the invariant positive form directly from the
finite action; no invariant inner product is postulated. -/
lemma gram_posDef (τ : G →* Matrix J J ℂ) :
    (∑ g, (τ g).conjTranspose * τ g).PosDef := by
  apply Matrix.posDef_sum Finset.univ_nonempty
  intro g hg
  apply Matrix.PosDef.conjTranspose_mul_self
  intro x y h
  have hh := congrArg (fun v => (τ g⁻¹).mulVec v) h
  simpa only [Matrix.mulVec_mulVec,← map_mul,inv_mul_cancel,map_one,Matrix.one_mulVec] using hh

lemma gram_invariant (τ : G →* Matrix J J ℂ) (h : G) :
    (τ h).conjTranspose*(∑ g, (τ g).conjTranspose*τ g)*τ h=
      ∑ g, (τ g).conjTranspose*τ g := by
  have hh := Equiv.sum_comp (Equiv.mulRight h) (fun g => (τ g).conjTranspose*τ g)
  calc
    _ = ∑ g, (τ (g*h)).conjTranspose * τ (g*h) := by
      simp only [Matrix.mul_sum,Matrix.sum_mul,map_mul,Matrix.conjTranspose_mul]
      apply Finset.sum_congr rfl
      intro g hg
      simp only [mul_assoc]
    _ = _ := hh

/- Actual conjugating matrices and a unitary action for any finite complex
matrix representation. -/
theorem unitarize (τ : G →* Matrix J J ℂ) :
    ∃ A B : Matrix J J ℂ, A*B=1 ∧ B*A=1 ∧ A.IsHermitian ∧ B.IsHermitian ∧
      (∀ g, (B*τ g*A).conjTranspose*(B*τ g*A)=1) := by
  let M : Matrix J J ℂ := ∑ g, (τ g).conjTranspose*τ g
  obtain ⟨A,hA,hAMA,hcomm⟩ := TensorBoard.exists_whitening M (gram_posDef τ)
  have hAM : A*M=M*A := (hcomm M (Commute.refl M)).eq
  let B := M*A
  have hAB : A*B=1 := by simpa only [B,mul_assoc] using hAMA
  have hBA : B*A=1 := by change M*A*A=1; rw [← hAM]; exact hAMA
  have hB : B.IsHermitian := by
    change (M*A).conjTranspose=M*A
    rw [Matrix.conjTranspose_mul,hA.isHermitian.eq,(gram_posDef τ).isHermitian.eq,hAM]
  have hB2 : B*B=M := by
    calc
      _ = M*(A*B) := by simp only [B,mul_assoc]
      _ = M := by rw [hAB,mul_one]
  refine ⟨A,B,hAB,hBA,hA.isHermitian,hB,?_⟩
  intro g
  calc
    _ = A*((τ g).conjTranspose*(B*B)*τ g)*A := by
      rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hA.isHermitian.eq,hB.eq]
      simp only [mul_assoc]
    _ = A*M*A := by rw [hB2,gram_invariant τ g]
    _ = 1 := hAMA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/- A genuine irreducible representation has a unitary finite matrix
realization, with the intertwining equivalence retained. -/
theorem exists_unitary (σ : Representation ℂ G V) [σ.IsIrreducible] :
    ∃ ρ : UnitaryIrrep G, Nonempty (Representation.Equiv σ ρ.asRepresentation) := by
  let d := Module.finrank ℂ V
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := (Module.finBasis ℂ V).equivFun
  let τ : G →* Matrix (Fin d) (Fin d) ℂ :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp ((e.conjAlgEquiv ℂ).toMonoidHom.comp σ)
  obtain ⟨A,B,hAB,hBA,hA,hB,hu⟩ := unitarize τ
  let f : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofLinearMap
    (Matrix.toLinAlgEquiv' B) (Matrix.toLinAlgEquiv' A)
    (by change Matrix.toLinAlgEquiv' B * Matrix.toLinAlgEquiv' A=1
        rw [← map_mul,hBA,map_one])
    (by change Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' B=1
        rw [← map_mul,hAB,map_one])
  let E := e.trans f
  let ν : G →* Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun g => B*τ g*A
      map_one' := by rw [map_one,mul_one,hBA]
      map_mul' := by intro g h; rw [map_mul]; simp only [mul_assoc];
                     rw [← mul_assoc A B,hAB,one_mul] }
  have he (g : G) (v : V) : (τ g).mulVec (e v)=e (σ g v) := by
    change (LinearMap.toMatrix' (e.conj (σ g))).mulVec (e v)=_
    rw [LinearMap.toMatrix'_mulVec]
    simp
  have hE (g : G) (v : V) : (ν g).mulVec (E v)=E (σ g v) := by
    change (B*τ g*A).mulVec (B.mulVec (e v))=B.mulVec (e (σ g v))
    rw [Matrix.mulVec_mulVec]
    have hh : B*τ g*A*B=B*τ g := by simp only [mul_assoc,hAB,mul_one]
    rw [hh,← Matrix.mulVec_mulVec,he]
  have hd : 0 < d := by
    have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
    have : Nontrivial V := inferInstanceAs (Nontrivial σ.asModule)
    exact Module.finrank_pos
  let ρ : UnitaryIrrep G :=
    { dimension := d
      positive := hd
      matrix := ν
      unitary := hu
      irreducible := by
        intro S hS
        let T : Subrepresentation σ :=
          { toSubmodule := S.comap E.toLinearMap
            apply_mem_toSubmodule := by
              intro g v hv
              change E (σ g v) ∈ S
              rw [← hE]
              exact hS g (E v) hv }
        rcases eq_bot_or_eq_top T with ht | ht
        · left
          apply le_antisymm _ bot_le
          intro w hw
          have hv : E.symm w ∈ T := by change E (E.symm w)∈S; simpa using hw
          rw [ht] at hv
          have hh : E.symm w=0 := hv
          simpa using congrArg E hh
        · right
          apply le_antisymm le_top
          intro w hw
          have hv : E.symm w ∈ T := by rw [ht]; trivial
          change E (E.symm w) ∈ S at hv
          simpa using hv }
  refine ⟨ρ,⟨Representation.Equiv.mk E ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  exact (hE g v).symm

end CoordinateSweeps.UnitaryRealization

namespace CoordinateSweeps.UnitaryIrrep
variable {G : Type*} [Group G] [Fintype G]

lemma projector_other (ρ σ : UnitaryIrrep G)
    (hne : ¬Nonempty (Representation.Equiv ρ.asRepresentation σ.asRepresentation)) :
    ρ.projector σ.matrix=0 := by
  obtain ⟨c,hc⟩ := σ.commuting_scalar (ρ.projector σ.matrix)
    (fun g => (ρ.projector_commute σ.matrix g).symm)
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  have horth := Representation.char_orthonormal σ.asRepresentation ρ.asRepresentation
  rw [ite_eq_right hne] at horth
  have ht : Matrix.trace (ρ.projector σ.matrix)=0 := by
    simp only [projector,Matrix.trace_sum,Matrix.trace_smul,coefficient]
    calc
      _ = (ρ.dimension : ℂ)*((Fintype.card G : ℂ)⁻¹ *
        ∑ g, Matrix.trace (ρ.matrix g⁻¹)*Matrix.trace (σ.matrix g)) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro g hg; simp only [smul_eq_mul]; ring
      _ = 0 := by
        have hh := horth
        simpa [character_asRepresentation,Nat.card_eq_fintype_card,
          ← Finset.mul_sum,mul_comm] using congrArg (fun z : ℂ => (ρ.dimension : ℂ)*z) hh
  rw [hc,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  have hc0 : c=0 := (mul_eq_zero.mp ht).resolve_right
    (Nat.cast_ne_zero.mpr σ.positive.ne')
  simpa [hc0] using hc

lemma cross_convolution (ρ σ : UnitaryIrrep G)
    (hne : ¬Nonempty (Representation.Equiv σ.asRepresentation ρ.asRepresentation)) (k : G) :
    ∑ g, ρ.coefficient g*σ.coefficient (g⁻¹*k)=0 := by
  calc
    _ = ((σ.dimension : ℂ)/(Fintype.card G : ℂ)) *
        Matrix.trace (σ.matrix k⁻¹ * ρ.projector σ.matrix) := by
      simp only [projector,Finset.mul_sum,mul_smul_comm,Matrix.trace_sum,
        Matrix.trace_smul,smul_eq_mul,coefficient,mul_inv_rev,inv_inv,map_mul]
      apply Finset.sum_congr rfl; intro g hg; ring
    _ = 0 := by
      rw [projector_other ρ σ (fun ⟨e⟩ => hne ⟨e.symm⟩),mul_zero,Matrix.trace_zero,mul_zero]

lemma projector_orthogonal {A : Type*} [Semiring A] [Algebra ℂ A]
    (ρ σ : UnitaryIrrep G)
    (hne : ¬Nonempty (Representation.Equiv σ.asRepresentation ρ.asRepresentation))
    (τ : G →* A) : ρ.projector τ*σ.projector τ=0 := by
  calc
    _ = ∑ g, ∑ h, (ρ.coefficient g*σ.coefficient h) • τ (g*h) := by
      simp only [projector,Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,map_mul]
      exact Finset.sum_comm
    _ = ∑ g, ∑ k, (ρ.coefficient g*σ.coefficient (g⁻¹*k)) • τ k := by
      apply Finset.sum_congr rfl; intro g hg
      simpa using Equiv.sum_comp (Equiv.mulLeft g)
        (fun k => (ρ.coefficient g*σ.coefficient (g⁻¹*k)) • τ k)
    _ = ∑ k, (∑ g, ρ.coefficient g*σ.coefficient (g⁻¹*k)) • τ k := by
      rw [Finset.sum_comm]; simp only [Finset.sum_smul]
    _ = 0 := by simp only [cross_convolution ρ σ hne,zero_smul,Finset.sum_const_zero]

lemma projector_intertwiner {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : UnitaryIrrep G)
    (τ : Representation ℂ G V) (ν : Representation ℂ G W)
    (F : Representation.IntertwiningMap τ ν) (v : V) :
    (ρ.projector ν) (F v)=F ((ρ.projector τ) v) := by
  simp only [projector,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,Representation.IntertwiningMap.isIntertwining]

lemma projector_matrix_asRepresentation (ρ σ : UnitaryIrrep G) :
    ρ.projector σ.asRepresentation=Matrix.toLinAlgEquiv' (ρ.projector σ.matrix) := by
  simp only [projector,map_sum,map_smul]
  rfl

end CoordinateSweeps.UnitaryIrrep
end
end
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
