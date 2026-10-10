import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin
namespace ScalarCycles
variable {K I J : Type*} [Field K] [Fintype I]

def supportedKernel (D : Matrix I I K) (P : I → Prop) : Submodule K (I → K) where
  carrier := {x | (∀ i, ¬ P i → x i = 0) ∧ Matrix.vecMul x D = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hxd⟩ ⟨hy,hyd⟩
    constructor
    · intro i hi; simp [hx i hi,hy i hi]
    · rw [Matrix.add_vecMul,hxd,hyd,add_zero]
  smul_mem' := by
    rintro r x ⟨hx,hxd⟩
    constructor
    · intro i hi; simp [hx i hi]
    · rw [Matrix.smul_vecMul,hxd,smul_zero]

lemma supported_vecMul (P : I → Prop) (R : J → Prop)
    (S : Matrix I J K) (hS : ∀ i j, S i j ≠ 0 → (P i ↔ R j))
    (x : I → K) (hx : ∀ i, ¬ P i → x i = 0) :
    ∀ j, ¬ R j → Matrix.vecMul x S j = 0 := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hs : S i j=0
  · simp [hs]
  · rw [hx i (fun hp => hj ((hS i j hs).mp hp)),zero_mul]

variable [Fintype J]

noncomputable def conjugateMap (L : Matrix I I K) (R : Matrix J J K)
    (P : I → Prop) (T : J → Prop) (S : Matrix I J K)
    (hS : ∀ i j, S i j ≠ 0 → (P i ↔ T j)) (hc : L*S=S*R) :
    supportedKernel L P →ₗ[K] supportedKernel R T where
  toFun x := ⟨Matrix.vecMul x.val S, supported_vecMul P T S hS x.val x.property.1, by
    rw [Matrix.vecMul_vecMul,← hc,← Matrix.vecMul_vecMul,x.property.2,Matrix.zero_vecMul]⟩
  map_add' x y := by apply Subtype.ext; exact Matrix.add_vecMul _ _ _
  map_smul' r x := by apply Subtype.ext; exact Matrix.smul_vecMul _ _ _

noncomputable def conjugateEquiv [DecidableEq I] [DecidableEq J]
    (L : Matrix I I K) (R : Matrix J J K)
    (P : I → Prop) (T : J → Prop) (S : Matrix I J K) (D : Matrix J I K)
    (hS : ∀ i j, S i j ≠ 0 → (P i ↔ T j))
    (hD : ∀ j i, D j i ≠ 0 → (T j ↔ P i))
    (hSD : S*D=1) (hDS : D*S=1) (hc : L*S=S*R) :
    supportedKernel L P ≃ₗ[K] supportedKernel R T := by
  have hd : R*D=D*L := by
    calc
      R*D = (D*S)*(R*D) := by rw [hDS,Matrix.one_mul]
      _ = D*(S*R)*D := by simp only [Matrix.mul_assoc]
      _ = D*(L*S)*D := by rw [hc]
      _ = D*L*(S*D) := by simp only [Matrix.mul_assoc]
      _ = D*L := by rw [hSD,Matrix.mul_one]
  refine {
    toLinearMap := conjugateMap L R P T S hS hc
    invFun := conjugateMap R L T P D hD hd
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Subtype.ext
    change Matrix.vecMul (Matrix.vecMul x.val S) D=x.val
    rw [Matrix.vecMul_vecMul,hSD,Matrix.vecMul_one]
  · intro x
    apply Subtype.ext
    change Matrix.vecMul (Matrix.vecMul x.val D) S=x.val
    rw [Matrix.vecMul_vecMul,hDS,Matrix.vecMul_one]

noncomputable def reindexEquiv (L : Matrix I I K) (P : I → Prop) (e : J ≃ I) :
    supportedKernel L P ≃ₗ[K] supportedKernel (L.submatrix e e) (P ∘ e) where
  toFun x := ⟨x.val ∘ e, by
    constructor
    · intro j hj; exact x.property.1 (e j) hj
    · rw [Matrix.submatrix_vecMul_equiv]
      simp only [Function.comp_assoc,e.self_comp_symm,Function.comp_id,x.property.2,Pi.zero_comp]⟩
  invFun y := ⟨y.val ∘ e.symm, by
    constructor
    · intro i hi
      exact y.property.1 (e.symm i) (by simpa only [Function.comp_apply,e.apply_symm_apply] using hi)
    · have hh := y.property.2
      rw [Matrix.submatrix_vecMul_equiv] at hh
      funext i
      simpa only [Function.comp_apply,e.apply_symm_apply,Pi.zero_apply] using congrFun hh (e.symm i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv y := by apply Subtype.ext; funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Block
variable {A : Type*} [Fintype A] [DecidableEq A] {B : A → Type*} [∀ a, Fintype (B a)]

lemma vecMul_blockDiagonal' (D : (a:A) → Matrix (B a) (B a) K)
    (x : (Sigma B) → K) (a:A) (i:B a) :
    Matrix.vecMul x (Matrix.blockDiagonal' D) ⟨a,i⟩ =
      Matrix.vecMul (fun j => x ⟨a,j⟩) (D a) i := by
  change (∑ z, x z * Matrix.blockDiagonal' D z ⟨a,i⟩) = _
  rw [Fintype.sum_sigma,Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]; rfl
  · intro b hb hba
    apply Finset.sum_eq_zero
    intro j hj
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hba,mul_zero]
  · simp

noncomputable def blockEquiv (D : (a:A) → Matrix (B a) (B a) K)
    (P : (a:A) → B a → Prop) :
    supportedKernel (Matrix.blockDiagonal' D) (fun x => P x.1 x.2) ≃ₗ[K]
      ((a:A) → supportedKernel (D a) (P a)) where
  toFun x a := ⟨fun i => x.val ⟨a,i⟩, by
    constructor
    · intro i hi; exact x.property.1 ⟨a,i⟩ hi
    · funext i
      rw [← vecMul_blockDiagonal']
      exact congrFun x.property.2 ⟨a,i⟩⟩
  invFun x := ⟨fun i => (x i.1).val i.2, by
    constructor
    · rintro ⟨a,i⟩ hi; exact (x a).property.1 i hi
    · funext i
      rw [vecMul_blockDiagonal']
      exact congrFun (x i.1).property.2 i.2⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Block

end ScalarCycles
end HarmonicArtin

end OAI
