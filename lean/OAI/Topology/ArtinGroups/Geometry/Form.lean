import Mathlib
import OAI.Topology.ArtinGroups.Geometry.Cartan

namespace OAI

namespace HarmonicArtin.Geometric.FiniteOrbit
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S G:Type*} [Fintype S] [Group G] [Fintype G]
  (ρ:G →* (S → ℝ) ≃ₗ[ℝ] (S → ℝ))

noncomputable def form (x y:S → ℝ) : ℝ :=
  ∑ w:G,ρ w x ⬝ᵥ ρ w y

lemma form_symm (x y:S → ℝ) : form ρ x y=form ρ y x := by
  unfold form
  apply Finset.sum_congr rfl
  intro w _
  exact dotProduct_comm _ _

lemma form_sub_right (x y z:S → ℝ) :
    form ρ x (y-z)=form ρ x y-form ρ x z := by
  simp only [form,map_sub,dotProduct_sub,Finset.sum_sub_distrib]

lemma form_smul_right (x y:S → ℝ) (r:ℝ) :
    form ρ x (r • y)=r*form ρ x y := by
  simp only [form,map_smul,dotProduct_smul,smul_eq_mul,Finset.mul_sum]

lemma form_neg_left (x y:S → ℝ) :
    form ρ (-x) y= -form ρ x y := by
  rw [form_symm,form,form]
  simp only [map_neg,dotProduct_neg,Finset.sum_neg_distrib]
  rw [show (∑ w,ρ w y ⬝ᵥ ρ w x)=
    ∑ w,ρ w x ⬝ᵥ ρ w y from by
      apply Finset.sum_congr rfl; intro w _; exact dotProduct_comm _ _]

lemma form_invariant (g:G) (x y:S → ℝ) :
    form ρ (ρ g x) (ρ g y)=form ρ x y := by
  unfold form
  have he (w:G) : ρ w (ρ g x) ⬝ᵥ
      ρ w (ρ g y)=
      ρ (w*g) x ⬝ᵥ ρ (w*g) y := by
    simp only [map_mul,LinearEquiv.mul_apply]
  simp_rw [he]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun w=>rfl)

lemma form_pos (x:S → ℝ) (hx:x≠0) : 0 < form ρ x x := by
  apply Finset.sum_pos'
  · intro w _
    exact Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  · refine ⟨1,Finset.mem_univ _,?_⟩
    simp only [map_one]
    change 0 < x ⬝ᵥ x
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _=>mul_self_nonneg _))
      (Ne.symm (fun h=>hx (dotProduct_self_eq_zero.mp h)))

lemma form_sum_left {I:Type*} [Fintype I] (x:I → S → ℝ) (y:S → ℝ) :
    form ρ (∑ i,x i) y=∑ i,form ρ (x i) y := by
  simp only [form,map_sum,sum_dotProduct]
  rw [Finset.sum_comm]

lemma form_smul_left (x y:S → ℝ) (r:ℝ) : form ρ (r • x) y=r*form ρ x y := by
  rw [form_symm,form_smul_right,form_symm ρ y x]

variable [DecidableEq S]

lemma form_basis_row {M:CoxeterMatrix S} (i:S) (g:G)
    (hg:ρ g=simpleReflection M i) (x:S → ℝ) :
    form ρ (Pi.single i 1) x=
      (form ρ (Pi.single i 1) (Pi.single i 1)/2)*(cartan M *ᵥ x) i := by
  have h:=form_invariant ρ g (Pi.single i 1) x
  have he : simpleReflection M i (Pi.single i 1)= -(Pi.single i 1) := by
    simp only [simpleReflection_apply]
    have hh : (cartan M *ᵥ Pi.single i 1) i=2 := by simp [Matrix.mulVec_single]
    rw [hh]
    module
  rw [hg,he,simpleReflection_apply,
    form_neg_left,form_sub_right,form_smul_right] at h
  linarith

noncomputable def scale (i:S) : ℝ := form ρ (Pi.single i 1) (Pi.single i 1)/2

lemma scale_pos (i:S) : 0 < scale ρ i := by
  apply div_pos _ (by norm_num)
  apply form_pos
  intro h
  have hi:=congrFun h i
  simp at hi

variable {T:Type*}
  {M:CoxeterMatrix S} (ι:T → S) (g:T → G) (hg:∀ i,ρ (g i)=simpleReflection M (ι i))

include hg

lemma scale_balance (i j:T) :
    scale ρ (ι i)*cartan M (ι i) (ι j)=scale ρ (ι j)*cartan M (ι i) (ι j) := by
  have h:=form_symm ρ (Pi.single (ι i) 1) (Pi.single (ι j) 1)
  rw [form_basis_row ρ (ι i) (g i) (hg i) (Pi.single (ι j) 1),
    form_basis_row ρ (ι j) (g j) (hg j) (Pi.single (ι i) 1)] at h
  simpa [Matrix.mulVec_single,← cartan_symm M (ι i) (ι j),scale] using h

variable [Fintype T]

lemma form_matrix (x y:T → ℝ) :
    form ρ (∑ i,x i • Pi.single (ι i) 1) (∑ j,y j • Pi.single (ι j) 1)=
      ∑ i,∑ j,scale ρ (ι i)*cartan M (ι i) (ι j)*x i*y j := by
  rw [form_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_smul_left,form_basis_row ρ (ι i) (g i) (hg i)]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,Finset.sum_apply,Pi.smul_apply,
    Matrix.mulVec_single,smul_eq_mul,Finset.mul_sum,scale,
    MulOpposite.op_one,one_smul,Matrix.col,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem principal_posDef (hι:Function.Injective ι) :
    ((cartan M).submatrix ι ι).PosDef := by
  have hs : ((cartan M).submatrix ι ι).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact cartan_symm M (ι j) (ι i)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  let z:T → ℝ := fun i=>x i/Real.sqrt (scale ρ (ι i))
  have heval (v:T → ℝ) (i:T) : (∑ j,v j • Pi.single (ι j) (1:ℝ)) (ι i)=v i := by
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    simp [hι.eq_iff]
  have hz:(∑ i,z i • Pi.single (ι i) (1:ℝ))≠0 := by
    intro h
    apply hx
    ext i
    have hi:=congrFun h (ι i)
    rw [heval] at hi
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (Real.sqrt_pos.2 (scale_pos ρ (ι i))))
  have hpos:=form_pos ρ _ hz
  rw [form_matrix ρ ι g hg] at hpos
  have he : (∑ i,∑ j,scale ρ (ι i)*cartan M (ι i) (ι j)*z i*z j)=
      x ⬝ᵥ (((cartan M).submatrix ι ι) *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:cartan M (ι i) (ι j)=0
    · simp [hij]
    · have hd:=mul_right_cancel₀ hij (scale_balance ρ ι g hg i j)
      have hn:=ne_of_gt (Real.sqrt_pos.2 (scale_pos ρ (ι i)))
      have hsq:=Real.sq_sqrt (scale_pos ρ (ι i)).le
      dsimp [z]
      rw [← hd]
      field_simp
      rw [hsq]
      ring
  rw [he] at hpos
  simpa only [star_trivial] using hpos

end HarmonicArtin.Geometric.FiniteOrbit

end OAI
