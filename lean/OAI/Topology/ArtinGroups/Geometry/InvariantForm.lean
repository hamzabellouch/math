import Mathlib
import OAI.Topology.ArtinGroups.Geometry.Cartan

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

noncomputable def invariantForm (x y:S → ℝ) : ℝ :=
  ∑ w:W,representation cs w x ⬝ᵥ representation cs w y

lemma invariantForm_symm (x y:S → ℝ) : invariantForm cs x y=invariantForm cs y x := by
  unfold invariantForm
  apply Finset.sum_congr rfl
  intro w _
  exact dotProduct_comm _ _

lemma invariantForm_sub_right (x y z:S → ℝ) :
    invariantForm cs x (y-z)=invariantForm cs x y-invariantForm cs x z := by
  simp only [invariantForm,map_sub,dotProduct_sub,Finset.sum_sub_distrib]

lemma invariantForm_smul_right (x y:S → ℝ) (r:ℝ) :
    invariantForm cs x (r • y)=r*invariantForm cs x y := by
  simp only [invariantForm,map_smul,dotProduct_smul,smul_eq_mul,Finset.mul_sum]

lemma invariantForm_neg_left (x y:S → ℝ) :
    invariantForm cs (-x) y= -invariantForm cs x y := by
  rw [invariantForm_symm,invariantForm,invariantForm]
  simp only [map_neg,dotProduct_neg,Finset.sum_neg_distrib]
  rw [show (∑ w,representation cs w y ⬝ᵥ representation cs w x)=
    ∑ w,representation cs w x ⬝ᵥ representation cs w y from by
      apply Finset.sum_congr rfl; intro w _; exact dotProduct_comm _ _]

lemma invariantForm_invariant (g:W) (x y:S → ℝ) :
    invariantForm cs (representation cs g x) (representation cs g y)=invariantForm cs x y := by
  unfold invariantForm
  have he (w:W) : representation cs w (representation cs g x) ⬝ᵥ
      representation cs w (representation cs g y)=
      representation cs (w*g) x ⬝ᵥ representation cs (w*g) y := by
    simp only [map_mul,LinearEquiv.mul_apply]
  simp_rw [he]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun w=>rfl)

lemma invariantForm_pos (x:S → ℝ) (hx:x≠0) : 0 < invariantForm cs x x := by
  apply Finset.sum_pos'
  · intro w _
    exact Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  · refine ⟨1,Finset.mem_univ _,?_⟩
    simp only [map_one]
    change 0 < x ⬝ᵥ x
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _=>mul_self_nonneg _))
      (Ne.symm (fun h=>hx (dotProduct_self_eq_zero.mp h)))

lemma invariantForm_basis_row (i:S) (x:S → ℝ) :
    invariantForm cs (Pi.single i 1) x=
      (invariantForm cs (Pi.single i 1) (Pi.single i 1)/2)*(cartan M *ᵥ x) i := by
  have h:=invariantForm_invariant cs (cs.simple i) (Pi.single i 1) x
  have he : simpleReflection M i (Pi.single i 1)= -(Pi.single i 1) := by
    simp only [simpleReflection_apply]
    have hh : (cartan M *ᵥ Pi.single i 1) i=2 := by simp [Matrix.mulVec_single]
    rw [hh]
    module
  simp only [representation_simple] at h
  rw [he,simpleReflection_apply,
    invariantForm_neg_left,invariantForm_sub_right,invariantForm_smul_right] at h
  linarith

noncomputable def invariantScale (i:S) : ℝ := invariantForm cs (Pi.single i 1) (Pi.single i 1)/2

lemma invariantScale_pos (i:S) : 0 < invariantScale cs i := by
  apply div_pos _ (by norm_num)
  apply invariantForm_pos
  intro h
  have hi:=congrFun h i
  simp at hi

lemma invariantScale_balance (i j:S) :
    invariantScale cs i * cartan M i j=invariantScale cs j * cartan M i j := by
  have h:=invariantForm_symm cs (Pi.single i 1) (Pi.single j 1)
  rw [invariantForm_basis_row cs i (Pi.single j 1),invariantForm_basis_row cs j (Pi.single i 1)] at h
  simpa [Matrix.mulVec_single,← cartan_symm M i j,invariantScale] using h

lemma invariantForm_matrix (x y:S → ℝ) :
    invariantForm cs x y=∑ i,∑ j,invariantScale cs i*cartan M i j*x i*y j := by
  have hx : x=∑ i,x i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [invariantForm_symm cs x y]
  conv_lhs => rw [hx]
  simp only [invariantForm,map_sum,map_smul,dotProduct_sum,dotProduct_smul,
    smul_eq_mul]
  rw [Finset.sum_comm]
  have he (i:S) : (∑ w,x i*(representation cs w y ⬝ᵥ representation cs w (Pi.single i 1)))=
      x i*invariantForm cs (Pi.single i 1) y := by
    rw [← Finset.mul_sum,invariantForm_symm]
    rfl
  simp_rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [invariantForm_basis_row cs i y]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,invariantScale]
  apply Finset.sum_congr rfl
  intro j _
  ring

include cs in

theorem cartan_posDef : (cartan M).PosDef := by
  have hs : (cartan M).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact cartan_symm M j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  let z:S → ℝ := fun i=>x i/Real.sqrt (invariantScale cs i)
  have hz:z≠0 := by
    intro h
    apply hx
    ext i
    have hi:=congrFun h i
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (Real.sqrt_pos.2 (invariantScale_pos cs i)))
  have hpos:=invariantForm_pos cs z hz
  rw [invariantForm_matrix] at hpos
  have he : (∑ i,∑ j,invariantScale cs i*cartan M i j*z i*z j)=x ⬝ᵥ (cartan M *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:cartan M i j=0
    · simp [hij]
    · have hd:=mul_right_cancel₀ hij (invariantScale_balance cs i j)
      have hn:=ne_of_gt (Real.sqrt_pos.2 (invariantScale_pos cs i))
      have hsq:=Real.sq_sqrt (invariantScale_pos cs i).le
      dsimp [z]
      rw [← hd]
      field_simp
      rw [hsq]
      ring
  rw [he] at hpos
  simpa only [star_trivial] using hpos

end HarmonicArtin.Geometric

end OAI
