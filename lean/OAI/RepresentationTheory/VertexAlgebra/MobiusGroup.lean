import OAI.RepresentationTheory.VertexAlgebra.MobiusGeometry
import OAI.RepresentationTheory.VertexAlgebra.SmoothTopology

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma implements_one : Implements 1 (1 : SmoothCircleLift) := by
  intro x
  simp [Rel,mul_comm]
lemma implements_mul {M N : SL(2,ℝ)} {F G : SmoothCircleLift}
    (hF : Implements M F) (hG : Implements N G) : Implements (M*N) (F*G) := by
  intro x
  have hh := hF (G x)
  have hg := hG x
  obtain ⟨hr1,hr2⟩ := collinear_unit (cos_sq_add_sin_sq (G x/2)) hg
  let r := (N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2))*Real.cos (G x/2)+
    (N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2))*Real.sin (G x/2)
  change r*Real.cos (G x/2)=N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2) at hr1
  change r*Real.sin (G x/2)=N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2) at hr2
  change (M 0 0*Real.cos (G x/2)+M 0 1*Real.sin (G x/2))*Real.sin (F (G x)/2)=
    (M 1 0*Real.cos (G x/2)+M 1 1*Real.sin (G x/2))*Real.cos (F (G x)/2) at hh
  simp only [Rel,SmoothCircleLift.mul_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination r*hh+(M 1 0*Real.cos (F (G x)/2)-M 0 0*Real.sin (F (G x)/2))*hr1+
    (M 1 1*Real.cos (F (G x)/2)-M 0 1*Real.sin (F (G x)/2))*hr2
lemma implements_inv {M : SL(2,ℝ)} {F : SmoothCircleLift}
    (hF : Implements M F) : Implements M⁻¹ F⁻¹ := by
  intro x
  have h := hF (F⁻¹ x)
  rw [Rel,F.apply_inv_apply] at h
  simp only [Rel,Matrix.SpecialLinearGroup.SL2_inv_expl,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  linear_combination -h
 

def lifts : Subgroup SmoothCircleLift where
  carrier := {F | ∃ M : SL(2,ℝ), Implements M F}
  one_mem' := ⟨1,implements_one⟩
  mul_mem' := by rintro F G ⟨M,hM⟩ ⟨N,hN⟩; exact ⟨M*N,implements_mul hM hN⟩
  inv_mem' := by rintro F ⟨M,hM⟩; exact ⟨M⁻¹,implements_inv hM⟩
def rotationMatrix (s : ℝ) : SL(2,ℝ) :=
  ⟨!![Real.cos (s/2),-Real.sin (s/2);Real.sin (s/2),Real.cos (s/2)],by
    simp only [Matrix.det_fin_two_of]
    nlinarith [cos_sq_add_sin_sq (s/2)]⟩
lemma implements_rotation (s : ℝ) : Implements (rotationMatrix s) (SmoothCircleLift.rotation s) := by
  intro x
  change (Real.cos (s/2)*Real.cos (x/2)+(-Real.sin (s/2))*Real.sin (x/2))*Real.sin ((x+s)/2)=
    (Real.sin (s/2)*Real.cos (x/2)+Real.cos (s/2)*Real.sin (x/2))*Real.cos ((x+s)/2)
  rw [show (x+s)/2=x/2+s/2 by ring,Real.sin_add,Real.cos_add]
  ring
lemma rotation_mem (s : ℝ) : SmoothCircleLift.rotation s ∈ lifts := ⟨rotationMatrix s,implements_rotation s⟩
def rotation (s : ℝ) : lifts := ⟨SmoothCircleLift.rotation s,rotation_mem s⟩
lemma rotation_zero : rotation 0=1 := Subtype.ext SmoothCircleLift.rotation_zero
lemma rotation_add (s t : ℝ) : rotation (s+t)=rotation s*rotation t :=
  Subtype.ext (SmoothCircleLift.rotation_add s t)
 

abbrev Group := lifts ⧸ (SmoothCircleLift.circleAction.comp lifts.subtype).ker
 
def inclusion : Group →* SmoothCircleDiffeomorphism :=
  QuotientGroup.lift (SmoothCircleLift.circleAction.comp lifts.subtype).ker
    ((QuotientGroup.mk' SmoothCircleLift.circleAction.ker).comp lifts.subtype) (by
      intro F hF
      exact (QuotientGroup.eq_one_iff _).mpr hF)
lemma inclusion_injective : Function.Injective inclusion := by
  apply (injective_iff_map_eq_one _).mpr
  intro F
  induction F using QuotientGroup.induction_on with
  | H F =>
    intro h
    apply (QuotientGroup.eq_one_iff F).mpr
    exact (QuotientGroup.eq_one_iff (F:SmoothCircleLift)).mp h
lemma inclusion_continuous : Continuous inclusion := by
  apply (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous_iff.mpr
  exact (QuotientGroup.isQuotientMap_mk SmoothCircleLift.circleAction.ker).continuous.comp continuous_subtype_val
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
