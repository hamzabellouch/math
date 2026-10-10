import OAI.RepresentationTheory.VertexAlgebra.CovarianceContinuation

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
 

def Rel (M : SL(2,ℝ)) (x y : ℝ) : Prop :=
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.sin (y/2)=
    (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.cos (y/2)
def Implements (M : SL(2,ℝ)) (F : SmoothCircleLift) : Prop := ∀ x, Rel M x (F x)
 
def density (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  (M 1 1*Real.cos (x/2)-M 0 1*Real.sin (x/2))^2+
    (M 0 0*Real.sin (x/2)-M 1 0*Real.cos (x/2))^2
lemma det (M : SL(2,ℝ)) : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
  simpa only [Matrix.det_fin_two] using M.det_coe
lemma cos_sq_add_sin_sq (x : ℝ) : Real.cos x^2+Real.sin x^2=1 := by
  nlinarith [Real.sin_sq_add_cos_sq x]
lemma collinear_unit {p q c s : ℝ} (hu : c^2+s^2=1) (h : p*s=q*c) :
    (p*c+q*s)*c=p ∧ (p*c+q*s)*s=q := by
  constructor
  · linear_combination p*hu-s*h
  · linear_combination q*hu+c*h
 
lemma derivative_density (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) (x : ℝ) :
    deriv F x=density M (F x) := by
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  have hdet : a*d-b*c=1 := det M
  have hrel (y : ℝ) :
      (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (F y/2)=
      (c*Real.cos (y/2)+d*Real.sin (y/2))*Real.cos (F y/2) := hF y
  let r := (a*Real.cos (x/2)+b*Real.sin (x/2))*Real.cos (F x/2)+
    (c*Real.cos (x/2)+d*Real.sin (x/2))*Real.sin (F x/2)
  obtain ⟨hr1,hr2⟩ := collinear_unit (cos_sq_add_sin_sq (F x/2)) (hrel x)
  change r*Real.cos (F x/2)=a*Real.cos (x/2)+b*Real.sin (x/2) at hr1
  change r*Real.sin (F x/2)=c*Real.cos (x/2)+d*Real.sin (x/2) at hr2
  have hid := (hasDerivAt_id x).div_const (2:ℝ)
  have hfd : HasDerivAt (fun y : ℝ => F y/2) (deriv F x/2) x :=
    (F.differentiable x).hasDerivAt.div_const 2
  have hl := ((hid.cos.const_mul a).add (hid.sin.const_mul b)).mul hfd.sin
  have hr := ((hid.cos.const_mul c).add (hid.sin.const_mul d)).mul hfd.cos
  have he : (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (F y/2))=
      (fun y => (c*Real.cos (y/2)+d*Real.sin (y/2))*Real.cos (F y/2)) := funext hrel
  change HasDerivAt (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (F y/2)) _ x at hl
  rw [he] at hl
  have hd := hl.unique hr
  dsimp only [id, Pi.add_apply] at hd
  have hd' : r*deriv F x=
      (-c*Real.sin (x/2)+d*Real.cos (x/2))*Real.cos (F x/2)-
      (-a*Real.sin (x/2)+b*Real.cos (x/2))*Real.sin (F x/2) := by
    dsimp only [r]
    linear_combination 2*hd
  have hrd : r^2*deriv F x=1 := by
    calc
      _ = r*(r*deriv F x) := by ring
      _ = (-c*Real.sin (x/2)+d*Real.cos (x/2))*(r*Real.cos (F x/2))-
          (-a*Real.sin (x/2)+b*Real.cos (x/2))*(r*Real.sin (F x/2)) := by rw [hd']; ring
      _ = (a*d-b*c)*(Real.cos (x/2)^2+Real.sin (x/2)^2) := by rw [hr1,hr2]; ring
      _ = 1 := by rw [hdet,cos_sq_add_sin_sq]; ring
  have hrne : r ≠ 0 := by intro h; simp [h] at hrd
  have hb1 : r*(d*Real.cos (F x/2)-b*Real.sin (F x/2))=Real.cos (x/2) := by
    calc
      _ = d*(r*Real.cos (F x/2))-b*(r*Real.sin (F x/2)) := by ring
      _ = (a*d-b*c)*Real.cos (x/2) := by rw [hr1,hr2]; ring
      _ = _ := by rw [hdet,one_mul]
  have hb2 : r*(a*Real.sin (F x/2)-c*Real.cos (F x/2))=Real.sin (x/2) := by
    calc
      _ = a*(r*Real.sin (F x/2))-c*(r*Real.cos (F x/2)) := by ring
      _ = (a*d-b*c)*Real.sin (x/2) := by rw [hr1,hr2]; ring
      _ = _ := by rw [hdet,one_mul]
  have hnorm : r^2*density M (F x)=1 := by
    calc
      _ = (r*(d*Real.cos (F x/2)-b*Real.sin (F x/2)))^2+
          (r*(a*Real.sin (F x/2)-c*Real.cos (F x/2)))^2 := by dsimp [density,a,b,c,d]; ring
      _ = 1 := by rw [hb1,hb2,cos_sq_add_sin_sq]
  exact mul_left_cancel₀ (pow_ne_zero 2 hrne) (hrd.trans hnorm.symm)
def constant (M : SL(2,ℝ)) : ℝ := (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2
def cosine (M : SL(2,ℝ)) : ℝ := (M 1 0^2+M 1 1^2-M 0 0^2-M 0 1^2)/2
def sine (M : SL(2,ℝ)) : ℝ := -(M 0 0*M 1 0+M 0 1*M 1 1)
lemma density_trigonometric (M : SL(2,ℝ)) (x : ℝ) :
    density M x=constant M+cosine M*Real.cos x+sine M*Real.sin x := by
  have hc : Real.cos x=Real.cos (x/2)^2-Real.sin (x/2)^2 := by
    have H := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at H
    nlinarith [cos_sq_add_sin_sq (x/2)]
  have hs : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    have H := Real.sin_two_mul (x/2)
    rwa [show 2*(x/2)=x by ring] at H
  rw [hc,hs]
  dsimp only [density,constant,cosine,sine]
  linear_combination (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2*cos_sq_add_sin_sq (x/2)
lemma determinant_constants (M : SL(2,ℝ)) : constant M^2-cosine M^2-sine M^2=1 := by
  calc
    _ = (M 0 0*M 1 1-M 0 1*M 1 0)^2 := by dsimp [constant,cosine,sine]; ring
    _ = 1 := by rw [det]; norm_num
lemma push_constant (M : SL(2,ℝ)) (F : SmoothCircleLift) (hF : Implements M F) :
    F.pushDensity 1 (fun _ => 1)=density M := by
  funext x
  simp only [SmoothCircleLift.pushDensity,pow_one,mul_one,derivative_density M F hF,
    SmoothCircleLift.apply_inv_apply]
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
