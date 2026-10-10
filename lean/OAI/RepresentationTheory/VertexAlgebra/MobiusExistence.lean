import OAI.RepresentationTheory.VertexAlgebra.MobiusGroup

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma derivative_pos_of_rel (M : SL(2,ℝ)) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hrel : ∀ x, Rel M x (f x)) (x : ℝ) : 0 < deriv f x := by
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  have hdet : a*d-b*c=1 := det M
  let r := (a*Real.cos (x/2)+b*Real.sin (x/2))*Real.cos (f x/2)+
    (c*Real.cos (x/2)+d*Real.sin (x/2))*Real.sin (f x/2)
  obtain ⟨hr1,hr2⟩ := collinear_unit (cos_sq_add_sin_sq (f x/2)) (hrel x)
  change r*Real.cos (f x/2)=a*Real.cos (x/2)+b*Real.sin (x/2) at hr1
  change r*Real.sin (f x/2)=c*Real.cos (x/2)+d*Real.sin (x/2) at hr2
  have hid := (hasDerivAt_id x).div_const (2:ℝ)
  have hfd := (hf x).hasDerivAt.div_const 2
  have hl := ((hid.cos.const_mul a).add (hid.sin.const_mul b)).mul hfd.sin
  have hr := ((hid.cos.const_mul c).add (hid.sin.const_mul d)).mul hfd.cos
  have he : (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (f y/2))=
      (fun y => (c*Real.cos (y/2)+d*Real.sin (y/2))*Real.cos (f y/2)) := funext hrel
  change HasDerivAt (fun y => (a*Real.cos (y/2)+b*Real.sin (y/2))*Real.sin (f y/2)) _ x at hl
  rw [he] at hl
  have hd := hl.unique hr
  dsimp only [id, Pi.add_apply] at hd
  have hd' : r*deriv f x=
      (-c*Real.sin (x/2)+d*Real.cos (x/2))*Real.cos (f x/2)-
      (-a*Real.sin (x/2)+b*Real.cos (x/2))*Real.sin (f x/2) := by
    dsimp only [r]
    linear_combination 2*hd
  have hrd : r^2*deriv f x=1 := by
    calc
      _ = r*(r*deriv f x) := by ring
      _ = (-c*Real.sin (x/2)+d*Real.cos (x/2))*(r*Real.cos (f x/2))-
          (-a*Real.sin (x/2)+b*Real.cos (x/2))*(r*Real.sin (f x/2)) := by rw [hd']; ring
      _ = (a*d-b*c)*(Real.cos (x/2)^2+Real.sin (x/2)^2) := by rw [hr1,hr2]; ring
      _ = 1 := by rw [hdet,cos_sq_add_sin_sq]; ring
  nlinarith [sq_nonneg r]

 

def dot (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.cos (x/2)+
  (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.sin (x/2)
def cross (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.cos (x/2)-
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.sin (x/2)
def positiveLiftFun (M : SL(2,ℝ)) (x : ℝ) : ℝ :=
  x+2*Real.arctan (cross M x/dot M x)
lemma positiveLiftFun_rel (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) (x : ℝ) :
    Rel M x (positiveLiftFun M x) := by
  have ht : Real.sin (Real.arctan (cross M x/dot M x))=
      (cross M x/dot M x)*Real.cos (Real.arctan (cross M x/dot M x)) := by
    rw [Real.sin_arctan,Real.cos_arctan]; ring
  unfold Rel positiveLiftFun
  rw [show (x+2*Real.arctan (cross M x/dot M x))/2=
      x/2+Real.arctan (cross M x/dot M x) by ring,Real.sin_add,Real.cos_add,ht]
  have hd : dot M x ≠ 0 := (hp x).ne'
  field_simp
  dsimp only [dot,cross]
  ring
lemma dot_smooth (M : SL(2,ℝ)) : ContDiff ℝ ∞ (dot M) := by
  have hc : ContDiff ℝ ∞ (fun x:ℝ => Real.cos (x/2)) := (contDiff_id.div_const 2).cos
  have hs : ContDiff ℝ ∞ (fun x:ℝ => Real.sin (x/2)) := (contDiff_id.div_const 2).sin
  exact (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hc).add
    (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hs)
lemma cross_smooth (M : SL(2,ℝ)) : ContDiff ℝ ∞ (cross M) := by
  have hc : ContDiff ℝ ∞ (fun x:ℝ => Real.cos (x/2)) := (contDiff_id.div_const 2).cos
  have hs : ContDiff ℝ ∞ (fun x:ℝ => Real.sin (x/2)) := (contDiff_id.div_const 2).sin
  exact (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hc).sub
    (((contDiff_const.mul hc).add (contDiff_const.mul hs)).mul hs)
lemma positiveLiftFun_smooth (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) :
    ContDiff ℝ ∞ (positiveLiftFun M) :=
  contDiff_id.add (contDiff_const.mul (((cross_smooth M).div (dot_smooth M) (fun x => (hp x).ne')).arctan))
lemma positiveLiftFun_period (M : SL(2,ℝ)) (x : ℝ) :
    positiveLiftFun M (x+2*Real.pi)=positiveLiftFun M x+2*Real.pi := by
  have hd : dot M (x+2*Real.pi)=dot M x := by
    dsimp only [dot]
    rw [show (x+2*Real.pi)/2=x/2+Real.pi by ring,Real.cos_add_pi,Real.sin_add_pi]
    ring
  have hc : cross M (x+2*Real.pi)=cross M x := by
    dsimp only [cross]
    rw [show (x+2*Real.pi)/2=x/2+Real.pi by ring,Real.cos_add_pi,Real.sin_add_pi]
    ring
  simp only [positiveLiftFun,hd,hc]; ring
end StronglyRationalVOA.CircleMobiusGeometry

namespace StronglyRationalVOA.SmoothCircleLift
 

def ofFunction (f : ℝ → ℝ) (hs : ContDiff ℝ ∞ f)
    (hp : ∀ x, f (x+2*Real.pi)=f x+2*Real.pi) (hd : ∀ x, 0 < deriv f x) : SmoothCircleLift := by
  let φ : PositiveCircleGeometry.SmoothLift := {
    toFun := fun x => f (2*Real.pi*x)/(2*Real.pi)
    add_one := by intro x; rw [mul_add,mul_one,hp,add_div,div_self (by positivity : (2*Real.pi:ℝ) ≠ 0)]
    smooth := (hs.comp (contDiff_const.mul contDiff_id)).div_const _
    derivative_pos := by
      intro x
      have hh := (((hs.differentiable (by simp) (2*Real.pi*x)).hasDerivAt).comp x
        ((hasDerivAt_id x).const_mul (2*Real.pi))).div_const (2*Real.pi)
      change HasDerivAt (fun x => f (2*Real.pi*x)/(2*Real.pi)) _ x at hh
      rw [hh.deriv]
      have he : deriv f (2*Real.pi*x)*(2*Real.pi*1)/(2*Real.pi)=deriv f (2*Real.pi*x) := by
        field_simp [Real.pi_ne_zero]
      rw [he]
      exact hd _ }
  have hj : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := φ.surjective (y/(2*Real.pi))
    refine ⟨2*Real.pi*x,?_⟩
    exact (div_left_inj' (by positivity : (2*Real.pi:ℝ) ≠ 0)).mp hx
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse f (strictMono_of_deriv_pos hd)
    (Function.surjInv hj) (Function.rightInverse_surjInv hj)
  refine ⟨e,hs,?_,hp⟩
  have hi := PositiveCircleGeometry.parameter_inverse_smooth (fun _ => e)
    (hs.comp contDiff_snd) (fun _ x => (hd x).ne')
  exact hi.comp ((contDiff_const (c := (0:ℝ))).prodMk contDiff_id)
@[simp] lemma ofFunction_apply (f : ℝ → ℝ) (hs : ContDiff ℝ ∞ f)
    (hp : ∀ x, f (x+2*Real.pi)=f x+2*Real.pi) (hd : ∀ x, 0 < deriv f x) (x : ℝ) :
    ofFunction f hs hp hd x=f x := rfl
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CircleMobiusGeometry

def positiveLift (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) : SmoothCircleLift :=
  SmoothCircleLift.ofFunction (positiveLiftFun M) (positiveLiftFun_smooth M hp)
    (positiveLiftFun_period M) (derivative_pos_of_rel M _
      ((positiveLiftFun_smooth M hp).differentiable (by simp)) (positiveLiftFun_rel M hp))
lemma implements_positiveLift (M : SL(2,ℝ)) (hp : ∀ x, 0 < dot M x) :
    Implements M (positiveLift M hp) := positiveLiftFun_rel M hp
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
