import OAI.RepresentationTheory.VertexAlgebra.MobiusFullGeometry

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups
namespace StronglyRationalVOA.CircleMobiusGeometry
 
lemma rel_circle_unique (M : SL(2,ℝ)) {x y z : ℝ} (hy : Rel M x y) (hz : Rel M x z) :
    (y : AddCircle (2*Real.pi))=(z : AddCircle (2*Real.pi)) := by
  let p := M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2)
  let q := M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2)
  let r := p*Real.cos (y/2)+q*Real.sin (y/2)
  obtain ⟨h1,h2⟩ := collinear_unit (cos_sq_add_sin_sq (y/2)) hy
  change r*Real.cos (y/2)=p at h1
  change r*Real.sin (y/2)=q at h2
  have hnon : p ≠ 0 ∨ q ≠ 0 := by
    by_contra h
    push Not at h
    have hc : Real.cos (x/2)=0 := by
      have hh := det M
      dsimp [p,q] at h
      linear_combination M 1 1*h.1-M 0 1*h.2-Real.cos (x/2)*hh
    have hs : Real.sin (x/2)=0 := by
      have hh := det M
      dsimp [p,q] at h
      linear_combination -M 1 0*h.1+M 0 0*h.2-Real.sin (x/2)*hh
    have hh := cos_sq_add_sin_sq (x/2)
    rw [hc,hs] at hh
    norm_num at hh
  have hr : r ≠ 0 := by
    intro h
    rw [h,zero_mul] at h1 h2
    exact hnon.elim (fun hp => hp h1.symm) (fun hq => hq h2.symm)
  have hsin : Real.sin ((z-y)/2)=0 := by
    apply (mul_eq_zero.mp (show r*Real.sin ((z-y)/2)=0 from ?_)).resolve_left hr
    rw [show (z-y)/2=z/2-y/2 by ring,Real.sin_sub]
    change p*Real.sin (z/2)=q*Real.cos (z/2) at hz
    linear_combination hz+Real.sin (z/2)*h1-Real.cos (z/2)*h2
  obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hsin
  apply sub_eq_zero.mp
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-n,?_⟩
  simp only [zsmul_eq_mul,Int.cast_neg]
  linarith
lemma implements_circle_unique {M : SL(2,ℝ)} {F G : SmoothCircleLift}
    (hF : Implements M F) (hG : Implements M G) : F.onCircle=G.onCircle := by
  funext x
  induction x using QuotientAddGroup.induction_on with
  | H x => exact rel_circle_unique M (hF x) (hG x)
lemma group_mk_eq {F G : lifts} (h : (F:SmoothCircleLift).onCircle=(G:SmoothCircleLift).onCircle) :
    (QuotientGroup.mk F : Group)=QuotientGroup.mk G := by
  apply inclusion_injective
  apply QuotientGroup.eq.mpr
  change (SmoothCircleLift.circleAction ((F:SmoothCircleLift)⁻¹*(G:SmoothCircleLift)))=1
  rw [map_mul,map_inv]
  have he : SmoothCircleLift.circleAction (F:SmoothCircleLift)=SmoothCircleLift.circleAction (G:SmoothCircleLift) :=
    Equiv.ext (congrFun h)
  rw [he,inv_mul_cancel]
 
def standardAction : SL(2,ℝ) →* Group where
  toFun M := QuotientGroup.mk (⟨(exists_implements M).choose, M, (exists_implements M).choose_spec⟩ : lifts)
  map_one' := by
    apply group_mk_eq
    exact implements_circle_unique (exists_implements 1).choose_spec implements_one
  map_mul' M N := by
    apply group_mk_eq
    exact implements_circle_unique (exists_implements (M*N)).choose_spec
      (implements_mul (exists_implements M).choose_spec (exists_implements N).choose_spec)
lemma standardAction_eq_mk {M : SL(2,ℝ)} {F : SmoothCircleLift} (hF : Implements M F) :
    standardAction M=QuotientGroup.mk (⟨F,M,hF⟩ : lifts) :=
  group_mk_eq (implements_circle_unique (exists_implements M).choose_spec hF)
lemma standardAction_surjective : Function.Surjective standardAction := by
  intro F
  induction F using QuotientGroup.induction_on with
  | H F =>
    obtain ⟨M,hM⟩ := F.property
    exact ⟨M,standardAction_eq_mk hM⟩
lemma center_le_standardAction_ker : Subgroup.center (SL(2,ℝ)) ≤ standardAction.ker := by
  intro M hM
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hM
  have h : Implements M (1:SmoothCircleLift) := by
    intro x
    simp only [Rel,← he,Matrix.scalar_apply,Matrix.diagonal_apply,SmoothCircleLift.one_apply]
    simp [mul_assoc,mul_comm,mul_left_comm]
  change standardAction M=1
  exact standardAction_eq_mk h
 

def projectiveStandardAction : PSL(2,ℝ) →* Group :=
  QuotientGroup.lift (Subgroup.center (SL(2,ℝ))) standardAction center_le_standardAction_ker
@[simp] lemma projectiveStandardAction_rotation (t : ℝ) :
    projectiveStandardAction (QuotientGroup.mk (rotationMatrix t))=QuotientGroup.mk (rotation t) :=
  standardAction_eq_mk (implements_rotation t)
lemma projectiveStandardAction_surjective : Function.Surjective projectiveStandardAction := by
  intro F
  obtain ⟨M,hM⟩ := standardAction_surjective F
  exact ⟨QuotientGroup.mk M,hM⟩
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
