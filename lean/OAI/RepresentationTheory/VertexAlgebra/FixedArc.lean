import OAI.RepresentationTheory.VertexAlgebra.LocalImplementer

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.SmoothCircleLift
 

lemma fixed_arc_deck (F : SmoothCircleLift) (I : ProperCircleArc)
    (hF : ∀ z ∈ I.carrier, F.onCircle z=z) :
    ∃ n : ℤ, ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ I.carrier → F x=x+n*(2*Real.pi) := by
  let S := Ioo I.left I.right
  have hz (x : S) : F x-x ∈ AddSubgroup.zmultiples (2*Real.pi) := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [AddCircle.coe_sub]
    apply sub_eq_zero.mpr
    exact hF _ ⟨x,x.property,rfl⟩
  let D : S → AddSubgroup.zmultiples (2*Real.pi) := fun x => ⟨F x-x,hz x⟩
  have hD : Continuous D := ((F.smooth.continuous.comp continuous_subtype_val).sub
    continuous_subtype_val).subtype_mk hz
  have hl : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).mpr hD
  let : PreconnectedSpace S := Subtype.preconnectedSpace isPreconnected_Ioo
  let x₀ : S := ⟨(I.left+I.right)/2,by constructor <;> linarith [I.nonempty']⟩
  obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hz x₀)
  simp only [zsmul_eq_mul] at hn
  have he (y : S) : F y-y=n*(2*Real.pi) := by
    exact (congrArg Subtype.val (hl.apply_eq_of_preconnectedSpace y x₀)).trans hn.symm
  refine ⟨n,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hx
  have hm : x-y ∈ AddSubgroup.zmultiples (2*Real.pi) := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (y : AddCircle (2*Real.pi))=(x : AddCircle (2*Real.pi)) at hxy
    rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨m,hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  simp only [zsmul_eq_mul] at hm
  have hrep : x=y+m*(2*Real.pi) := by linarith
  rw [hrep,F.integer_shift]
  linarith [he ⟨y,hy⟩]
lemma fixed_arc_normalize (F : SmoothCircleLift) (I : ProperCircleArc)
    (hF : ∀ z ∈ I.carrier, F.onCircle z=z) :
    ∃ G : SmoothCircleLift, G.onCircle=F.onCircle ∧
      ∀ x : ℝ, (x : AddCircle (2*Real.pi)) ∈ I.carrier → G x=x := by
  obtain ⟨n,hn⟩ := F.fixed_arc_deck I hF
  refine ⟨rotation (((-n : ℤ):ℝ)*(2*Real.pi))*F,?_,?_⟩
  · funext z
    rw [onCircle_mul,deck_onCircle]
  · intro x hx
    simp only [mul_apply,rotation_apply,Int.cast_neg,neg_mul,hn x hx]
    ring
end StronglyRationalVOA.SmoothCircleLift
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_conjugation_eq_of_circle (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : SmoothCircleLift) (h : F.onCircle=G.onCircle) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv=
      (U.diffeomorphismImplementer hc G).conjStarAlgEquiv := by
  apply projective_equality_conjugation
  change U.diffeomorphismProjectiveRepresentation hc (QuotientGroup.mk F)=
    U.diffeomorphismProjectiveRepresentation hc (QuotientGroup.mk G)
  congr 1
  apply QuotientGroup.eq.mpr
  change SmoothCircleLift.circleAction (F⁻¹*G)=1
  rw [map_mul,map_inv]
  have he : SmoothCircleLift.circleAction F=SmoothCircleLift.circleAction G := by
    ext z; exact congrFun h z
  rw [he,inv_mul_cancel]
 

lemma diffeomorphism_local_action (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (I : ProperCircleArc)
    (hF : ∀ z ∈ I.carrier, F.onCircle z=z)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ U.intervalAlgebra hc I) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv Q=Q := by
  obtain ⟨G,hG,hfixed⟩ := F.fixed_arc_normalize I hF
  rw [U.diffeomorphism_conjugation_eq_of_circle hc F G hG.symm]
  exact U.diffeomorphism_local_action_of_fixed_lift hc G I.isOpen_carrier hfixed hQ
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
