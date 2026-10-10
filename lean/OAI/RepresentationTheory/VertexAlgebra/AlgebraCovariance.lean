import OAI.RepresentationTheory.VertexAlgebra.GraphCovariance

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA
lemma projective_equality_conjugation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (E F : H ≃ₗᵢ[ℂ] H)
    (h : (QuotientGroup.mk E : ProjectiveUnitaryGroup H)=QuotientGroup.mk F) :
    E.conjStarAlgEquiv=F.conjStarAlgEquiv := by
  obtain ⟨c,_,hc⟩ := QuotientGroup.eq.mp h
  have he (x : H) : F x=c • E x := by
    have H := congrArg E (hc x)
    change E (E.symm (F x))=E (c • x) at H
    simpa only [E.apply_symm_apply,map_smul] using H
  ext B x
  change E (B (E.symm x))=F (B (F.symm x))
  have hi : E.symm x=c • F.symm x := by
    apply E.injective
    rw [E.apply_symm_apply,map_smul,← he,F.apply_symm_apply]
  rw [hi,map_smul,map_smul,← he]
end StronglyRationalVOA

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_conjugate_primary_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (T : U.PrimaryTestField) {O : Set (AddCircle (2*Real.pi))}
    (hT : tsupport T.test.onCircle ⊆ O)
    {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.localAlgebra hc (F.onCircle '' O)).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (T.field hc).graph) :
    (((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q) x,
      ((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q) y) ∈ (T.field hc).graph := by
  obtain ⟨c,hc'⟩ := U.diffeomorphism_primaryTest_graph hc F T
  let E := U.diffeomorphismImplementer hc F
  have H := U.local_commutant_preserves_graph hc hQ T.homogeneous
    (F.pushTest (T.weight-1) T.test)
    ((F.pushTest_support (T.weight-1) T.test).trans (image_mono hT)) ((hc' x y).mp hxy)
  apply (hc' _ _).mpr
  change (E (E.symm (Q (E x))),E (E.symm (Q (E y)))+c • E (E.symm (Q (E x)))) ∈ _
  simpa only [E.apply_symm_apply,map_add,map_smul] using H
lemma diffeomorphism_conjugate_commutant (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.localAlgebra hc (F.onCircle '' O)).commutant) :
    (U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q ∈
      (U.localAlgebra hc O).commutant := by
  rw [U.localAlgebra_eq_primaryAlgebra hc hO,← SetLike.mem_coe,
    primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  let E := U.diffeomorphismImplementer hc F
  have hdata : ∀ B ∈ U.primaryGraphData hc O,
      E.symm.conjStarAlgEquiv Q*B=B*E.symm.conjStarAlgEquiv Q := by
    rintro B ⟨T,hT,i,j,rfl⟩
    apply ClosedGraphData.entry_commutes_of_graph_invariant
    · intro x y hxy
      exact U.diffeomorphism_conjugate_primary_graph hc F T hT hQ hxy
    · intro x y hxy
      have h := U.diffeomorphism_conjugate_primary_graph hc F T hT (star_mem hQ) hxy
      have hs : (U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv (star Q)=
          star ((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv Q) :=
        ((U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv).map_star' Q
      rw [hs] at h
      exact h
  intro B hB
  rcases hB with hB | hB
  · exact (hdata B hB).symm
  · apply (hdata B ?_).symm
    obtain ⟨T,hT,i,j,he⟩ := hB
    refine ⟨T,hT,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
 

lemma localAlgebra_diffeomorphism_mem (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    {B : Completion V →L[ℂ] Completion V} (hB : B ∈ U.localAlgebra hc O) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈ U.localAlgebra hc (F.onCircle '' O) := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.localAlgebra hc (F.onCircle '' O)),
    VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  have h := (VonNeumannAlgebra.mem_commutant_iff.mp
    (U.diffeomorphism_conjugate_commutant hc F hO hQ)) B hB
  have H := congrArg (U.diffeomorphismImplementer hc F).conjStarAlgEquiv h
  simpa only [map_mul,← LinearIsometryEquiv.symm_conjStarAlgEquiv,StarAlgEquiv.apply_symm_apply] using H.symm
lemma diffeomorphism_inverse_conjugation (hc : A.toVertexAlgebra.C2Cofinite) (F : SmoothCircleLift) :
    (U.diffeomorphismImplementer hc F⁻¹).conjStarAlgEquiv=
      (U.diffeomorphismImplementer hc F).symm.conjStarAlgEquiv := by
  apply projective_equality_conjugation
  exact (U.liftProjectiveRepresentation hc).map_inv F
 
lemma localAlgebra_diffeomorphism_iff (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (B : Completion V →L[ℂ] Completion V) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈ U.localAlgebra hc (F.onCircle '' O) ↔
      B ∈ U.localAlgebra hc O := by
  constructor
  · intro hB
    have H := U.localAlgebra_diffeomorphism_mem hc F⁻¹ (F.circleHomeomorph.isOpenMap O hO) hB
    have hset : F⁻¹.onCircle '' (F.onCircle '' O)=O := by
      rw [← image_comp]
      simp only [Function.comp_def,F.onCircle_inverse,image_id']
    change (U.diffeomorphismImplementer hc F⁻¹).conjStarAlgEquiv
      ((U.diffeomorphismImplementer hc F).conjStarAlgEquiv B) ∈
      U.localAlgebra hc (F⁻¹.onCircle '' (F.onCircle '' O)) at H
    rw [hset,U.diffeomorphism_inverse_conjugation hc F,
      ← LinearIsometryEquiv.symm_conjStarAlgEquiv,StarAlgEquiv.symm_apply_apply] at H
    exact H
  · exact U.localAlgebra_diffeomorphism_mem hc F hO
lemma intervalAlgebra_diffeomorphism_iff (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (I : ProperCircleArc) (B : Completion V →L[ℂ] Completion V) :
    (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈ U.intervalAlgebra hc (F.mapArc I) ↔
      B ∈ U.intervalAlgebra hc I := by
  change _ ∈ U.localAlgebra hc (F.mapArc I).carrier ↔ _
  rw [F.mapArc_carrier]
  exact U.localAlgebra_diffeomorphism_iff hc F I.isOpen_carrier B
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
