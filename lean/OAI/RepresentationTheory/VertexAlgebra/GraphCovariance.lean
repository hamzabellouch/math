import OAI.RepresentationTheory.VertexAlgebra.CovarianceContinuation

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 

lemma onSubmodule_affine_graph (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (E : H ≃ₗᵢ[ℂ] H) (e : D ≃ₗᵢ[ℂ] D) (he : ∀ z : D, (e z : H)=E z)
    (c : ℂ) (hcov : ∀ z : D, Q (e z)=e (P z)+c • e z)
    (hP : (onSubmodule D P).IsClosable) (hQ : (onSubmodule D Q).IsClosable)
    {x y : H} (hxy : (x,y) ∈ (onSubmodule D P).closure.graph) :
    (E x,E y+c • E x) ∈ (onSubmodule D Q).closure.graph := by
  rw [← hP.graph_closure_eq_closure_graph] at hxy
  have hclosed : IsClosed {p : H × H |
      (E p.1,E p.2+c • E p.1) ∈ (onSubmodule D Q).closure.graph} :=
    hQ.closure_isClosed.preimage ((E.continuous.comp continuous_fst).prodMk
      ((E.continuous.comp continuous_snd).add ((E.continuous.comp continuous_fst).const_smul c)))
  apply (closure_minimal (s := ((onSubmodule D P).graph : Set _)) ?_ hclosed) hxy
  rintro p hp
  obtain ⟨z,hz,hPz⟩ := (onSubmodule D P).mem_graph_iff.mp hp
  have ht : ((z : H),(P z : H))=p := Prod.ext hz hPz
  rw [← ht]
  have h := LinearPMap.le_graph_of_le (onSubmodule D Q).le_closure
    (onSubmodule_mem_graph D Q (e z))
  rw [hcov z] at h
  change ((e z : H),(e (P z) : H)+c • (e z : H)) ∈ _ at h
  rw [he z,he (P z)] at h
  exact h
lemma onSubmodule_affine_graph_iff (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (E : H ≃ₗᵢ[ℂ] H) (e : D ≃ₗᵢ[ℂ] D) (he : ∀ z : D, (e z : H)=E z)
    (c : ℂ) (hcov : ∀ z : D, Q (e z)=e (P z)+c • e z)
    (hP : (onSubmodule D P).IsClosable) (hQ : (onSubmodule D Q).IsClosable)
    (x y : H) :
    (x,y) ∈ (onSubmodule D P).closure.graph ↔
    (E x,E y+c • E x) ∈ (onSubmodule D Q).closure.graph := by
  constructor
  · exact onSubmodule_affine_graph D P Q E e he c hcov hP hQ
  · intro hxy
    have hei (z : D) : (e.symm z : H)=E.symm z := by
      apply E.injective
      rw [E.apply_symm_apply,← he,e.apply_symm_apply]
    have hci (z : D) : P (e.symm z)=e.symm (Q z)+(-c) • e.symm z := by
      apply e.injective
      rw [map_add,map_smul,e.apply_symm_apply,e.apply_symm_apply,neg_smul,← sub_eq_add_neg]
      have h := hcov (e.symm z)
      rw [e.apply_symm_apply] at h
      exact eq_sub_iff_add_eq.mpr h.symm
    have h := onSubmodule_affine_graph D Q P E.symm e.symm hei (-c) hci hQ hP hxy
    simpa only [map_add,map_smul,E.symm_apply_apply,neg_smul,add_neg_cancel_right] using h
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma diffeomorphism_primaryTest_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (T : U.PrimaryTestField) :
    ∃ c : ℂ, ∀ x y : Completion V,
      (x,y) ∈ (T.field hc).graph ↔
      (U.diffeomorphismImplementer hc F x,
        U.diffeomorphismImplementer hc F y+c • U.diffeomorphismImplementer hc F x) ∈
      (U.closedSmoothField hc T.state T.weight (F.pushTest (T.weight-1) T.test)).graph := by
  have hcov : ∃ c : ℂ, ∀ y : U.smoothEnergySpace,
      U.smoothSmear hc T.homogeneous (F.pushTest (T.weight-1) T.test).rapid_coefficients
        (U.diffeomorphismSmoothImplementer hc F y)=
      U.diffeomorphismSmoothImplementer hc F
        (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients y)+
        c • U.diffeomorphismSmoothImplementer hc F y := by
    rcases T.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,_⟩
    · have hp : A.IsPrimary T.state := by
        intro n hn
        by_cases h : n=1
        · subst n; exact T.quasiPrimary
        · exact A.virasoro_eq_zero_of_lt (hw ▸ T.homogeneous) n (by omega)
      refine ⟨0,fun y => ?_⟩
      simpa only [zero_smul,add_zero] using
        U.diffeomorphism_primary_test_smooth hc T.homogeneous hp T.hermitian (by omega) F T.test T.real y
    · obtain ⟨c,hc'⟩ := U.diffeomorphism_stress_test_smooth hc F T.test T.real
      refine ⟨c,fun y => ?_⟩
      have HH := hc' y
      simpa only [hw,ha,Nat.reduceSub] using HH
    · refine ⟨0,fun y => ?_⟩
      simpa only [zero_smul,add_zero] using
        U.diffeomorphism_primary_test_smooth hc T.homogeneous hp T.hermitian (by omega) F T.test T.real y
  obtain ⟨c,hc'⟩ := hcov
  refine ⟨c,fun x y => ?_⟩
  have h := SymmetricOperator.onSubmodule_affine_graph_iff U.smoothEnergySpace
    (U.smoothSmear hc T.homogeneous T.test.rapid_coefficients)
    (U.smoothSmear hc T.homogeneous (F.pushTest (T.weight-1) T.test).rapid_coefficients)
    (U.diffeomorphismImplementer hc F) (U.diffeomorphismSmoothImplementer hc F)
    (fun _ => rfl) c hc'
    (U.smoothSmear_core_closable hc T.homogeneous _)
    (U.smoothSmear_core_closable hc T.homogeneous _) x y
  rw [U.smoothSmear_core,U.smoothSmear_core] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
