import OAI.RepresentationTheory.VertexAlgebra.ModuleCreationVacuum
import OAI.RepresentationTheory.VertexAlgebra.ModuleSpectralNorms
import OAI.RepresentationTheory.VertexAlgebra.CreationDistribution

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
open UniformSpace
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

def creationVacuumSmear (a : W) (f : SmoothCircleFunction) : Completion W :=
  ∑' n : ℕ, f.coefficient (-(n:ℤ)) • M.creationVacuumCoefficient a n

def localVacuumCreations (I : ProperCircleArc) : Set (Completion W) :=
  {x | ∃ (a : W) (z : ℂ), a ∈ M.grade z ∧ ∃ f : SmoothCircleFunction,
    tsupport f.onCircle ⊆ I.carrier ∧ x = M.creationVacuumSmear a f}

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

theorem creation_scalar_polynomial_bound (t : EnergyBand) {h : ℕ} {a : W}
    (ha : a ∈ M.bandGrade t h) (η : Completion W) (n : ℕ) :
    ‖inner ℂ η (M.creationVacuumCoefficient a n)‖ ≤
      (‖η‖*‖a‖)*(1+(n:ℝ))^(h+1) := by
  calc
    _ ≤ ‖η‖*‖M.creationVacuumCoefficient a n‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*((1+(n:ℝ))^(h+1)*‖a‖) := by
      gcongr
      exact Q.creationVacuumCoefficient_norm t ha n
    _ = _ := by ring

theorem creationVacuumSmear_inner (t : EnergyBand) {h : ℕ} {a : W}
    (ha : a ∈ M.bandGrade t h) (η : Completion W) (f : SmoothCircleFunction) :
    inner ℂ η (M.creationVacuumSmear a f) =
      ScalarCreationSmear (fun n => inner ℂ η (M.creationVacuumCoefficient a n)) f := by
  unfold creationVacuumSmear ScalarCreationSmear
  rw [inner_tsum_right (Q.creationVacuumSmear_summable t ha f).of_norm]
  simp only [inner_smul_right]

theorem creationVacuumSmear_orthogonal (I : ProperCircleArc) {η : Completion W}
    (hη : ∀ x ∈ M.localVacuumCreations I, inner ℂ η x = 0) : η = 0 := by
  have hband (t : EnergyBand) (h : ℕ) (a : W) (ha : a ∈ M.bandGrade t h) :
      inner ℂ η (a:Completion W) = 0 := by
    have H := scalarCreation_constant_zero_of_local
      (Q.creation_scalar_polynomial_bound t ha η) I (by
        intro f hf
        rw [← Q.creationVacuumSmear_inner t ha η f]
        exact hη _ ⟨a, (t.val:ℂ)+h, ha, f, hf, rfl⟩)
    simpa using H
  have halg (a : W) : inner ℂ η (a:Completion W) = 0 := by
    apply M.homogeneous_induction (P := fun a => inner ℂ η (a:Completion W) = 0)
      (by simp only [Completion.coe_zero, inner_zero_right]) _
      (fun a b ha hb => by simp [Completion.coe_add, inner_add_right, ha, hb]) a
    intro z a ha
    by_cases ha0 : a=0
    · simp only [ha0, Completion.coe_zero, inner_zero_right]
    obtain ⟨t, h, hz⟩ := Q.exists_band_of_mem ha ha0
    exact hband t h a (by change a ∈ M.grade _; rwa [← hz])
  have hself : inner ℂ η η = 0 :=
    Completion.denseRange_coe.induction_on (p := fun x => inner ℂ η x = 0) η
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const) halg
  exact inner_self_eq_zero.mp hself

 

theorem localVacuumCreations_total (I : ProperCircleArc) :
    (Submodule.span ℂ (M.localVacuumCreations I)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro η hη
  apply Q.creationVacuumSmear_orthogonal I
  intro x hx
  exact inner_eq_zero_symm.mp (hη x (Submodule.subset_span hx))

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
