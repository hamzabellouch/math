import OAI.RepresentationTheory.VertexAlgebra.ModuleCurrentEnergy

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

namespace GradingRestrictedModule
variable (M : A.GradingRestrictedModule W)
 

def linearCurrentBoundSubmodule : Submodule ℂ V where
  carrier := {a | ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (x : W),
    ‖M.physicalMode a 1 m x‖ ≤ C*(1+|(m : ℝ)|)*‖M.energyShift x‖}
  zero_mem' := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro m x
    simp only [physicalMode, mode_zero, LinearMap.zero_apply, norm_zero]
    positivity
  add_mem' := by
    rintro a b ⟨C,hC,HC⟩ ⟨D,hD,HD⟩
    refine ⟨C+D,add_pos hC hD,?_⟩
    intro m x
    change ‖mode M.fields (a+b) (m+1-1) x‖ ≤ _
    rw [mode_add, LinearMap.add_apply]
    calc
      _ ≤ ‖M.physicalMode a 1 m x‖ + ‖M.physicalMode b 1 m x‖ := norm_add_le _ _
      _ ≤ C*(1+|(m : ℝ)|)*‖M.energyShift x‖ + D*(1+|(m : ℝ)|)*‖M.energyShift x‖ :=
        add_le_add (HC m x) (HD m x)
      _ = _ := by ring
  smul_mem' := by
    rintro z a ⟨C,hC,HC⟩
    refine ⟨(‖z‖+1)*C, by positivity, ?_⟩
    intro m x
    change ‖mode M.fields (z • a) (m+1-1) x‖ ≤ _
    rw [mode_smul, LinearMap.smul_apply, norm_smul]
    calc
      _ ≤ ‖z‖ * (C*(1+|(m : ℝ)|)*‖M.energyShift x‖) :=
        mul_le_mul_of_nonneg_left (HC m x) (norm_nonneg z)
      _ ≤ (‖z‖+1) * (C*(1+|(m : ℝ)|)*‖M.energyShift x‖) := by gcongr; linarith
      _ = _ := by ring

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

 

omit Q in
theorem weight_one_quasiPrimary (_unitaryStructure : M.UnitaryStructure U)
    {a : V} (ha : a ∈ A.grade 1) : A.IsQuasiPrimary a := by
  obtain ⟨q,hq,hqq,b,hb,he⟩ := U.quasiPrimary_decomposition (d := 0) ha
  rw [A.grade_zero] at hb
  obtain ⟨z,rfl⟩ := Submodule.mem_span_singleton.mp hb
  have hzero : A.virasoroMode (-1) A.vacuum = 0 := by
    change mode A.fields A.conformalVector 0 A.vacuum = 0
    rw [A.conformal_translation]
    change mode A.fields A.vacuum (-2) A.vacuum = 0
    rw [A.vacuum_mode]
    norm_num
  rw [map_smul, hzero, smul_zero, add_zero] at he
  simpa only [he] using hqq

 
theorem weight_one_linear_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (x : W),
      ‖M.physicalMode a 1 m x‖ ≤ C*(1+|(m : ℝ)|)*‖M.energyShift x‖ := by
  obtain ⟨S,hS,hspan⟩ := U.exists_hermitian_quasiPrimary_spanning 1
  have hle : Submodule.span ℂ (S : Set V) ≤ M.linearCurrentBoundSubmodule := by
    apply Submodule.span_le.mpr
    intro b hb
    obtain ⟨hbg,hbq,hbh⟩ := hS b hb
    exact Q.current_linear_energyBound hc hbg hbq hbh
  exact hle (hspan a ha (Q.weight_one_quasiPrimary ha))

 

theorem virasoro_linear_energyBound (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (x : W),
      ‖M.virasoroMode m x‖ ≤ C*(1+|(m : ℝ)|)^4*‖M.energyShift x‖ := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [CFTTypeVOA.UnitaryStructure.IsHermitian, U.pct_conformal]
  simpa only [physicalMode_conformal, show 2*2=4 by decide, show 2-1=1 by decide,
    pow_one] using Q.optimal_quasiPrimary_energyBound hc A.conformal_mem
      A.conformal_quasiPrimary hh (by decide)

 

theorem source_energy_theorem (_hSimple : A.toVertexAlgebra.IsSimple)
    (hSR : A.IsStronglyRational.{u,v}) : M.SourceEnergyConclusion U := by
  refine ⟨Q.polynomialEnergyBounds hSR.2.2, ?_, ?_, ?_⟩
  · intro d hd a ha hq hh
    obtain ⟨C,hC,HC⟩ := Q.optimal_quasiPrimary_energyBound hSR.2.2 ha hq hh hd
    exact ⟨C,hC,2*d, by simpa only [Int.cast_abs] using HC⟩
  · intro a ha
    obtain ⟨C,hC,HC⟩ := Q.weight_one_linear_energyBound hSR.2.2 ha
    exact ⟨C,hC,1, by simpa only [Int.cast_abs, pow_one] using HC⟩
  · obtain ⟨C,hC,HC⟩ := Q.virasoro_linear_energyBound hSR.2.2
    exact ⟨C,hC,4, by simpa only [Int.cast_abs] using HC⟩

end UnitaryStructure
end GradingRestrictedModule
end StronglyRationalVOA.CFTTypeVOA

end

end OAI
