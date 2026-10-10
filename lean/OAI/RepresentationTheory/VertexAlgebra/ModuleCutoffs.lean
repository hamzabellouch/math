import OAI.RepresentationTheory.VertexAlgebra.ModuleSpectralNorms

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

 
def energyCutoff (t : EnergyBand) (N : ℕ) : Submodule ℂ W :=
  ⨆ h : Fin (N+1), M.bandGrade t h
instance energyCutoff_finite (t : EnergyBand) (N : ℕ) :
    FiniteDimensional ℂ (M.energyCutoff t N) := by
  unfold energyCutoff
  infer_instance

theorem grade_le_energyCutoff (t : EnergyBand) {h N : ℕ} (hh : h ≤ N) :
    M.bandGrade t h ≤ M.energyCutoff t N := by
  exact le_iSup (fun k : Fin (N+1) => M.bandGrade t k) ⟨h, by omega⟩

theorem energyCutoff_mono (t : EnergyBand) : Monotone (M.energyCutoff t) := by
  intro N K hNK
  apply iSup_le
  intro h
  exact M.grade_le_energyCutoff t (by omega)

def bandComponent (t : EnergyBand) (h : ℕ) : Module.End ℂ W :=
  M.gradeComponent ((t.val:ℂ)+h)
theorem bandComponent_mem (t : EnergyBand) (h : ℕ) (x : W) :
    M.bandComponent t h x ∈ M.bandGrade t h := M.gradeComponent_mem _ _

def cutoffProjection (t : EnergyBand) (N : ℕ) : Module.End ℂ W :=
  ∑ h ∈ Finset.range (N+1), M.bandComponent t h

theorem cutoffProjection_apply (t : EnergyBand) (N : ℕ) (x : W) :
    M.cutoffProjection t N x=∑ h ∈ Finset.range (N+1), M.bandComponent t h x := by
  simp [cutoffProjection]

theorem cutoffProjection_on_grade (t : EnergyBand) {h N : ℕ} {x : W}
    (hh : h ≤ N) (hx : x ∈ M.bandGrade t h) : M.cutoffProjection t N x=x := by
  classical
  rw [M.cutoffProjection_apply]
  rw [Finset.sum_eq_single h]
  · exact M.gradeComponent_of_mem hx
  · intro k _ hkh
    apply M.gradeComponent_of_mem_ne _ hx
    intro he
    have hc : (h:ℂ)=(k:ℂ) := add_left_cancel he
    exact hkh (by exact_mod_cast hc.symm)
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

theorem cutoffProjection_of_mem (t : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff t N) : M.cutoffProjection t N x=x := by
  have H : M.energyCutoff t N ≤ LinearMap.ker (M.cutoffProjection t N-LinearMap.id) := by
    apply iSup_le
    intro h y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact M.cutoffProjection_on_grade t (by omega) hy
  have h := H hx
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using h

theorem cutoffProjection_mem (t : EnergyBand) (N : ℕ) (x : W) :
    M.cutoffProjection t N x ∈ M.energyCutoff t N := by
  rw [M.cutoffProjection_apply]
  apply Submodule.sum_mem
  intro h hh
  exact M.grade_le_energyCutoff t (by simpa using hh) (M.bandComponent_mem t h x)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

theorem band_orthogonalFamily (t : EnergyBand) :
    OrthogonalFamily ℂ (fun h => M.bandGrade t h) (fun h => (M.bandGrade t h).subtypeₗᵢ) := by
  intro h k hhk x y
  apply Q.grades_orthogonal _ x.property y.property
  intro he
  have hc : (h:ℂ)=(k:ℂ) := add_left_cancel he
  exact hhk (by exact_mod_cast hc)

theorem norm_sq_eq_sum_cutoff (t : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff t N) :
    ‖x‖^2=∑ h ∈ Finset.range (N+1), ‖M.bandComponent t h x‖^2 := by
  have H := (Q.band_orthogonalFamily t).norm_sum
    (fun h => ⟨M.bandComponent t h x, M.bandComponent_mem t h x⟩) (Finset.range (N+1))
  change ‖∑ h ∈ Finset.range (N+1), M.bandComponent t h x‖^2=_ at H
  rw [← M.cutoffProjection_apply, M.cutoffProjection_of_mem t hx] at H
  exact H

theorem energy_norm_sq_eq_sum_cutoff (t : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff t N) (r : ℕ) :
    ‖(M.energyShift^r) x‖^2=
      ∑ h ∈ Finset.range (N+1), ((1+t.val+h)^r*‖M.bandComponent t h x‖)^2 := by
  have H := (Q.band_orthogonalFamily t).norm_sum
    (fun h => ⟨(M.energyShift^r) (M.bandComponent t h x), by
      rw [M.energyShift_pow_on_band t (M.bandComponent_mem t h x)]
      exact (M.bandGrade t h).smul_mem _ (M.bandComponent_mem t h x)⟩)
    (Finset.range (N+1))
  change ‖∑ h ∈ Finset.range (N+1), (M.energyShift^r) (M.bandComponent t h x)‖^2=
    ∑ h ∈ Finset.range (N+1), ‖(M.energyShift^r) (M.bandComponent t h x)‖^2 at H
  rw [← map_sum, ← M.cutoffProjection_apply, M.cutoffProjection_of_mem t hx] at H
  simpa only [Q.energyShift_pow_norm_on_grade (M.bandComponent_mem t _ _),
    Complex.add_re, Complex.ofReal_re, Complex.natCast_re, add_assoc] using H

theorem energyShift_pow_norm_on_cutoff (t : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff t N) (r : ℕ) :
    ‖(M.energyShift^r) x‖ ≤ (2*(1+(N:ℝ)))^r*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [Q.energy_norm_sq_eq_sum_cutoff t hx, mul_pow, Q.norm_sq_eq_sum_cutoff t hx, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hhN : (h:ℝ) ≤ N := by exact_mod_cast (by simpa using hh : h ≤ N)
  have ht := t.property.1
  have ht' := t.property.2
  rw [mul_pow]
  gcongr
  linarith [Nat.cast_nonneg (α:=ℝ) N]

theorem mode_norm_sq_eq_sum_cutoff (t : EnergyBand) {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) (n : ℤ) {x : W} (hx : x ∈ M.energyCutoff t N) :
    ‖mode M.fields a n x‖^2=
      ∑ h ∈ Finset.range (N+1), ‖mode M.fields a n (M.bandComponent t h x)‖^2 := by
  classical
  let f := fun h => mode M.fields a n (M.bandComponent t h x)
  have hsum : ∑ h ∈ Finset.range (N+1), f h=mode M.fields a n x := by
    dsimp only [f]
    rw [← map_sum, ← M.cutoffProjection_apply, M.cutoffProjection_of_mem t hx]
  have H : inner ℂ (∑ h ∈ Finset.range (N+1), f h) (∑ h ∈ Finset.range (N+1), f h)=
      ∑ h ∈ Finset.range (N+1), inner ℂ (f h) (f h) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro h hh
    rw [inner_sum]
    apply Finset.sum_eq_single h
    · intro k _ hkh
      apply Q.mode_images_orthogonal ha (M.bandComponent_mem t h x) (M.bandComponent_mem t k x) _ n
      intro he
      exact hkh (by exact_mod_cast (add_left_cancel he).symm)
    · exact fun hn => (hn hh).elim
  rw [hsum] at H
  simp only [inner_self_eq_norm_sq_to_K] at H
  exact_mod_cast H

theorem physicalMode_zero_above_cutoff (t : EnergyBand) {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) {x : W} (hx : x ∈ M.energyCutoff t N)
    (m : ℤ) (hm : (N:ℤ) < m) : M.physicalMode a d m x=0 := by
  rw [← M.cutoffProjection_of_mem t hx, M.cutoffProjection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro h hh
  exact Q.physicalMode_eq_zero_above_band t ha (M.bandComponent_mem t h x) m
    (by have hh := Finset.mem_range.mp hh; omega)

theorem physicalMode_mem_cutoff (t : EnergyBand) {a : V} {d N K : ℕ}
    (ha : a ∈ A.grade d) {x : W} (hx : x ∈ M.energyCutoff t N)
    (m : ℤ) (hm : (N:ℤ)-m ≤ K) : M.physicalMode a d m x ∈ M.energyCutoff t K := by
  rw [← M.cutoffProjection_of_mem t hx, M.cutoffProjection_apply, map_sum]
  apply Submodule.sum_mem
  intro h hh
  by_cases hm' : (h:ℤ) < m
  · rw [Q.physicalMode_eq_zero_above_band t ha (M.bandComponent_mem t h x) m hm']
    exact Submodule.zero_mem _
  · apply M.grade_le_energyCutoff t (h := ((h:ℤ)-m).toNat)
      (by have hh := Finset.mem_range.mp hh; omega)
    exact M.physicalMode_mem_band t ha (M.bandComponent_mem t h x) m (by omega)

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
