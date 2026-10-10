import OAI.RepresentationTheory.VertexAlgebra.ModuleModeAlgebra

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {A : CFTTypeVOA V} {W : Type v} [AddCommGroup W] [Module ℂ W]
  (M : A.GradingRestrictedModule W)

@[simp]
theorem gradeComponent_apply (d : ℂ) (a : W) :
    M.gradeComponent d a = (M.gradingEquiv a d : W) := rfl

theorem gradeComponent_mem (d : ℂ) (a : W) : M.gradeComponent d a ∈ M.grade d :=
  (M.gradingEquiv a d).property

theorem gradeComponent_of_mem {d : ℂ} {a : W} (ha : a ∈ M.grade d) :
    M.gradeComponent d a = a := by
  exact congrArg Subtype.val (M.grading_internal.ofBijective_coeLinearMap_of_mem ha)

theorem gradeComponent_of_mem_ne {d e : ℂ} (hde : e ≠ d) {a : W}
    (ha : a ∈ M.grade e) : M.gradeComponent d a = 0 := by
  exact congrArg Subtype.val
    (M.grading_internal.ofBijective_coeLinearMap_of_mem_ne hde ha)

 
def gradeSupport (a : W) : Finset ℂ := by
  classical
  exact (M.gradingEquiv a).support

 
theorem sum_gradeComponents (a : W) :
    ∑ d ∈ M.gradeSupport a, M.gradeComponent d a = a := by
  classical
  change ∑ d ∈ (M.gradingEquiv a).support, M.gradeComponent d a = a
  calc
    _ = DirectSum.coeLinearMap M.grade
        (∑ d ∈ (M.gradingEquiv a).support,
          DirectSum.of (fun d => M.grade d) d (M.gradingEquiv a d)) := by
      simp only [map_sum, DirectSum.coeLinearMap_of, gradeComponent_apply]
    _ = DirectSum.coeLinearMap M.grade (M.gradingEquiv a) := by
      rw [DirectSum.sum_support_of]
    _ = a := (LinearEquiv.ofBijective (DirectSum.coeLinearMap M.grade)
      M.grading_internal).apply_symm_apply a

 

theorem homogeneous_induction {P : W → Prop} (h0 : P 0)
    (hh : ∀ d : ℂ, ∀ a ∈ M.grade d, P a)
    (hadd : ∀ a b : W, P a → P b → P (a + b)) (a : W) : P a := by
  let : DirectSum.Decomposition M.grade := M.grading_internal.chooseDecomposition
  exact DirectSum.Decomposition.inductionOn M.grade h0
    (fun {d} x => hh d x x.property) hadd a

theorem virasoro_zero_on_grade {z : ℂ} {x : W} (hx : x ∈ M.grade z) :
    M.virasoroMode 0 x = z • x := M.conformal_energy z x hx

 
theorem gradeComponent_energy (d : ℂ) (a : W) :
    M.gradeComponent d (M.virasoroMode 0 a) = (d : ℂ) • M.gradeComponent d a := by
  apply M.homogeneous_induction (P := fun a =>
    M.gradeComponent d (M.virasoroMode 0 a) = (d : ℂ) • M.gradeComponent d a)
  · simp
  · intro e b hb
    rw [M.virasoro_zero_on_grade hb, map_smul]
    by_cases he : e = d
    · subst e
      rfl
    · rw [M.gradeComponent_of_mem_ne he hb]
      simp
  · intro b c hb hc
    simp only [map_add, smul_add, hb, hc]

 
theorem gradeComponent_eigenvalue {a : W} {z : ℂ}
    (ha : M.virasoroMode 0 a = z • a) (d : ℂ) (hd : (d : ℂ) ≠ z) :
    M.gradeComponent d a = 0 := by
  have h := congrArg (M.gradeComponent d) ha
  rw [M.gradeComponent_energy, map_smul] at h
  have h' : ((d : ℂ) - z) • M.gradeComponent d a = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hd)

 
theorem mem_grade_of_energy {d : ℂ} {a : W}
    (ha : M.virasoroMode 0 a = (d : ℂ) • a) : a ∈ M.grade d := by
  classical
  rw [← M.sum_gradeComponents a]
  apply Submodule.sum_mem
  intro e _
  by_cases he : e = d
  · subst e
    exact M.gradeComponent_mem d a
  · rw [M.gradeComponent_eigenvalue ha e (by exact_mod_cast he)]
    exact (M.grade d).zero_mem

 
theorem energy_mode_commutator {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    (n : ℤ) (x : W) :
    M.virasoroMode 0 (mode M.fields a n x) -
      mode M.fields a n (M.virasoroMode 0 x) =
        ((d : ℂ)-n-1) • mode M.fields a n x := by
  have h := M.toWeakModule.mode_commutator_nat A.conformalVector a x 1 n
  have h0 : mode A.fields A.conformalVector 0 a=A.toVertexAlgebra.translation a := by
    rw [A.conformal_translation]
  have h1 : mode A.fields A.conformalVector 1 a=(d : ℂ) • a := A.conformal_energy d a ha
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, Nat.choose_zero_right, Nat.choose_self,
    one_smul, Int.sub_zero, h0, h1, mode_smul, LinearMap.smul_apply] at h
  rw [M.toWeakModule.translation_covariance] at h
  simp only [LinearMap.smul_apply, show 1+n-1=n by omega] at h
  change mode M.fields A.conformalVector 1 (mode M.fields a n x)-
    mode M.fields a n (mode M.fields A.conformalVector 1 x)=_
  rw [h, ← add_smul]
  congr 1
  push_cast
  ring

theorem mode_mem_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    {z : ℂ} {x : W} (hx : x ∈ M.grade z) (n : ℤ) :
    mode M.fields a n x ∈ M.grade (z+d-n-1) := by
  apply M.mem_grade_of_energy
  have h := M.energy_mode_commutator ha n x
  rw [M.virasoro_zero_on_grade hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← add_smul]
  congr 1
  ring

theorem physicalMode_mem_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    {z : ℂ} {x : W} (hx : x ∈ M.grade z) (m : ℤ) :
    M.physicalMode a d m x ∈ M.grade (z-m) := by
  have h := M.mode_mem_grade ha hx (m+d-1)
  have he : z+(d : ℂ)-((m+(d : ℤ)-1 : ℤ) : ℂ)-1=z-m := by push_cast; ring
  rw [he] at h
  exact h

@[simp] theorem physicalMode_conformal (m : ℤ) :
    M.physicalMode A.conformalVector 2 m=M.virasoroMode m := by
  unfold physicalMode virasoroMode
  congr 1
  omega

theorem virasoro_mem_grade {z : ℂ} {x : W} (hx : x ∈ M.grade z) (m : ℤ) :
    M.virasoroMode m x ∈ M.grade (z-m) := by
  simpa using M.physicalMode_mem_grade A.conformal_mem hx m

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
