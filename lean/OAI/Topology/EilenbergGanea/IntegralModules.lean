import OAI.Topology.EilenbergGanea.Model
import OAI.Topology.EilenbergGanea.PresentationAlignment
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Noetherian.Basic

namespace OAI

noncomputable section

open Classical Set

/-! Group-ring augmentation and literal two-syzygy dimension criterion. -/
namespace EilenbergGanea
open CategoryTheory

section ProjectiveBound
variable {R P Q M : Type} [Ring R]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup M] [Module R M]

/-- Two successive projective syzygies give the literal integral upper bound. -/
theorem projectiveDimension_le_two_of_syzygies
    (ε : P →ₗ[R] M) (hε : Function.Surjective ε)
    (d : Q →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    [Module.Projective R P] [Module.Projective R Q]
    [Module.Projective R (LinearMap.ker d)] :
    CategoryTheory.projectiveDimension (ModuleCat.of R M) ≤ 2 := by
  have h₁ := (LinearMap.shortExact_shortComplexKer hd).hasProjectiveDimensionLT_X₃ 1
    (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker d)) 1)
    (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R Q) 2)
  have h₂ := (LinearMap.shortExact_shortComplexKer hε).hasProjectiveDimensionLT_X₃ 2
    h₁ (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R P) 3)
  exact (CategoryTheory.projectiveDimension_le_iff _ 2).mpr h₂
end ProjectiveBound

section CayleyModules
variable {Γ S : Type} [Group Γ]

abbrev IntegralGroupRing (Γ : Type) [Group Γ] := MonoidAlgebra ℤ Γ
abbrev IntegralTrivialModule (Γ : Type) [Group Γ] :=
  (Representation.trivial ℤ Γ ℤ).asModule

def cayleyAugmentation : IntegralGroupRing Γ →ₗ[IntegralGroupRing Γ] IntegralTrivialModule Γ :=
  LinearMap.toSpanSingleton (IntegralGroupRing Γ) _
    ((Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1)

@[simp] theorem cayleyAugmentation_single (g : Γ) (n : ℤ) :
    cayleyAugmentation (MonoidAlgebra.single g n) =
      (Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm n := by
  change (MonoidAlgebra.single g n : IntegralGroupRing Γ) •
    ((Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1) = _
  rw [Representation.single_smul]
  change (n : ℤ) * 1 = n
  exact mul_one n

theorem cayleyAugmentation_surjective :
    Function.Surjective (cayleyAugmentation (Γ := Γ)) := by
  intro n
  refine ⟨MonoidAlgebra.single (1 : Γ) ((Representation.trivial ℤ Γ ℤ).asModuleEquiv n),?_⟩
  rw [cayleyAugmentation_single,LinearEquiv.symm_apply_apply]

def cayleyDifferential (v : S → Γ) :
    (S →₀ IntegralGroupRing Γ) →ₗ[IntegralGroupRing Γ] IntegralGroupRing Γ :=
  Finsupp.linearCombination _ (fun s => MonoidAlgebra.single (v s) 1 - 1)

@[simp] theorem cayleyDifferential_single (v : S → Γ) (s : S) (r : IntegralGroupRing Γ) :
    cayleyDifferential v (Finsupp.single s r) = r * (MonoidAlgebra.single (v s) 1 - 1) := by
  simp [cayleyDifferential]

@[simp] theorem cayleyAugmentation_one :
    cayleyAugmentation (1 : IntegralGroupRing Γ) =
      (Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1 :=
  cayleyAugmentation_single (1 : Γ) 1

@[simp] theorem cayleyAugmentation_difference (g : Γ) :
    cayleyAugmentation (MonoidAlgebra.single g 1 - 1) = 0 := by
  rw [map_sub, cayleyAugmentation_single, cayleyAugmentation_one, sub_self]

theorem cayleyDifferential_aug (v : S → Γ) :
    (cayleyAugmentation (Γ := Γ)).comp (cayleyDifferential v) = 0 := by
  change (cayleyAugmentation (Γ := Γ)).comp
    (Finsupp.linearCombination _ (fun s => MonoidAlgebra.single (v s) 1 - 1)) = 0
  rw [← Finsupp.linearCombination_linear_comp]
  have he : (cayleyAugmentation (Γ := Γ)) ∘
      (fun s => MonoidAlgebra.single (v s) 1 - 1) = (0 : S → IntegralTrivialModule Γ) := by
    funext s
    exact cayleyAugmentation_difference (v s)
  rw [he, Finsupp.linearCombination_zero]

 theorem cayleyGeneratorDifference_mem (v : S → Γ) (w : FreeGroup S) :
    MonoidAlgebra.single (FreeGroup.lift v w) 1 - 1 ∈ LinearMap.range (cayleyDifferential v) := by
  induction w using FreeGroup.induction_on with
  | one =>
      simp only [map_one]
      have he : (MonoidAlgebra.single (1 : Γ) 1 : IntegralGroupRing Γ) = 1 := rfl
      rw [he,sub_self]
      exact Submodule.zero_mem _
  | of s =>
      exact ⟨Finsupp.single s 1,by simp⟩
  | inv_of s =>
      refine ⟨Finsupp.single s (-MonoidAlgebra.single (v s)⁻¹ 1),?_⟩
      simp [mul_sub,MonoidAlgebra.single_mul_single]
      rfl
  | mul w z hw hz =>
      have hh := (LinearMap.range (cayleyDifferential v)).smul_mem
        (MonoidAlgebra.single (FreeGroup.lift v w) 1) hz
      have hc := (LinearMap.range (cayleyDifferential v)).add_mem hw hh
      rw [map_mul]
      convert hc using 1
      change _ = (_ - 1) + _ * (_ - 1)
      rw [mul_sub,mul_one,MonoidAlgebra.single_mul_single,one_mul]
      abel

theorem cayleyAugmentation_normalize (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v)) (r : IntegralGroupRing Γ) :
    r - MonoidAlgebra.single 1
      ((Representation.trivial ℤ Γ ℤ).asModuleEquiv (cayleyAugmentation r)) ∈
        LinearMap.range (cayleyDifferential v) := by
  classical
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r t hr ht =>
      rw [map_add, map_add, MonoidAlgebra.single_add]
      convert (LinearMap.range (cayleyDifferential v)).add_mem hr ht using 1; abel
  | single g n =>
      rw [cayleyAugmentation_single, LinearEquiv.apply_symm_apply]
      obtain ⟨w, hw⟩ := hv g
      have hm := (LinearMap.range (cayleyDifferential v)).toAddSubgroup.zsmul_mem
        (cayleyGeneratorDifference_mem v w) n
      rw [hw] at hm
      convert hm using 1
      simp only [smul_sub, MonoidAlgebra.smul_single, zsmul_eq_mul, mul_one]
      rfl

theorem cayley_exact (v : S → Γ) (hv : Function.Surjective (FreeGroup.lift v)) :
    LinearMap.range (cayleyDifferential v) = LinearMap.ker (cayleyAugmentation (Γ := Γ)) := by
  apply le_antisymm
  · rintro _ ⟨r,rfl⟩
    exact LinearMap.congr_fun (cayleyDifferential_aug v) r
  · intro r hr
    have hm := cayleyAugmentation_normalize v hv r
    rw [LinearMap.mem_ker.mp hr, map_zero, MonoidAlgebra.single_zero, sub_zero] at hm
    exact hm

def cayleySyzygyDifferential (v : S → Γ) :
    (S →₀ IntegralGroupRing Γ) →ₗ[IntegralGroupRing Γ]
      LinearMap.ker (cayleyAugmentation (Γ := Γ)) :=
  (cayleyDifferential v).codRestrict _ (by
    intro r
    exact LinearMap.congr_fun (cayleyDifferential_aug v) r)

theorem cayleySyzygyDifferential_surjective (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v)) :
    Function.Surjective (cayleySyzygyDifferential v) := by
  intro r
  have hr : (r : IntegralGroupRing Γ) ∈ LinearMap.range (cayleyDifferential v) := by
    rw [cayley_exact v hv]
    exact r.property
  obtain ⟨s, hs⟩ := hr
  exact ⟨s, Subtype.ext hs⟩

theorem cayley_projectiveDimension_le_two (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v))
    [Module.Projective (IntegralGroupRing Γ) (LinearMap.ker (cayleyDifferential v))] :
    CategoryTheory.projectiveDimension
      (ModuleCat.of (IntegralGroupRing Γ) (IntegralTrivialModule Γ)) ≤ 2 := by
  have hk : LinearMap.ker (cayleySyzygyDifferential v) =
      LinearMap.ker (cayleyDifferential v) := LinearMap.ker_codRestrict _ _ _
  have : Module.Projective (IntegralGroupRing Γ)
      (LinearMap.ker (cayleySyzygyDifferential v)) := hk ▸ inferInstance
  exact projectiveDimension_le_two_of_syzygies cayleyAugmentation
    cayleyAugmentation_surjective (cayleySyzygyDifferential v)
    (cayleySyzygyDifferential_surjective v hv)

end CayleyModules
end EilenbergGanea

namespace EilenbergGanea
section ChainPackaging
variable {Γ S T : Type} [Group Γ]

/-- Reindex the actual integral edge chains as a free left group-ring module. -/
def chainPackaging : BasedChains Γ S ≃ₗ[ℤ] S →₀ IntegralGroupRing Γ :=
  ((Finsupp.domLCongr (Equiv.prodComm Γ S)).trans (Finsupp.curryLinearEquiv ℤ)).trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm)

@[simp] theorem chainPackaging_single (g : Γ) (s : S) (n : ℤ) :
    chainPackaging (Finsupp.single (g,s) n) =
      Finsupp.single s (MonoidAlgebra.single g n) := by
  simp [chainPackaging, Finsupp.curry_single]

@[simp] theorem chainPackaging_symm_single (g : Γ) (s : S) (n : ℤ) :
    (chainPackaging (Γ := Γ) (S := S)).symm
        (Finsupp.single s (MonoidAlgebra.single g n)) = Finsupp.single (g,s) n := by
  apply (chainPackaging (Γ := Γ) (S := S)).injective
  simp

theorem chainPackaging_translate (g : Γ) (c : BasedChains Γ S) :
    chainPackaging (translateChains g c) =
      (MonoidAlgebra.single g 1 : IntegralGroupRing Γ) • chainPackaging c := by
  have he : (chainPackaging (Γ := Γ) (S := S)).toLinearMap.comp (translateChains g) =
      (DistribSMul.toLinearMap ℤ (S →₀ IntegralGroupRing Γ) (MonoidAlgebra.single g 1 : IntegralGroupRing Γ)).comp
        (chainPackaging (Γ := Γ) (S := S)).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨h,s⟩ n
    simp [Finsupp.smul_single, MonoidAlgebra.single_mul_single]
  exact LinearMap.congr_fun he c

theorem chainPackaging_boundary (v : S → Γ) (c : BasedChains Γ S) :
    cayleyDifferential v (chainPackaging c) = MonoidAlgebra.ofCoeff (edgeBoundary v c) := by
  have he : ((cayleyDifferential v).restrictScalars ℤ).comp
      (chainPackaging (Γ := Γ) (S := S)).toLinearMap =
      (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (edgeBoundary v) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,s⟩ n
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      chainPackaging_single, cayleyDifferential_single, edgeBoundary_single, map_smul,
      map_sub]
    simp only [mul_sub, MonoidAlgebra.single_mul_single, mul_one,
      MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.ofCoeff_single,
      MonoidAlgebra.smul_single, smul_sub, smul_eq_mul]
  exact LinearMap.congr_fun he c

theorem chainPackaging_symm_translate (g : Γ) (c : S →₀ IntegralGroupRing Γ) :
    (chainPackaging (Γ := Γ) (S := S)).symm ((MonoidAlgebra.single g 1 : IntegralGroupRing Γ) • c) =
      translateChains g (chainPackaging.symm c) := by
  apply (chainPackaging (Γ := Γ) (S := S)).injective
  rw [chainPackaging_translate, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Equivariance on integral chains is exactly full group-ring linearity. -/
def chainRingMap (A : BasedChains Γ S →ₗ[ℤ] BasedChains Γ T)
    (hA : ChainsEquivariant A) :
    (S →₀ IntegralGroupRing Γ) →ₗ[IntegralGroupRing Γ] T →₀ IntegralGroupRing Γ where
  toFun c := chainPackaging (A (chainPackaging.symm c))
  map_add' _ _ := by simp only [map_add]
  map_smul' r c := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]
    | add r t hr ht => simp only [add_smul, map_add, hr, ht]
    | single g n =>
        have hn : (MonoidAlgebra.single g n : IntegralGroupRing Γ) =
            n • MonoidAlgebra.single g 1 := by simp
        rw [hn]
        simp only [smul_assoc, map_smul, chainPackaging_symm_translate, RingHom.id_apply]
        rw [hA g _, chainPackaging_translate]

@[simp] theorem chainRingMap_apply (A : BasedChains Γ S →ₗ[ℤ] BasedChains Γ T)
    (hA : ChainsEquivariant A) (c : S →₀ IntegralGroupRing Γ) :
    chainRingMap A hA c = chainPackaging (A (chainPackaging.symm c)) := rfl

theorem chainPackaging_mem_cycles (v : S → Γ) (c : BasedChains Γ S) :
    c ∈ cycles v ↔ chainPackaging c ∈ LinearMap.ker (cayleyDifferential v) := by
  change edgeBoundary v c = 0 ↔ cayleyDifferential v (chainPackaging c) = 0
  rw [chainPackaging_boundary]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    have hh := congrArg MonoidAlgebra.coeff h
    exact hh

theorem projective_cayley_cycles_of_boundary_basis (v : S → Γ)
    (A : BasedChains Γ T →ₗ[ℤ] BasedChains Γ S) (hA : ChainsEquivariant A)
    (hAi : Function.Injective A) (hAr : LinearMap.range A = cycles v) :
    Module.Projective (IntegralGroupRing Γ) (LinearMap.ker (cayleyDifferential v)) := by
  have hm : ∀ c, chainRingMap A hA c ∈ LinearMap.ker (cayleyDifferential v) := by
    intro c
    apply (chainPackaging_mem_cycles v _).mp
    rw [← hAr]
    exact ⟨chainPackaging.symm c,rfl⟩
  let d := (chainRingMap A hA).codRestrict _ hm
  have hi : Function.Injective d := by
    intro c c' h
    apply (chainPackaging (Γ := Γ) (S := T)).symm.injective
    apply hAi
    apply chainPackaging.injective
    exact congrArg Subtype.val h
  have hs : Function.Surjective d := by
    intro c
    have hc : chainPackaging.symm (c : S →₀ IntegralGroupRing Γ) ∈ cycles v := by
      apply (chainPackaging_mem_cycles v _).mpr
      rw [LinearEquiv.apply_symm_apply]
      exact c.property
    rw [← hAr] at hc
    obtain ⟨b,hb⟩ := hc
    refine ⟨chainPackaging b,Subtype.ext ?_⟩
    change chainPackaging (A (chainPackaging.symm (chainPackaging b))) = c.val
    rw [LinearEquiv.symm_apply_apply,hb,LinearEquiv.apply_symm_apply]
  exact Module.Projective.of_equiv' (LinearEquiv.ofBijective d ⟨hi,hs⟩)

theorem projectiveDimension_le_two_of_boundary_basis (v : S → Γ)
    (hv : Function.Surjective (FreeGroup.lift v))
    (A : BasedChains Γ T →ₗ[ℤ] BasedChains Γ S) (hA : ChainsEquivariant A)
    (hAi : Function.Injective A) (hAr : LinearMap.range A = cycles v) :
    CategoryTheory.projectiveDimension
      (ModuleCat.of (IntegralGroupRing Γ) (IntegralTrivialModule Γ)) ≤ 2 := by
  have := projective_cayley_cycles_of_boundary_basis v A hA hAi hAr
  exact cayley_projectiveDimension_le_two v hv

end ChainPackaging


end EilenbergGanea

end

end OAI
