import OAI.RepresentationTheory.VertexAlgebra.ModulePositiveEnergy

namespace OAI

noncomputable section
universe u v
namespace StronglyRationalVOA
 

abbrev EnergyBand := {t : ℝ // 0 ≤ t ∧ t < 1}
namespace CFTTypeVOA.GradingRestrictedModule
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {A : CFTTypeVOA V} {W : Type v} [AddCommGroup W] [Module ℂ W]
  (M : A.GradingRestrictedModule W)
def bandGrade (t : EnergyBand) (h : ℕ) : Submodule ℂ W := M.grade ((t.val:ℂ)+h)
instance bandGradeFinite (t : EnergyBand) (h : ℕ) : FiniteDimensional ℂ (M.bandGrade t h) :=
  M.grade_finite _
theorem mode_mem_band {d h k : ℕ} {a : V} {x : W} (t : EnergyBand)
    (ha : a ∈ A.grade d) (hx : x ∈ M.bandGrade t h) (n : ℤ)
    (hk : (k:ℤ) = d+h-n-1) : mode M.fields a n x ∈ M.bandGrade t k := by
  have H := M.mode_mem_grade ha hx n
  have he : (t.val:ℂ)+h+d-n-1=(t.val:ℂ)+k := by
    have he' : (k:ℂ)=(d:ℂ)+h-n-1 := by exact_mod_cast hk
    rw [he']; ring
  change _ ∈ M.grade _ at H ⊢
  rwa [he] at H

theorem physicalMode_mem_band {d h k : ℕ} {a : V} {x : W} (t : EnergyBand)
    (ha : a ∈ A.grade d) (hx : x ∈ M.bandGrade t h) (m : ℤ)
    (hk : (k:ℤ) = h-m) : M.physicalMode a d m x ∈ M.bandGrade t k :=
  M.mode_mem_band t ha hx _ (by omega)

theorem virasoro_mem_band {h k : ℕ} {x : W} (t : EnergyBand)
    (hx : x ∈ M.bandGrade t h) (m : ℤ) (hk : (k:ℤ)=h-m) :
    M.virasoroMode m x ∈ M.bandGrade t k := by
  simpa using M.physicalMode_mem_band t A.conformal_mem hx m hk

theorem energyShift_on_band {h : ℕ} {x : W} (t : EnergyBand) (hx : x ∈ M.bandGrade t h) :
    M.energyShift x = (1+(t.val:ℂ)+h) • x := by
  change x+M.virasoroMode 0 x=_
  rw [M.virasoro_zero_on_grade hx]
  module

theorem energyShift_pow_on_band {h : ℕ} {x : W} (t : EnergyBand)
    (hx : x ∈ M.bandGrade t h) (k : ℕ) :
    (M.energyShift^k) x=(1+(t.val:ℂ)+h)^k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, M.energyShift_on_band t hx,
      smul_smul, ← pow_succ]

 
theorem physical_normal_product_resplit (a b : V) (c : W) (d e : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    M.physicalMode (mode A.fields a (-1) b) (d+e) m c =
      (∑ᶠ j : ℕ, M.physicalMode a d (-1-j) (M.physicalMode b e (m+1+j) c)) +
      (∑ᶠ j : ℕ, M.physicalMode b e (m-j) (M.physicalMode a d j c)) -
      ∑ i ∈ Finset.range (d-1), ∑ j ∈ Finset.range (i+1),
        (i.choose j:ℂ) • mode M.fields (mode A.fields a j b) (m+d+e-2-j) c := by
  have h := M.toWeakModule.mode_normal_product_resplit a b c (m+d+e-1) (d-1)
  simp only [Nat.cast_sub hd, Nat.cast_one] at h
  simp_rw [M.toWeakModule.mode_commutator_nat] at h
  have E₁ (j : ℕ) : (d : ℤ) - 1 - 1 - j = -1 - j + d - 1 := by omega
  have E₂ (j : ℕ) : m + d + e - 1 - ((d : ℤ) - 1) + j = m + 1 + j + e - 1 := by omega
  have E₃ (j : ℕ) : m + d + e - 1 - 1 - ((d : ℤ) - 1) - j = m - j + e - 1 := by omega
  have E₄ (j : ℕ) : (d : ℤ) - 1 + j = (j : ℤ) + d - 1 := by omega
  have E₅ (i j : ℕ) : (i : ℤ) + (m + d + e - 1 - 1 - i) - j = m + d + e - 2 - j := by omega
  simp_rw [E₁, E₂, E₃, E₄, E₅] at h
  simpa only [physicalMode, Nat.cast_add, ← add_assoc] using h
end CFTTypeVOA.GradingRestrictedModule
namespace CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)
include R

theorem physicalMode_eq_zero_above_band {d h : ℕ} {a : V} {x : W} (t : EnergyBand)
    (ha : a ∈ A.grade d) (hx : x ∈ M.bandGrade t h) (m : ℤ) (hm : (h : ℤ) < m) :
    M.physicalMode a d m x=0 := by
  apply R.physicalMode_eq_zero_of_negative ha hx m
  simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
  have hi : (h:ℝ)+1 ≤ m := by exact_mod_cast hm
  linarith [t.property.2]

theorem physical_normal_product_on_band {a b : V} {c : W} {d e h : ℕ} (t : EnergyBand)
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hc : c ∈ M.bandGrade t h)
    (hd : 1 ≤ d) (k : ℕ) :
    M.physicalMode (mode A.fields a (-1) b) (d+e) ((h:ℤ)-k) c =
      (∑ j ∈ Finset.range k, M.physicalMode a d (-1-j)
        (M.physicalMode b e ((h:ℤ)-k+1+j) c)) +
      (∑ j ∈ Finset.range (h+1), M.physicalMode b e ((h:ℤ)-k-j)
        (M.physicalMode a d j c)) -
      ∑ i ∈ Finset.range (d-1), ∑ j ∈ Finset.range (i+1),
        (i.choose j:ℂ) • mode M.fields (mode A.fields a j b)
          ((h:ℤ)-k+d+e-2-j) c := by
  classical
  rw [M.physical_normal_product_resplit a b c d e hd ((h:ℤ)-k)]
  have hL : Function.support (fun j : ℕ => M.physicalMode a d (-1-j)
      (M.physicalMode b e ((h:ℤ)-k+1+j) c)) ⊆ (Finset.range k : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra he
    apply hj
    dsimp only
    rw [R.physicalMode_eq_zero_above_band t hb hc ((h:ℤ)-k+1+j) (by omega), map_zero]
  have hR : Function.support (fun j : ℕ => M.physicalMode b e ((h:ℤ)-k-j)
      (M.physicalMode a d j c)) ⊆ (Finset.range (h+1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra he
    apply hj
    dsimp only
    rw [R.physicalMode_eq_zero_above_band t ha hc j (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hR]
end CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
end StronglyRationalVOA

end

end OAI
