import OAI.Topology.EilenbergGanea.Seed
import OAI.Topology.EilenbergGanea.SmallHolonomy

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Exact quaternion monodromy of the fixed presentation seed. -/
open scoped Quaternion
namespace EilenbergGanea

abbrev SeedSU2 := unitary ℍ

def seedGoldenReal : ℝ := (1 + Real.sqrt 5) / 4

def seedXQuaternion : ℍ := ⟨0,1,0,0⟩
def seedYQuaternion : ℍ :=
  ⟨seedGoldenReal,1/2,Real.sqrt ((3 - Real.sqrt 5)/8),0⟩

theorem seedGoldenReal_quadratic : 4 * seedGoldenReal ^ 2 - 2 * seedGoldenReal - 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [seedGoldenReal]
  nlinarith

theorem seedGoldenReal_cubic : 8 * seedGoldenReal ^ 3 - 4 * seedGoldenReal = 1 := by
  have h := seedGoldenReal_quadratic
  nlinarith [sq_nonneg (2 * seedGoldenReal - 1),
    mul_eq_zero_of_left h seedGoldenReal]

theorem seedGoldenReal_quartic : 16 * seedGoldenReal ^ 4 - 12 * seedGoldenReal ^ 2 + 1 = 0 := by
  have h := seedGoldenReal_quadratic
  have h' := seedGoldenReal_cubic
  nlinarith [mul_eq_zero_of_left h (seedGoldenReal ^ 2),
    congrArg (fun t : ℝ => t * seedGoldenReal) h']

theorem seedX_normSq : Quaternion.normSq seedXQuaternion = 1 := by
  rw [Quaternion.normSq_def']
  norm_num [seedXQuaternion]

theorem seedY_normSq : Quaternion.normSq seedYQuaternion = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hle : Real.sqrt (5 : ℝ) ≤ 3 := by nlinarith
  have hc := Real.sq_sqrt (show (0 : ℝ) ≤ (3 - Real.sqrt 5)/8 by positivity)
  rw [Quaternion.normSq_def']
  change seedGoldenReal ^ 2 + (1 / 2 : ℝ) ^ 2 + Real.sqrt ((3 - Real.sqrt 5)/8) ^ 2 + 0 ^ 2 = 1
  dsimp [seedGoldenReal]
  nlinarith

def seedXUnit : SeedSU2 := ⟨seedXQuaternion,by
  rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,seedX_normSq]
  simp⟩

def seedYUnit : SeedSU2 := ⟨seedYQuaternion,by
  rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,seedY_normSq]
  simp⟩

theorem unitQuaternion_quadratic (q : ℍ) (h : Quaternion.normSq q = 1) :
    q ^ 2 = (2 * q.re : ℝ) * q - 1 := by
  have hh := Quaternion.star_mul_self q
  rw [h,Quaternion.star_eq_two_re_sub,sub_mul] at hh
  simp only [Quaternion.coe_one] at hh
  have hh' : ((2 * q.re : ℝ) : ℍ) * q = 1 + q * q := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hh
  rw [pow_two]
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using hh'.symm

theorem unitQuaternion_half_cube (q : ℍ) (h : Quaternion.normSq q = 1)
    (hr : q.re = 1/2) : q ^ 3 = -1 := by
  have hh := unitQuaternion_quadratic q h
  rw [hr] at hh
  norm_num at hh
  calc
    q ^ 3 = q ^ 2 * q := by rw [pow_succ]
    _ = (q - 1) * q := by rw [hh]
    _ = q ^ 2 - q := by noncomm_ring
    _ = -1 := by rw [hh]; noncomm_ring

theorem seedX_square : seedXQuaternion ^ 2 = -1 := by
  rw [pow_two]
  apply Quaternion.ext
  · rw [Quaternion.re_mul]
    norm_num [seedXQuaternion]
  · rw [Quaternion.imI_mul]
    norm_num [seedXQuaternion]
  · rw [Quaternion.imJ_mul]
    norm_num [seedXQuaternion]
  · rw [Quaternion.imK_mul]
    norm_num [seedXQuaternion]

theorem seedY_fifth : seedYQuaternion ^ 5 = -1 := by
  let q := seedYQuaternion
  let c : ℍ := (seedGoldenReal : ℝ)
  have hh : q ^ 2 = 2 * c * q - 1 := by
    simpa only [q,c,seedYQuaternion,Quaternion.coe_mul, show ((2 : ℝ) : ℍ) = 2 from rfl] using unitQuaternion_quadratic seedYQuaternion seedY_normSq
  have h3 : q ^ 3 = (4 * c ^ 2 - 1) * q - 2 * c := by
    calc
      q ^ 3 = q ^ 2 * q := by rw [pow_succ]
      _ = (2 * c * q - 1) * q := by rw [hh]
      _ = 2 * c * q ^ 2 - q := by noncomm_ring
      _ = (4 * c ^ 2 - 1) * q - 2 * c := by rw [hh]; noncomm_ring
  have h4 : q ^ 4 = (8 * c ^ 3 - 4 * c) * q - (4 * c ^ 2 - 1) := by
    calc
      q ^ 4 = q ^ 3 * q := by rw [pow_succ]
      _ = ((4 * c ^ 2 - 1) * q - 2 * c) * q := by rw [h3]
      _ = (4 * c ^ 2 - 1) * q ^ 2 - 2 * c * q := by noncomm_ring
      _ = (8 * c ^ 3 - 4 * c) * q - (4 * c ^ 2 - 1) := by rw [hh]; noncomm_ring
  have h5 : q ^ 5 = (16 * c ^ 4 - 12 * c ^ 2 + 1) * q - (8 * c ^ 3 - 4 * c) := by
    calc
      q ^ 5 = q ^ 4 * q := by rw [pow_succ]
      _ = ((8 * c ^ 3 - 4 * c) * q - (4 * c ^ 2 - 1)) * q := by rw [h4]
      _ = (8 * c ^ 3 - 4 * c) * q ^ 2 - (4 * c ^ 2 - 1) * q := by noncomm_ring
      _ = _ := by rw [hh]; noncomm_ring
  have hc3 : 8 * c ^ 3 - 4 * c = 1 := by
    change (8 : ℍ) * (seedGoldenReal : ℍ) ^ 3 - 4 * (seedGoldenReal : ℍ) = 1
    have h := congrArg (fun r : ℝ => (r : ℍ)) seedGoldenReal_cubic
    simpa only [Quaternion.coe_sub,Quaternion.coe_mul,Quaternion.coe_pow,Quaternion.coe_one,
      show ((8 : ℝ) : ℍ) = 8 from rfl, show ((4 : ℝ) : ℍ) = 4 from rfl] using h
  have hc4 : 16 * c ^ 4 - 12 * c ^ 2 + 1 = 0 := by
    change (16 : ℍ) * (seedGoldenReal : ℍ) ^ 4 - 12 * (seedGoldenReal : ℍ) ^ 2 + 1 = 0
    have h := congrArg (fun r : ℝ => (r : ℍ)) seedGoldenReal_quartic
    simpa only [Quaternion.coe_sub,Quaternion.coe_mul,Quaternion.coe_pow,Quaternion.coe_add,
      Quaternion.coe_one,Quaternion.coe_zero, show ((16 : ℝ) : ℍ) = 16 from rfl,
      show ((12 : ℝ) : ℍ) = 12 from rfl] using h
  simpa [hc3,hc4] using h5

theorem seedXYinv_cube : (seedXQuaternion * star seedYQuaternion) ^ 3 = -1 := by
  apply unitQuaternion_half_cube
  · rw [map_mul,Quaternion.normSq_star,seedX_normSq,seedY_normSq,mul_one]
  · rw [Quaternion.re_mul]
    rw [Quaternion.imI_star]
    norm_num [seedXQuaternion,seedYQuaternion]

theorem seed_unit_relations :
    seedXUnit ^ 2 = seedYUnit ^ 5 ∧
    seedXUnit ^ 2 = (seedXUnit * seedYUnit⁻¹) ^ 3 := by
  constructor
  · apply Subtype.val_injective
    change seedXQuaternion ^ 2 = seedYQuaternion ^ 5
    rw [seedX_square,seedY_fifth]
  · apply Subtype.val_injective
    change seedXQuaternion ^ 2 = (seedXQuaternion * star seedYQuaternion) ^ 3
    rw [seedX_square,seedXYinv_cube]

def seedRelator : Bool → FreeGroup Bool
  | false => FreeGroup.of false ^ 2 * (FreeGroup.of true ^ 5)⁻¹
  | true => FreeGroup.of false ^ 2 * ((FreeGroup.of false * (FreeGroup.of true)⁻¹) ^ 3)⁻¹

theorem seedWord_relator (r : Bool) : FreeGroup.mk (seedWord r) = seedRelator r := by
  cases r <;> decide

def seedLetterUnit : Bool → SeedSU2
  | false => seedXUnit
  | true => seedYUnit

theorem seedRelator_unit (r : Bool) : FreeGroup.lift seedLetterUnit (seedRelator r) = 1 := by
  cases r
  · simp only [seedRelator,map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,seedLetterUnit]
    rw [seed_unit_relations.1,mul_inv_cancel]
  · simp only [seedRelator,map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,seedLetterUnit]
    rw [seed_unit_relations.2,mul_inv_cancel]

abbrev SeedPresentationGroup := PresentedGroup (Set.range seedRelator)

def seedMonodromy : SeedPresentationGroup →* SeedSU2 :=
  PresentedGroup.toGroup (f := seedLetterUnit) (by
    rintro _ ⟨r,rfl⟩
    exact seedRelator_unit r)

theorem seedMonodromy_nontrivial : seedMonodromy (PresentedGroup.of false) ≠ 1 := by
  intro h
  have hh := congrArg (fun q : SeedSU2 => (q : ℍ).re) h
  simp [seedMonodromy,seedLetterUnit,seedXUnit,seedXQuaternion] at hh

/-- The source exponent-sum boundary, with rows indexed by its two relators. -/
def seedExponentMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2,-5;-1,3]

theorem seedExponentMatrix_det : seedExponentMatrix.det = 1 := by
  norm_num [seedExponentMatrix,Matrix.det_fin_two]

end EilenbergGanea



end

end OAI
