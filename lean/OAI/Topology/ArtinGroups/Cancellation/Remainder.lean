import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.GaussianCancellation

variable {R : Type*} [Ring R]

def remainder (d h : R) : R := 1 - d * h - h * d

theorem remainder_commutes (d h : R) (hd : d * d = 0) :
    d * remainder d h = remainder d h * d := by
  simp only [remainder, mul_sub, sub_mul, mul_one, one_mul]
  simp only [← mul_assoc, hd, zero_mul]
  simp only [mul_assoc, hd, mul_zero, sub_zero]

theorem h_mul_remainder (d h : R) (hh : h * h = 0) (hhdh : h * d * h = h) :
    h * remainder d h = 0 := by
  simp only [remainder, mul_sub, mul_one, ← mul_assoc, hh, zero_mul, hhdh]
  abel

theorem remainder_mul_h (d h : R) (hh : h * h = 0) (hhdh : h * d * h = h) :
    remainder d h * h = 0 := by
  have hdsh : d * h * h = 0 := by rw [mul_assoc, hh, mul_zero]
  simp only [remainder, sub_mul, one_mul, hdsh, hhdh]
  abel

theorem remainder_idempotent (d h : R) (hd : d * d = 0)
    (hh : h * h = 0) (hhdh : h * d * h = h) :
    remainder d h * remainder d h = remainder d h := by
  calc
    remainder d h * remainder d h =
        remainder d h - d * (h * remainder d h) - h * (d * remainder d h) := by
      conv_lhs => lhs; unfold remainder
      noncomm_ring
    _ = remainder d h := by
      rw [h_mul_remainder d h hh hhdh, mul_zero, sub_zero,
        remainder_commutes d h hd, ← mul_assoc,
        h_mul_remainder d h hh hhdh, zero_mul, sub_zero]

theorem remainder_homotopy (d h : R) :
    1 - remainder d h = d * h + h * d := by
  unfold remainder
  abel

section Linear

variable {K V A B : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

def pivotHomotopy (ι : A →ₗ[K] V) (π : V →ₗ[K] B) (e : A ≃ₗ[K] B) :
    Module.End K V := ι.comp (e.symm.toLinearMap.comp π)

theorem pivotHomotopy_square (ι : A →ₗ[K] V) (π : V →ₗ[K] B)
    (e : A ≃ₗ[K] B) (hπι : π.comp ι = 0) :
    pivotHomotopy ι π e * pivotHomotopy ι π e = 0 := by
  apply LinearMap.ext
  intro x
  have hz : π (ι (e.symm (π x))) = 0 := LinearMap.congr_fun hπι _
  change ι (e.symm (π (ι (e.symm (π x))))) = 0
  rw [hz, map_zero, map_zero]

theorem pivotHomotopy_retract (d : Module.End K V)
    (ι : A →ₗ[K] V) (π : V →ₗ[K] B) (e : A ≃ₗ[K] B)
    (hpivot : π.comp (d.comp ι) = e.toLinearMap) :
    pivotHomotopy ι π e * d * pivotHomotopy ι π e = pivotHomotopy ι π e := by
  apply LinearMap.ext
  intro x
  have he : π (d (ι (e.symm (π x)))) = e (e.symm (π x)) :=
    LinearMap.congr_fun hpivot _
  change ι (e.symm (π (d (ι (e.symm (π x)))))) = ι (e.symm (π x))
  rw [he, e.apply_symm_apply]

abbrev Reduced (d h : Module.End K V) := LinearMap.range (remainder d h)

variable (d h : Module.End K V) (hd : d * d = 0)
  (hh : h * h = 0) (hhdh : h * d * h = h)

def reducedDifferential : Module.End K (Reduced d h) :=
  d.restrict (fun _ hx => by
    obtain ⟨x, rfl⟩ := hx
    refine ⟨d x, ?_⟩
    exact (LinearMap.congr_fun (remainder_commutes d h hd) x).symm)

theorem reducedDifferential_square :
    reducedDifferential d h hd * reducedDifferential d h hd = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun hd x

def projectReduced : V →ₗ[K] Reduced d h := (remainder d h).rangeRestrict

theorem projection_inclusion (hd : d * d = 0) (hh : h * h = 0)
    (hhdh : h * d * h = h) :
    (projectReduced d h).comp (Reduced d h).subtype = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨_, x, rfl⟩
  apply Subtype.ext
  exact LinearMap.congr_fun (remainder_idempotent d h hd hh hhdh) x

theorem inclusion_projection :
    (Reduced d h).subtype.comp (projectReduced d h) = remainder d h := rfl

theorem inclusion_chainMap :
    (Reduced d h).subtype.comp (reducedDifferential d h hd) =
      d.comp (Reduced d h).subtype := rfl

theorem projection_chainMap :
    (projectReduced d h).comp d =
      (reducedDifferential d h hd).comp (projectReduced d h) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (LinearMap.congr_fun (remainder_commutes d h hd) x).symm

end Linear
end HarmonicArtin.GaussianCancellation

end OAI
