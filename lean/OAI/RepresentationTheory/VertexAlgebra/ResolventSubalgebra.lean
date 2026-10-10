import OAI.RepresentationTheory.VertexAlgebra.SelfAdjointResolvent

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
universe u v

 

theorem map_ringInverse_of_isUnit {A : Type u} {B : Type v} [Ring A] [Ring B]
    (f : A →+* B) {a : A} (ha : IsUnit a) : f (Ring.inverse a) = Ring.inverse (f a) := by
  apply left_inv_eq_right_inv
  · rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  · exact Ring.mul_inverse_cancel _ (ha.map f)

theorem map_resolvent_of_mem {A : Type u} {B : Type v} [Ring A] [Ring B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {a : A} {z : ℂ}
    (ha : z ∈ resolventSet ℂ a) : f (resolvent a z) = resolvent (f a) z := by
  change f (Ring.inverse (algebraMap ℂ A z - a)) = _
  have he : f (Ring.inverse (algebraMap ℂ A z - a)) =
      Ring.inverse (f (algebraMap ℂ A z - a)) :=
    map_ringInverse_of_isUnit f.toRingHom (spectrum.mem_resolventSet_iff.mp ha)
  rw [he, map_sub, AlgHom.commutes]
  rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coe_resolvent_imaginary (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    (b : B) (hb : IsSelfAdjoint (b : H →L[ℂ] H)) :
    ((resolvent b Complex.I : B) : H →L[ℂ] H) = resolvent (b : H →L[ℂ] H) Complex.I := by
  have hr : Complex.I ∈ resolventSet ℂ b := by
    rw [spectrum.mem_resolventSet_iff]
    apply (StarSubalgebra.coe_isUnit B).mp
    exact spectrum.mem_resolventSet_iff.mp (imaginary_mem_resolvent hb)
  exact map_resolvent_of_mem B.subtype.toAlgHom hr
end StronglyRationalVOA.BicommutantDensity

end

end OAI
