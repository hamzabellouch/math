import Mathlib

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 
def orbitMap (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : B →ₗ[ℂ] H where
  toFun b := (b : H →L[ℂ] H) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def orbit (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : Submodule ℂ H :=
  (orbitMap B x).range.topologicalClosure

instance orbit_isClosed (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    IsClosed (orbit B x : Set H) := Submodule.isClosed_topologicalClosure _

theorem self_mem_orbit (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : x ∈ orbit B x := by
  apply Submodule.le_topologicalClosure
  exact ⟨1, rfl⟩

theorem orbit_invariant (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H)
    (b : B) {y : H} (hy : y ∈ orbit B x) : (b : H →L[ℂ] H) y ∈ orbit B x := by
  have h : closure ((orbitMap B x).range : Set H) ⊆
      (b : H →L[ℂ] H) ⁻¹' (orbit B x : Set H) := by
    apply closure_minimal
    · rintro _ ⟨c, rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨b*c, rfl⟩
    · exact (orbit_isClosed B x).preimage (b : H →L[ℂ] H).continuous
  exact h hy

theorem projection_commutes_of_invariant (S : Submodule ℂ H) [IsClosed (S : Set H)]
    (D : H →L[ℂ] H) (hD : ∀ y ∈ S, D y ∈ S) (hDs : ∀ y ∈ S, D.adjoint y ∈ S) :
    Commute S.starProjection D := by
  apply ContinuousLinearMap.ext
  intro x
  change S.starProjection (D x) = D (S.starProjection x)
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hD _ (S.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact S.starProjection_inner_eq_zero x _ (hDs w hw)

theorem orbit_projection_mem_commutant (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) :
    (orbit B x).starProjection ∈ StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro b hb
  have hc (b : B) : Commute (orbit B x).starProjection (b : H →L[ℂ] H) :=
    projection_commutes_of_invariant _ _ (fun _ hy => orbit_invariant B x b hy)
      (fun _ hy => orbit_invariant B x (star b) hy)
  exact ⟨(hc ⟨b,hb⟩).eq.symm, (hc (star ⟨b,hb⟩)).eq.symm⟩

 
theorem bicommutant_mem_orbit (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) (x : H) :
    (D : H →L[ℂ] H) x ∈ orbit B x := by
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp D.property _
    (orbit_projection_mem_commutant B x)).1
  have hp : (orbit B x).starProjection x = x :=
    (orbit B x).starProjection_eq_self_iff.mpr (self_mem_orbit B x)
  have he := congrArg (fun Q : H →L[ℂ] H => Q x) hc
  change (orbit B x).starProjection ((D : H →L[ℂ] H) x) =
    (D : H →L[ℂ] H) ((orbit B x).starProjection x) at he
  rw [hp] at he
  exact (orbit B x).starProjection_eq_self_iff.mp he

 
theorem exists_approx_one (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)))
    (x : H) {ε : ℝ} (hε : 0 < ε) : ∃ b : B, ‖(b : H →L[ℂ] H) x - (D : H →L[ℂ] H) x‖ < ε := by
  have hm := bicommutant_mem_orbit B D x
  change (D : H →L[ℂ] H) x ∈ closure ((orbitMap B x).range : Set H) at hm
  obtain ⟨y, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp hm ε hε
  exact ⟨b, by simpa only [dist_eq_norm, orbitMap, LinearMap.coe_mk, AddHom.coe_mk,
    norm_sub_rev] using hb⟩
end StronglyRationalVOA.BicommutantDensity

end

end OAI
