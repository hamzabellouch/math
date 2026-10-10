import OAI.RepresentationTheory.VertexAlgebra.BicommutantSelfAdjoint
import OAI.RepresentationTheory.VertexAlgebra.ResolventSubalgebra
import OAI.RepresentationTheory.VertexAlgebra.ModuleIntegrationTarget

namespace OAI

noncomputable section
namespace StronglyRationalVOA
open Filter
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace LocalOperatorAlgebra
 theorem vonNeumann_isClosed (N : VonNeumannAlgebra H) : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  rw [← N.centralizer_centralizer]
  exact Set.isClosed_centralizer _

 theorem IsNormal.tendsto_net {N : VonNeumannAlgebra H}
    {π : N.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)} (hπ : IsNormal N π)
    {ι : Type w} {F : Filter ι} {a : ι → N.toStarSubalgebra} {D : N.toStarSubalgebra}
    (hb : ∃ C : ℝ, ∀ᶠ i in F, ‖(a i : H →L[ℂ] H)‖ ≤ C)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ x ((a i : H →L[ℂ] H) y)) F
      (nhds (inner ℂ x ((D : H →L[ℂ] H) y)))) (x y : K) :
    Tendsto (fun i => inner ℂ x (π (a i) y)) F (nhds (inner ℂ x (π D y))) := by
  apply Filter.tendsto_map'_iff.mp
  apply hπ (Filter.map a F) D
  · simpa only [Filter.eventually_map] using hb
  · intro x y
    exact Filter.tendsto_map'_iff.mpr (ht x y)

 theorem normal_eq_of_bounded_net {N : VonNeumannAlgebra H}
    {π ρ : N.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)}
    (hπ : IsNormal N π) (hρ : IsNormal N ρ)
    {ι : Type w} {F : Filter ι} [F.NeBot] {a : ι → N.toStarSubalgebra} {D : N.toStarSubalgebra}
    (hb : ∃ C : ℝ, ∀ᶠ i in F, ‖(a i : H →L[ℂ] H)‖ ≤ C)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ x ((a i : H →L[ℂ] H) y)) F
      (nhds (inner ℂ x ((D : H →L[ℂ] H) y))))
    (he : ∀ i, π (a i) = ρ (a i)) : π D = ρ D := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have hp := hπ.tendsto_net hb ht x y
  have hr := hρ.tendsto_net hb ht x y
  simp_rw [he] at hp
  exact tendsto_nhds_unique hp hr
end LocalOperatorAlgebra

namespace BicommutantDensity
open LocalOperatorAlgebra

 

theorem normal_eq_selfAdjoint (N : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    (hB : B ≤ N.toStarSubalgebra)
    (hgen : N.toStarSubalgebra ≤ Bicommutant B)
    (π ρ : N.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hπ : IsNormal N π) (hρ : IsNormal N ρ)
    (he : ∀ b : B, π ⟨b.val,hB b.property⟩ = ρ ⟨b.val,hB b.property⟩)
    (D : N.toStarSubalgebra) (hD : IsSelfAdjoint (D : H →L[ℂ] H)) : π D = ρ D := by
  classical
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumann_isClosed N
  obtain ⟨a,ha⟩ := exists_selfAdjoint_strong_net B ⟨D.val,hgen D.property⟩ hD
  let r : (ℕ × Finset H) → N.toStarSubalgebra := fun i =>
    ⟨((resolvent (a i).val Complex.I : B) : H →L[ℂ] H), hB (resolvent (a i).val Complex.I).property⟩
  have hsa (i : ℕ × Finset H) : IsSelfAdjoint ((a i).val : H →L[ℂ] H) :=
    (a i).property.map B.subtype
  have hrval (i : ℕ × Finset H) : (r i : H →L[ℂ] H) =
      resolvent ((a i).val : H →L[ℂ] H) Complex.I := coe_resolvent_imaginary B _ (hsa i)
  have hdval : ((resolvent D Complex.I : N.toStarSubalgebra) : H →L[ℂ] H) = resolvent D.val Complex.I :=
    coe_resolvent_imaginary N.toStarSubalgebra D hD
  have ht := resolvent_imaginary_tendsto hsa hD ha
  have her : π (resolvent D Complex.I) = ρ (resolvent D Complex.I) := by
    apply normal_eq_of_bounded_net hπ hρ (a := r) (F := atTop)
    · refine ⟨1, Filter.Eventually.of_forall (fun i => ?_)⟩
      rw [hrval]
      exact norm_resolvent_imaginary_le (hsa i)
    · intro x y
      simp_rw [hrval, hdval]
      exact (tendsto_const_nhds (x := x)).inner (ht y)
    · intro i
      exact he (resolvent (a i).val Complex.I)
  have hunit : IsUnit (algebraMap ℂ N.toStarSubalgebra Complex.I - D) := by
    apply (StarSubalgebra.coe_isUnit N.toStarSubalgebra).mp
    exact spectrum.mem_resolventSet_iff.mp (imaginary_mem_resolvent hD)
  have h1 := congrArg π (Ring.mul_inverse_cancel _ hunit)
  have h2 := congrArg ρ (Ring.inverse_mul_cancel _ hunit)
  change π ((algebraMap ℂ N.toStarSubalgebra Complex.I - D) * resolvent D Complex.I) = π 1 at h1
  change ρ (resolvent D Complex.I * (algebraMap ℂ N.toStarSubalgebra Complex.I - D)) = ρ 1 at h2
  simp only [map_mul, map_one] at h1 h2
  rw [her] at h1
  have heq := left_inv_eq_right_inv h1 h2
  simp only [map_sub, AlgHomClass.commutes] at heq
  exact sub_right_injective heq
end BicommutantDensity
end StronglyRationalVOA

end

end OAI
