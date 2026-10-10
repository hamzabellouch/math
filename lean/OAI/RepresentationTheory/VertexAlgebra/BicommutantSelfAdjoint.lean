import OAI.RepresentationTheory.VertexAlgebra.BicommutantStrongNet

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
open Filter BoundedIntertwiner
attribute [local instance] Classical.propDecidable InnerProductSpace.complexToReal
universe u w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type w} [Fintype ι]

def selfAdjointOrbitMap (B : StarSubalgebra ℂ (H →L[ℂ] H)) (x : ι → H) :
    selfAdjoint B →ₗ[ℝ] SumSpace ι H where
  toFun b := WithLp.toLp 2 (fun i => (b.val : H →L[ℂ] H) (x i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 

theorem selfAdjoint_mem_orbit (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : Bicommutant B) (hD : IsSelfAdjoint (D : H →L[ℂ] H)) (x : ι → H) :
    WithLp.toLp 2 (fun i => (D : H →L[ℂ] H) (x i)) ∈
      (selfAdjointOrbitMap B x).range.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  intro z hz
  obtain ⟨a,ha⟩ := exists_strong_net B D
  have hw (i : ι) := selfAdjointPart_weak_tendsto hD ha (x i) (z i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hw i)
  have hlim := Complex.continuous_re.tendsto _ |>.comp hsum
  have hlim' : Tendsto (fun n => inner ℝ z
      (selfAdjointOrbitMap B x (selfAdjointPart ℝ (a n)))) atTop
      (nhds (inner ℝ z (WithLp.toLp 2 (fun i => (D : H →L[ℂ] H) (x i))))) := by
    simp_rw [real_inner_eq_re_inner ℂ, PiLp.inner_apply]
    change Tendsto (fun n => (∑ i, inner ℂ (z i)
      (((selfAdjointPart ℝ (a n) : B) : H →L[ℂ] H) (x i))).re) atTop
      (nhds ((∑ i, inner ℂ (z i) ((D : H →L[ℂ] H) (x i))).re))
    exact hlim
  have hzero (n : ℕ × Finset H) : inner ℝ z
      (selfAdjointOrbitMap B x (selfAdjointPart ℝ (a n))) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (K := (selfAdjointOrbitMap B x).range)
      ⟨selfAdjointPart ℝ (a n), rfl⟩ hz
  simp_rw [hzero] at hlim'
  exact (tendsto_nhds_unique tendsto_const_nhds hlim').symm

 

theorem exists_selfAdjoint_approx_finite (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : Bicommutant B) (hD : IsSelfAdjoint (D : H →L[ℂ] H))
    (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : selfAdjoint B, ∀ i, ‖(b.val : H →L[ℂ] H) (x i) - (D : H →L[ℂ] H) (x i)‖ < ε := by
  have hm := selfAdjoint_mem_orbit B D hD x
  change WithLp.toLp 2 (fun i => (D : H →L[ℂ] H) (x i)) ∈
    closure ((selfAdjointOrbitMap B x).range : Set (SumSpace ι H)) at hm
  obtain ⟨y, ⟨b,rfl⟩, hb⟩ := Metric.mem_closure_iff.mp hm ε hε
  refine ⟨b, fun i => ?_⟩
  have hi := PiLp.norm_apply_le
    (selfAdjointOrbitMap B x b - WithLp.toLp 2 (fun i => (D : H →L[ℂ] H) (x i))) i
  change ‖(b.val : H →L[ℂ] H) (x i) - (D : H →L[ℂ] H) (x i)‖ ≤ _ at hi
  apply hi.trans_lt
  rw [dist_eq_norm, norm_sub_rev] at hb
  exact hb

 

theorem exists_selfAdjoint_strong_net (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : Bicommutant B) (hD : IsSelfAdjoint (D : H →L[ℂ] H)) :
    ∃ a : (ℕ × Finset H) → selfAdjoint B, ∀ x : H,
      Tendsto (fun i => ((a i).val : H →L[ℂ] H) x) atTop (nhds ((D : H →L[ℂ] H) x)) := by
  classical
  have hex (i : ℕ × Finset H) : ∃ b : selfAdjoint B, ∀ x ∈ i.2,
      ‖(b.val : H →L[ℂ] H) x - (D : H →L[ℂ] H) x‖ < 1 / ((i.1 : ℝ) + 1) := by
    obtain ⟨b,hb⟩ := exists_selfAdjoint_approx_finite B D hD (fun x : i.2 => x.val)
      (show 0 < 1 / ((i.1 : ℝ)+1) by positivity)
    exact ⟨b, fun x hx => hb ⟨x,hx⟩⟩
  choose a ha using hex
  refine ⟨a, fun x => Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
  refine ⟨(N,{x}), fun i hi => ?_⟩
  have hx : x ∈ i.2 := hi.2 (Finset.mem_singleton_self x)
  have ht : 1 / ((i.1 : ℝ)+1) < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (by positivity :
      0 < 1 / ((i.1 : ℝ)+1))] using hN i.1 hi.1
  simpa only [dist_eq_norm] using (ha i x hx).trans ht
end StronglyRationalVOA.BicommutantDensity

end

end OAI
