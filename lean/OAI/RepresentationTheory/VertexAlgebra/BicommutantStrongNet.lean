import OAI.RepresentationTheory.VertexAlgebra.BicommutantFinite

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
open Filter
attribute [local instance] Classical.propDecidable
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Bicommutant (B : StarSubalgebra ℂ (H →L[ℂ] H)) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))

 

theorem exists_strong_net (B : StarSubalgebra ℂ (H →L[ℂ] H)) (D : Bicommutant B) :
    ∃ a : (ℕ × Finset H) → B, ∀ x : H,
      Tendsto (fun i => (a i : H →L[ℂ] H) x) atTop (nhds ((D : H →L[ℂ] H) x)) := by
  classical
  have hex (i : ℕ × Finset H) : ∃ b : B, ∀ x ∈ i.2,
      ‖(b : H →L[ℂ] H) x - (D : H →L[ℂ] H) x‖ < 1 / ((i.1 : ℝ) + 1) := by
    obtain ⟨b,hb⟩ := exists_approx_finite B D (fun x : i.2 => x.val)
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

 
theorem selfAdjointPart_weak_tendsto
    {B : StarSubalgebra ℂ (H →L[ℂ] H)} {ι : Type*} {F : Filter ι}
    {a : ι → B} {D : H →L[ℂ] H} (hD : IsSelfAdjoint D)
    (ha : ∀ x, Tendsto (fun i => (a i : H →L[ℂ] H) x) F (nhds (D x))) (x y : H) :
    Tendsto (fun i => inner ℂ y (((selfAdjointPart ℝ (a i) : B) : H →L[ℂ] H) x)) F
      (nhds (inner ℂ y (D x))) := by
  have h1 := (tendsto_const_nhds (x := y)).inner (𝕜 := ℂ) (ha x)
  have h2 := (ha y).inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
  have h := (h1.add h2).const_smul (1/2 : ℝ)
  have he (b : H →L[ℂ] H) :
      inner ℂ y (((1/2 : ℝ) • (b + star b)) x) =
      (1/2 : ℝ) • (inner ℂ y (b x) + inner ℂ (b y) x) := by
    simp only [smul_apply, add_apply,
      inner_smul_right_eq_smul, inner_add_right]
    exact congrArg (fun z : ℂ => (1/2 : ℝ) • (inner ℂ y (b x) + z))
      (ContinuousLinearMap.adjoint_inner_right b y x)
  have hd : inner ℂ (D y) x = inner ℂ y (D x) := by
    have he := ContinuousLinearMap.adjoint_inner_left D x y
    change inner ℂ ((star D) y) x = _ at he
    rwa [hD.star_eq] at he
  have hf (i : ι) : inner ℂ y (((selfAdjointPart ℝ (a i) : B) : H →L[ℂ] H) x) =
      (1/2 : ℝ) • (inner ℂ y ((a i : H →L[ℂ] H) x) + inner ℂ ((a i : H →L[ℂ] H) y) x) := by
    change inner ℂ y (((⅟ 2 : ℝ) • ((a i : H →L[ℂ] H) + star (a i : H →L[ℂ] H))) x) = _
    simpa only [invOf_eq_inv, one_div] using he (a i : H →L[ℂ] H)
  simp_rw [hf]
  convert h using 1
  rw [hd, smul_add, ← add_smul]
  norm_num
end StronglyRationalVOA.BicommutantDensity

end

end OAI
