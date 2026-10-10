import Mathlib

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
open Filter Topology
open scoped NNReal
universe u v w
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {α : Type v} {β : Type w}

theorem tendsto_coeff_of_dense_of_bound (e : β → K) (hd : DenseRange e)
    (A : α → K →L[ℂ] K) (B : K →L[ℂ] K) (l : Filter α) (C : ℝ≥0)
    (hbound : ∀ a, ‖A a‖ ≤ C)
    (hc : ∀ u v, Tendsto (fun a => inner ℂ (e u) (A a (e v))) l
      (nhds (inner ℂ (e u) (B (e v))))) (x y : K) :
    Tendsto (fun a => inner ℂ x (A a y)) l (nhds (inner ℂ x (B y))) := by
  have hfirst (v : β) (x : K) :
      Tendsto (fun a => inner ℂ x (A a (e v))) l (nhds (inner ℂ x (B (e v)))) := by
    have heq : Equicontinuous (fun a x => inner ℂ x (A a (e v))) := by
      apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous _ (C * ‖e v‖₊)
      intro a
      apply LipschitzWith.of_dist_le_mul
      intro u w
      rw [dist_eq_norm, ← inner_sub_left, dist_eq_norm]
      have hh : ‖A a (e v)‖ ≤ C * ‖e v‖ :=
        (A a).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hbound a) (norm_nonneg _))
      calc
        ‖inner ℂ (u-w) (A a (e v))‖ ≤ ‖u-w‖ * ‖A a (e v)‖ := norm_inner_le_norm _ _
        _ ≤ ‖u-w‖ * (C * ‖e v‖) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
    exact hd.induction (fun z ⟨u, huz⟩ => huz ▸ hc u v)
      (heq.isClosed_setOfPred_tendsto (by fun_prop)) x
  have heq : Equicontinuous (fun a y => inner ℂ x (A a y)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (‖x‖₊ * C)
    intro a
    apply LipschitzWith.of_dist_le_mul
    intro u w
    rw [dist_eq_norm, ← inner_sub_right, ← map_sub, dist_eq_norm]
    have hh : ‖A a (u-w)‖ ≤ C * ‖u-w‖ :=
      (A a).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hbound a) (norm_nonneg _))
    calc
      ‖inner ℂ x (A a (u-w))‖ ≤ ‖x‖ * ‖A a (u-w)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (C * ‖u-w‖) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
  exact hd.induction (fun z ⟨v, hvz⟩ => hvz ▸ hfirst v x)
    (heq.isClosed_setOfPred_tendsto (by fun_prop)) y

theorem tendsto_coeff_of_dense_of_eventual_bound (e : β → K) (hd : DenseRange e)
    (A : α → K →L[ℂ] K) (B : K →L[ℂ] K) (l : Filter α)
    (hbound : ∃ C : ℝ, ∀ᶠ a in l, ‖A a‖ ≤ C)
    (hc : ∀ u v, Tendsto (fun a => inner ℂ (e u) (A a (e v))) l
      (nhds (inner ℂ (e u) (B (e v))))) (x y : K) :
    Tendsto (fun a => inner ℂ x (A a y)) l (nhds (inner ℂ x (B y))) := by
  classical
  obtain ⟨C, hC⟩ := hbound
  let D : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  let A' (a : α) : K →L[ℂ] K := if ‖A a‖ ≤ D then A a else 0
  have hb : ∀ a, ‖A' a‖ ≤ D := by
    intro a
    dsimp [A']
    split_ifs with h
    · exact h
    · simpa only [norm_zero] using D.coe_nonneg
  have he : A' =ᶠ[l] A := by
    filter_upwards [hC] with a ha
    exact ite_eq_left (ha.trans (le_max_left C 0))
  have hc' : ∀ u v, Tendsto (fun a => inner ℂ (e u) (A' a (e v))) l
      (nhds (inner ℂ (e u) (B (e v)))) := by
    intro u v
    apply (hc u v).congr'
    filter_upwards [he] with a ha
    rw [ha]
  apply (tendsto_coeff_of_dense_of_bound e hd A' B l D hb hc' x y).congr'
  filter_upwards [he] with a ha
  rw [ha]
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
