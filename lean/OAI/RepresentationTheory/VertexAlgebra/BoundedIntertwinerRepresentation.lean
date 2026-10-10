import OAI.RepresentationTheory.VertexAlgebra.BoundedIntertwinerCore

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι : Type w}

omit [CompleteSpace H] in
theorem eq_adjoint_of_total (T : ι → H →L[ℂ] K) (hDense : DenseRange (core T))
    (D E : K →L[ℂ] K)
    (h : ∀ i j x y, inner ℂ (D (T i x)) (T j y) = inner ℂ (T i x) (E (T j y))) :
    D = E.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have h₁ (i : ι) (u : H) (v : K) :
      inner ℂ (D (T i u)) v = inner ℂ (T i u) (E v) := by
    have he : (fun v => inner ℂ (D (T i u)) v) = (fun v => inner ℂ (T i u) (E v)) := by
      apply hDense.equalizer (by fun_prop) (by fun_prop)
      funext a
      simp only [Function.comp_apply, core_apply, map_sum, inner_sum]
      exact Finset.sum_congr rfl (fun j _ => h i j u (a j))
    exact congrFun he v
  have he : (fun x => inner ℂ (D x) y) = (fun x => inner ℂ x (E y)) := by
    apply hDense.equalizer (by fun_prop) (by fun_prop)
    funext a
    simp only [Function.comp_apply, core_apply, map_sum, sum_inner]
    exact Finset.sum_congr rfl (fun i _ => h₁ i (a i) y)
  exact congrFun he x

variable (B : StarSubalgebra ℂ (H →L[ℂ] H)) (T : ι → H →L[ℂ] K)
  (hDense : DenseRange (core T))
  (hGram : ∀ (b : B) i j, Commute ((T i).adjoint.comp (T j)) (b : H →L[ℂ] H))

include hDense hGram
theorem action_star (b : B) :
    action T ((star b : B) : H →L[ℂ] H) = (action T (b : H →L[ℂ] H)).adjoint := by
  apply eq_adjoint_of_total T hDense
  intro i j x y
  rw [action_intertwines T _ hDense (hGram (star b)),
    action_intertwines T _ hDense (hGram b)]
  change inner ℂ (T i ((b : H →L[ℂ] H).adjoint x)) (T j y) = _
  rw [← ContinuousLinearMap.adjoint_inner_right (T i),
    ContinuousLinearMap.adjoint_inner_left (b : H →L[ℂ] H)]
  have hc := congrArg (fun D : H →L[ℂ] H => D y) (hGram b i j).eq
  change (T i).adjoint (T j ((b : H →L[ℂ] H) y)) =
    (b : H →L[ℂ] H) ((T i).adjoint (T j y)) at hc
  rw [← hc, ContinuousLinearMap.adjoint_inner_right (T i)]

 

def representation : B →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun b := action T (b : H →L[ℂ] H)
  map_zero' := by
    apply ext_of_total T hDense
    intro i x
    rw [action_intertwines T _ hDense (hGram 0)]
    simp
  map_one' := by
    apply ext_of_total T hDense
    intro i x
    rw [action_intertwines T _ hDense (hGram 1)]
    simp
  map_add' b c := by
    apply ext_of_total T hDense
    intro i x
    rw [add_apply, action_intertwines T _ hDense (hGram (b+c)),
      action_intertwines T _ hDense (hGram b), action_intertwines T _ hDense (hGram c)]
    simp
  map_mul' b c := by
    apply ext_of_total T hDense
    intro i x
    rw [mul_apply_eq_comp, action_intertwines T _ hDense (hGram (b*c)),
      action_intertwines T _ hDense (hGram c), action_intertwines T _ hDense (hGram b)]
    rfl
  commutes' z := by
    apply ext_of_total T hDense
    intro i x
    rw [action_intertwines T _ hDense (hGram (algebraMap ℂ B z))]
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' b := by
    exact action_star B T hDense hGram b

@[simp] theorem representation_intertwines (b : B) (i : ι) (x : H) :
    representation B T hDense hGram b (T i x) = T i ((b : H →L[ℂ] H) x) :=
  action_intertwines T _ hDense (hGram b) i x

theorem representation_norm_le (b : B) :
    ‖representation B T hDense hGram b‖ ≤ ‖(b : H →L[ℂ] H)‖ :=
  norm_action_le T _ hDense (hGram b)
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
