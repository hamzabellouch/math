import OAI.RepresentationTheory.VertexAlgebra.BoundedIntertwinerFinite

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {ι : Type w}

def core (T : ι → H →L[ℂ] K) : (ι →₀ H) →ₗ[ℂ] K :=
  Finsupp.lsum ℂ (fun i => (T i).toLinearMap)
@[simp] theorem core_apply (T : ι → H →L[ℂ] K) (x : ι →₀ H) :
    core T x = ∑ i ∈ x.support, T i (x i) := rfl
@[simp] theorem core_single (T : ι → H →L[ℂ] K) (i : ι) (x : H) :
    core T (Finsupp.single i x) = T i x := by
  simp [core, Finsupp.lsum_apply, Finsupp.sum_single_index]

def coreAct (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H) : (ι →₀ H) →ₗ[ℂ] K :=
  core (fun i => (T i).comp D)
@[simp] theorem coreAct_apply (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H) (x : ι →₀ H) :
    coreAct T D x = ∑ i ∈ x.support, T i (D (x i)) := rfl
@[simp] theorem coreAct_single (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H) (i : ι) (x : H) :
    coreAct T D (Finsupp.single i x) = T i (D x) :=
  core_single (fun i => (T i).comp D) i x

variable [CompleteSpace H] [CompleteSpace K]

theorem norm_coreAct_le (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H)
    (h : ∀ i j, Commute ((T i).adjoint.comp (T j)) D) (x : ι →₀ H) :
    ‖coreAct T D x‖ ≤ ‖D‖ * ‖core T x‖ := by
  classical
  have hn := norm_sum_le (fun i : x.support => T i) D
    (fun i j => h i j) (fun i => x i)
  rw [coreAct_apply, core_apply, Finset.sum_subtype x.support (fun _ => Iff.rfl),
    Finset.sum_subtype x.support (fun _ => Iff.rfl)]
  exact hn

 

def action (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H) : K →L[ℂ] K :=
  (coreAct T D).extendOfNorm (core T)

theorem action_core (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H)
    (hDense : DenseRange (core T)) (h : ∀ i j, Commute ((T i).adjoint.comp (T j)) D)
    (x : ι →₀ H) : action T D (core T x) = coreAct T D x :=
  LinearMap.extendOfNorm_eq hDense ⟨‖D‖, norm_coreAct_le T D h⟩ x

theorem action_intertwines (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H)
    (hDense : DenseRange (core T)) (h : ∀ i j, Commute ((T i).adjoint.comp (T j)) D)
    (i : ι) (x : H) : action T D (T i x) = T i (D x) := by
  simpa only [core_single, coreAct_single] using action_core T D hDense h (Finsupp.single i x)

theorem norm_action_le (T : ι → H →L[ℂ] K) (D : H →L[ℂ] H)
    (hDense : DenseRange (core T)) (h : ∀ i j, Commute ((T i).adjoint.comp (T j)) D) :
    ‖action T D‖ ≤ ‖D‖ :=
  LinearMap.opNorm_extendOfNorm_le hDense (norm_nonneg _) (norm_coreAct_le T D h)

omit [CompleteSpace H] [CompleteSpace K] in
theorem ext_of_total (T : ι → H →L[ℂ] K) (hDense : DenseRange (core T))
    (D E : K →L[ℂ] K) (h : ∀ i x, D (T i x) = E (T i x)) : D = E := by
  apply DFunLike.coe_injective
  apply hDense.equalizer D.continuous E.continuous
  funext x
  simp only [Function.comp_apply, core_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => h i (x i))
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
