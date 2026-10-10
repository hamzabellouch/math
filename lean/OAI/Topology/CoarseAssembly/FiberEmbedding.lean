import OAI.Topology.CoarseAssembly.HilbertSum
import OAI.Topology.CoarseAssembly.FiberConstants
import OAI.Topology.CoarseAssembly.Conjugation

namespace OAI

/-! # The constant-fiber spatial isometry

This is the actual map from the base Roe module to the fibered Roe module.
On singleton boundary fibers it is exactly the coordinate inclusion.
-/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} (Q : I → Type*) [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fiberEmbedding : lp (fun _ : I => H) 2 →ₗᵢ[ℂ] lp (fun _ : Sigma Q => H) 2 :=
  flattenIsometry.comp (blockIsometry (fun i => fiberConstantIsometry (Q i)))

omit [CompleteSpace H] in
@[simp] theorem fiberEmbedding_apply (x : lp (fun _ : I => H) 2) (i : I) (q : Q i) :
    fiberEmbedding Q x ⟨i, q⟩ = (fiberNormalization (Q i) : ℂ) • x i := rfl

omit [CompleteSpace H] in
theorem fiberEmbedding_singleton [DecidableEq I] [DecidableEq (Sigma Q)]
    (i : I) [Subsingleton (Q i)] (q : Q i) (h : H) :
    fiberEmbedding Q (lp.single 2 i h) = lp.single 2 ⟨i, q⟩ h := by
  let : Unique (Q i) := ⟨⟨q⟩, fun x => Subsingleton.elim x q⟩
  apply lp.ext
  funext z
  rcases z with ⟨j, r⟩
  by_cases hji : j = i
  · subst j
    have hqr : r = q := Subsingleton.elim _ _
    subst r
    simp [fiberEmbedding_apply]
  · have hz : (⟨j, r⟩ : Sigma Q) ≠ ⟨i, q⟩ := fun h => hji (congrArg Sigma.fst h)
    simp [fiberEmbedding_apply, hji, hz]

def fiberProjection : lp (fun _ : Sigma Q => H) 2 →L[ℂ] lp (fun _ : Sigma Q => H) 2 :=
  (fiberEmbedding Q).toContinuousLinearMap.comp (fiberEmbedding Q).toContinuousLinearMap.adjoint

theorem fiberProjection_idempotent :
    fiberProjection (H := H) Q * fiberProjection Q = fiberProjection Q := by
  ext x
  simp [fiberProjection]

theorem fiberProjection_selfAdjoint : star (fiberProjection (H := H) Q) = fiberProjection Q := by
  simp [fiberProjection, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp]

theorem fiberProjection_norm_le : ‖fiberProjection (H := H) Q‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  have hv := (fiberEmbedding (H := H) Q).norm_toContinuousLinearMap_le
  nlinarith [norm_nonneg (fiberEmbedding (H := H) Q).toContinuousLinearMap]

end CoarseAssembly

end

end OAI
