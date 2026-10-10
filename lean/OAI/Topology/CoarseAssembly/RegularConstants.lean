import OAI.Topology.CoarseAssembly.AveragingEnergy

namespace OAI

/-! # Invariants of the actual amplified finite regular representation -/

noncomputable section

namespace CoarseAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Q : Type*) [Fintype Q] [Group Q]

/-- Left translations form a unitary representation, with the ample
coefficient space unchanged. -/
def leftTranslationHom : Q →* (lp (fun _ : Q => H) 2 ≃ₗᵢ[ℂ] lp (fun _ : Q => H) 2) where
  toFun := leftTranslation Q
  map_one' := by
    ext x q
    change x ((1 : Q)⁻¹ * q) = x q
    simp
  map_mul' a b := by
    ext x q
    change x ((a * b)⁻¹ * q) = x (b⁻¹ * (a⁻¹ * q))
    simp only [mul_inv_rev, mul_assoc]

theorem regular_fixed_projection (x : lp (fun _ : Q => H) 2)
    (hfix : ∀ g : Q, leftTranslation Q g x = x) : constantProjection Q x = x := by
  have hcoord (q : Q) : x q = x 1 := by
    have h := congrArg (fun v : lp (fun _ : Q => H) 2 => v q) (hfix q)
    change x (q⁻¹ * q) = x q at h
    simpa using h.symm
  have hr : (fiberNormalization Q : ℂ) ≠ 0 := by
    have hs := fiberNormalization_sq Q
    have hn : fiberNormalization Q ≠ 0 := by intro hz; rw [hz] at hs; norm_num at hs
    exact_mod_cast hn
  let a : H := (fiberNormalization Q : ℂ)⁻¹ • x 1
  have hx : x = fiberConstant Q a := by
    apply lp.ext
    funext q
    rw [fiberConstant_apply]
    change x q = (fiberNormalization Q : ℂ) • ((fiberNormalization Q : ℂ)⁻¹ • x 1)
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    exact hcoord q
  rw [hx]
  change (fiberConstantIsometry (H := H) Q)
    ((fiberConstantIsometry (H := H) Q).toContinuousLinearMap.adjoint
      ((fiberConstantIsometry (H := H) Q) a)) = _
  rw [adjoint_apply_isometry]
  rfl

theorem regular_fixed_iff_projection (x : lp (fun _ : Q => H) 2) :
    (∀ g : Q, leftTranslation Q g x = x) ↔ constantProjection Q x = x := by
  refine ⟨regular_fixed_projection Q x, ?_⟩
  intro hx g
  have h := DFunLike.congr_fun (leftTranslation_projection (H := H) Q g) x
  change leftTranslation Q g (constantProjection Q x) = constantProjection Q x at h
  rwa [hx] at h

/-- The kernel of the constant projection is orthogonal to every invariant
vector of the regular representation. -/
theorem inner_eq_zero_of_projection_zero (x y : lp (fun _ : Q => H) 2)
    (hx : constantProjection Q x = 0) (hy : constantProjection Q y = y) :
    inner ℂ y x = 0 := by
  let U := (fiberConstantIsometry (H := H) Q).toContinuousLinearMap
  have hax : U.adjoint x = 0 := by
    apply (fiberConstantIsometry (H := H) Q).injective
    change constantProjection Q x = (fiberConstantIsometry (H := H) Q) 0
    simpa only [map_zero] using hx
  calc
    inner ℂ y x = inner ℂ (constantProjection Q y) x := by rw [hy]
    _ = inner ℂ (U.adjoint y) (U.adjoint x) :=
      (ContinuousLinearMap.adjoint_inner_right U (U.adjoint y) x).symm
    _ = 0 := by rw [hax, inner_zero_right]

end CoarseAssembly

end

end OAI
