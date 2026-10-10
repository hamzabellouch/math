import OAI.Topology.CoarseAssembly.FiberEmbedding

namespace OAI

/-! # Permutations and normalized quotient-copying maps

These are the two types of edge operator in the graph construction:
permutations at equal depth, and normalized copying along a surjective
finite-group quotient. Their norm and constant-vector properties are
proved on the actual finite-fiber Hilbert spaces.
-/

noncomputable section

namespace CoarseAssembly

variable {Q R H : Type*} [Fintype Q] [Fintype R]
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

def reindexFiberVector (e : Q ≃ R) (x : lp (fun _ : Q => H) 2) :
    lp (fun _ : R => H) 2 := ⟨fun r => x (e.symm r), Memℓp.all _⟩

omit [NormedSpace ℂ H] in
theorem reindexFiber_norm (e : Q ≃ R) (x : lp (fun _ : Q => H) 2) :
    ‖reindexFiberVector e x‖ = ‖x‖ := by
  have hsq : ‖reindexFiberVector e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq, tsum_fintype, tsum_fintype]
    exact Equiv.sum_comp e.symm (fun q => ‖x q‖ ^ 2)
  nlinarith [norm_nonneg (reindexFiberVector e x), norm_nonneg x]

def reindexFiber (e : Q ≃ R) : lp (fun _ : Q => H) 2 ≃ₗᵢ[ℂ] lp (fun _ : R => H) 2 where
  toFun := reindexFiberVector e
  invFun := reindexFiberVector e.symm
  left_inv x := by apply lp.ext; funext q; simp [reindexFiberVector]
  right_inv x := by apply lp.ext; funext r; simp [reindexFiberVector]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reindexFiber_norm e

@[simp] theorem reindexFiber_apply (e : Q ≃ R) (x : lp (fun _ : Q => H) 2) (r : R) :
    reindexFiber e x r = x (e.symm r) := rfl

theorem reindexFiber_constant (e : Q ≃ R) (h : H) :
    reindexFiber e (fiberConstant Q h) = fiberConstant R h := by
  apply lp.ext
  funext r
  simp only [reindexFiber_apply, fiberConstant_apply, fiberNormalization, Fintype.card_congr e]

section GroupQuotient

variable {G K : Type*} [Group G] [Group K] [Fintype G] [Fintype K]

def quotientSection (f : G →* K) (hf : Function.Surjective f) (k : K) : G := (hf k).choose

omit [Fintype G] [Fintype K] in
@[simp] theorem quotientSection_spec (f : G →* K) (hf : Function.Surjective f) (k : K) :
    f (quotientSection f hf k) = k := (hf k).choose_spec

def quotientFiberEquiv (f : G →* K) (hf : Function.Surjective f) : G ≃ ((_k : K) × f.ker) where
  toFun g := ⟨f g, ⟨(quotientSection f hf (f g))⁻¹ * g, by simp⟩⟩
  invFun z := quotientSection f hf z.1 * z.2.val
  left_inv g := by simp
  right_inv z := by
    rcases z with ⟨k, z, hz⟩
    have hz' : f z = 1 := hz
    simp only [map_mul, quotientSection_spec, hz', mul_one]
    congr 1
    apply Subtype.ext
    simp

def quotientCopy (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f) :
    lp (fun _ : K => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 := by
  classical
  exact (reindexFiber (quotientFiberEquiv f hf).symm).toLinearIsometry.comp
    (fiberEmbedding (fun _ : K => f.ker))

@[simp] theorem quotientCopy_apply (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f)
    (x : lp (fun _ : K => ℂ) 2) (g : G) :
    quotientCopy f hf x g = (fiberNormalization f.ker : ℂ) * x (f g) := rfl

theorem quotientCopy_constant (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f) :
    quotientCopy f hf (fiberConstant K (1 : ℂ)) = fiberConstant G 1 := by
  classical
  have hcard : Fintype.card G = Fintype.card K * Fintype.card f.ker := by
    simpa using Fintype.card_congr (quotientFiberEquiv f hf)
  have hnorm : fiberNormalization f.ker * fiberNormalization K = fiberNormalization G := by
    simp only [fiberNormalization, hcard, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg (Fintype.card K)), mul_inv_rev]
  apply lp.ext
  funext g
  simp only [quotientCopy_apply, fiberConstant_apply, smul_eq_mul, mul_one]
  exact_mod_cast hnorm

theorem quotientCopy_adjoint_constant (f : G →* K) [Fintype f.ker]
    (hf : Function.Surjective f) :
    (quotientCopy f hf).toContinuousLinearMap.adjoint (fiberConstant G (1 : ℂ)) =
      fiberConstant K 1 := by
  rw [← quotientCopy_constant f hf, adjoint_apply_isometry]

/-- The shallow-to-deep edge operator, including its right holonomy twist. -/
def twistedQuotientCopy (f : G →* K) [Fintype f.ker] (hf : Function.Surjective f) (a : K) :
    lp (fun _ : K => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 :=
  (quotientCopy f hf).comp (reindexFiber (Equiv.mulRight a)).toLinearIsometry

theorem twistedQuotientCopy_constant (f : G →* K) [Fintype f.ker]
    (hf : Function.Surjective f) (a : K) :
    twistedQuotientCopy f hf a (fiberConstant K (1 : ℂ)) = fiberConstant G 1 := by
  change quotientCopy f hf (reindexFiber (Equiv.mulRight a) (fiberConstant K 1)) = _
  rw [reindexFiber_constant, quotientCopy_constant]

theorem twistedQuotientCopy_adjoint_constant (f : G →* K) [Fintype f.ker]
    (hf : Function.Surjective f) (a : K) :
    (twistedQuotientCopy f hf a).toContinuousLinearMap.adjoint (fiberConstant G (1 : ℂ)) =
      fiberConstant K 1 := by
  rw [← twistedQuotientCopy_constant f hf a, adjoint_apply_isometry]

theorem twistedQuotientCopy_apply (f : G →* K) [Fintype f.ker]
    (hf : Function.Surjective f) (a : K) (x : lp (fun _ : K => ℂ) 2) (g : G) :
    twistedQuotientCopy f hf a x g = (fiberNormalization f.ker : ℂ) * x (f g * a⁻¹) := rfl

end GroupQuotient

end CoarseAssembly

end

end OAI
