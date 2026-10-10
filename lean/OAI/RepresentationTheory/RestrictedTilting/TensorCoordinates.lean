import OAI.RepresentationTheory.RestrictedTilting.CoordinateTensor

namespace OAI

namespace FiberFunctorProof
open Matrix
open scoped TensorProduct BigOperators Kronecker
universe u v
variable (k : Type u) [Field k]
variable {β ι : Type u} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

noncomputable def uncurryLinearEquiv : (β → ι → k) ≃ₗ[k] (β × ι → k) where
  toFun v bi := v bi.1 bi.2
  invFun v b i := v (b,i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
noncomputable def tensorCoordinates (e : V ≃ₗ[k] (β → k)) (f : W ≃ₗ[k] (ι → k)) :
    (V ⊗[k] W) ≃ₗ[k] (β × ι → k) :=
  (TensorProduct.congr e f).trans ((coordinateTensorEquiv k).trans (uncurryLinearEquiv k))

omit [Fintype ι] [DecidableEq ι] in
lemma tensorCoordinates_tmul (e : V ≃ₗ[k] (β → k)) (f : W ≃ₗ[k] (ι → k)) (v : V) (w : W) :
    tensorCoordinates k e f (v ⊗ₜ[k] w) = fun bi => e v bi.1 * f w bi.2 := by
  simp only [tensorCoordinates, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    coordinateTensorEquiv_tmul]
  rfl

variable {G : Type v} [Monoid G]
lemma tensorCoordinates_intertwines (σ : Representation k G V) (ρ : Representation k G W)
    (e : V ≃ₗ[k] (β → k)) (f : W ≃ₗ[k] (ι → k)) (g : G) (v : V ⊗[k] W) :
    tensorCoordinates k e f ((σ.tprod ρ) g v) =
      (LinearMap.toMatrix' (coordinateRepresentation k σ e g) ⊗ₖ
        LinearMap.toMatrix' (coordinateRepresentation k ρ f g)) *ᵥ tensorCoordinates k e f v := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, Matrix.mulVec_add, hv, hw]
  | tmul v w =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, tensorCoordinates_tmul,
      tensorCoordinates_tmul, coordinateRepresentation_equiv, coordinateRepresentation_equiv,
      ← LinearMap.toMatrix'_mulVec (coordinateRepresentation k σ e g),
      ← LinearMap.toMatrix'_mulVec (coordinateRepresentation k ρ f g)]
    funext bi
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap,
      Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    ring
end FiberFunctorProof

end OAI
