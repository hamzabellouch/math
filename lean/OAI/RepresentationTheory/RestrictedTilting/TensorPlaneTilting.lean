import OAI.RepresentationTheory.RestrictedTilting.PiPlaneOrigin
import OAI.RepresentationTheory.RestrictedTilting.CoordinateTensor
import OAI.RepresentationTheory.RestrictedTilting.AssociatedPlaneJet

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]
variable {β : Type u} [Fintype β] [DecidableEq β]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]
  [Module.Finite k (M ⧸ planeJetRelation (M := M) k 1)]
variable (τ : Representation k (SL2 k) (β → k)) (σ : Representation k (SL2 k) M)
  (hσ : PlaneCompatible k σ)

noncomputable def tensorPlaneOriginIso :
    FDRep.of τ ⊗ planeJetFD k σ hσ 1 ≅
    @planeJetFD k _ (β → M) _ _ _ _ (piPlaneOrigin_finite (β := β) (M := M) k)
      (matrixTensorRepresentation τ σ) (matrixTensor_planeCompatible k τ σ hσ) 1 := by
  letI := piPlaneOrigin_finite (β := β) (M := M) k
  let C := coordinateTensorEquiv (β := β) (M := M ⧸ planeJetRelation (M := M) k 1) k
  let E := piPlaneOriginEquiv (β := β) (M := M) k
  let f : FDRep.of τ ⊗ planeJetFD k σ hσ 1 ⟶
      planeJetFD k (matrixTensorRepresentation τ σ) (matrixTensor_planeCompatible k τ σ hσ) 1 :=
    fdrepHom k (C.trans E.symm).toLinearMap (by
      intro g v
      apply E.injective
      change E (E.symm (C ((τ.tprod (planeJetRep k σ hσ 1)) g v))) =
        E (planeJetRep k (matrixTensorRepresentation τ σ) (matrixTensor_planeCompatible k τ σ hσ)
          1 g (E.symm (C v)))
      rw [E.apply_symm_apply, piPlaneOriginEquiv_intertwines, E.apply_symm_apply]
      exact coordinateTensorEquiv_intertwines k τ (planeJetRep k σ hσ 1) g v)
  letI : IsIso f := fdrepHom_isIso_of_bijective k f (C.trans E.symm).bijective
  exact asIso f

variable [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "σN" => associatedSectionsRepresentation k ι ρ
local notation "hN" => associatedSections_planeCompatible k ι ρ
variable [Module.Finite k ((associatedSectionsSubmodule k ι ρ) ⧸
  planeJetRelation (M := associatedSectionsSubmodule k ι ρ) k 1)]

noncomputable def associatedOriginJetIso :
    associatedOriginFD k ι ρ P hP d hd ≅ planeJetFD k σN hN 1 := by
  let E : (associatedOriginRep k ι ρ).V ≃ₗ[k] N ⧸ planeJetRelation (M := N) k 1 :=
    Submodule.quotEquivOfEq _ _ (associated_planeJet_one k ι ρ).symm
  let f : associatedOriginFD k ι ρ P hP d hd ⟶ planeJetFD k σN hN 1 := fdrepHom k E.toLinearMap (by
    intro g v
    obtain ⟨v,rfl⟩ := (associatedOriginRelations k ι ρ).mkQ_surjective v
    rfl)
  letI : IsIso f := fdrepHom_isIso_of_bijective k f E.bijective
  exact asIso f

variable (p : ℕ) [Fact p.Prime] [CharP k p]

include hP hd in
lemma tensorAssociatedOrigin_tilting (m : ℕ) (hm : d < p^(m+1))
    (e : steinberg k p m ≃ₗ[k] (β → k)) :
    IsTilting k (@planeJetFD k _ (β → N) _ _ _ _ (piPlaneOrigin_finite (β := β) (M := N) k)
      (matrixTensorRepresentation (coordinateRepresentation k (steinberg k p m).ρ e) σN)
      (matrixTensor_planeCompatible k _ σN hN) 1) := by
  have h := associatedOrigin_tilting k p ι ρ P hP d hd m hm
  exact h.of_iso k
    ((MonoidalCategory.tensorIso (coordinateFDIso k (steinberg k p m) e)
      (associatedOriginJetIso k ι ρ P hP d hd)) ≪≫
        tensorPlaneOriginIso k (coordinateRepresentation k (steinberg k p m).ρ e) σN hN)
end FiberFunctorProof

end OAI
