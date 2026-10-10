import OAI.RepresentationTheory.RestrictedTilting.BoundedUnipotentTilting
import OAI.RepresentationTheory.RestrictedTilting.FiniteSubgroupLift
import OAI.RepresentationTheory.RestrictedTilting.TensorCoordinates

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory Matrix
open scoped TensorProduct Kronecker
universe u

 

def RestrictedTiltingTheorem : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ), 1 ≤ r → ∀ (l : (Fin r → ZMod p) →+ k), Function.Injective l →
    ∀ (D : FDRep k (Multiplicative (Fin r → ZMod p))),
      ∃ T : FDRep k (SL2 k), IsTilting k T ∧
        Nonempty (((restrictElementary k p r l).obj (steinberg k p (r-1)) ⊗ D) ≅
          (restrictElementary k p r l).obj T)

 

theorem restricted_tilting : RestrictedTiltingTheorem.{u} := by
  intro k _ _ p _ _ r hr l hl D
  classical
  let S := steinberg k p (r-1)
  let β := ULift.{u} (Fin (Module.finrank k S))
  let ι := ULift.{u} (Fin (Module.finrank k D))
  let e : S ≃ₗ[k] (β → k) := ((Module.finBasis k S).reindex Equiv.ulift.symm).equivFun
  let f : D ≃ₗ[k] (ι → k) := ((Module.finBasis k D).reindex Equiv.ulift.symm).equivFun
  let σ := coordinateRepresentation k D.ρ f
  obtain ⟨ρ,P,hP,hd,hρ⟩ := finite_subgroup_polynomial_lift k l hl σ
  have hc : Fintype.card (Fin r → ZMod p) = p^r := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [hc] at hd
  have hp : 0 < p^r := Nat.pow_pos (Fact.out : p.Prime).pos
  have hm : p^r-1 < p^((r-1)+1) := by
    rw [Nat.sub_add_cancel hr]
    omega
  obtain ⟨T,hT,E,hE⟩ := bounded_unipotent_tilting_coordinates k p β ι ρ P hP (p^r-1) hd
    (r-1) hm e
  let C := tensorCoordinates k e f
  let A := ((restrictElementary k p r l).obj S) ⊗ D
  let B := (restrictElementary k p r l).obj T
  let L : A ≃ₗ[k] B := C.trans E.symm
  have hL : ∀ a, ∀ v : A, L (A.ρ a v) = B.ρ a (L v) := by
    intro a v
    apply E.injective
    change E (E.symm (C (A.ρ a v))) = E (T.ρ (unipotent k (l a.toAdd)) (E.symm (C v)))
    rw [E.apply_symm_apply, hE, E.apply_symm_apply]
    have hC := tensorCoordinates_intertwines k
      (S.ρ.comp (elementaryEmbedding k p r l)) D.ρ e f a v
    change C (A.ρ a v) = _ at hC
    rw [hC, hρ]
    rfl
  refine ⟨T,hT, ⟨Action.mkIso L.toFGModuleCatIso (fun a => ?_)⟩⟩
  apply FGModuleCat.hom_ext
  exact LinearMap.ext (hL a)
end FiberFunctorProof

end OAI
