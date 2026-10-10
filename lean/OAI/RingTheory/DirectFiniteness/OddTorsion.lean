import Mathlib
import OAI.RingTheory.DirectFiniteness.PrescribedOutputs

namespace OAI

/-! An embedded cyclic subgroup of odd prime order in the prescribed group. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.Prescription.Output

def diagonalPoint : Multiplicative (ZMod ell) →* GluedGroup.PointGroup ell where
  toFun c := Multiplicative.ofAdd (fun _ => c.toAdd)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma diagonalPoint_injective : Function.Injective diagonalPoint := by
  intro c d he
  exact congrArg (fun a : GluedGroup.PointGroup ell => a.toAdd (0 : Fin 2)) he

def retainedPoint : GluedGroup.PointGroup ell →* G :=
  (MonoidHom.inl _ _).comp
    ((CharacterTwist.emb (ChosenCriterion.inclusion ell Inc assignment)
      (ChosenCriterion.inclusion_injective ell Inc assignment nonempty_Inc girth_Inc)
      v0 form).comp
        ((MonoidHom.inl _ _).comp (AssignedDevelopment.point Inc ell assignment v0)))

lemma retainedPoint_injective : Function.Injective retainedPoint := by
  dsimp only [retainedPoint, MonoidHom.coe_comp]
  apply Function.Injective.comp (fun x y h => congrArg Prod.fst h)
  apply Function.Injective.comp (CharacterTwist.emb_injective _ _ _ _)
  apply Function.Injective.comp (fun x y h => congrArg Prod.fst h)
  exact AssignedDevelopment.point_injective Inc ell assignment nonempty_Inc girth_Inc v0

theorem prescribed_odd_prime_order :
    ∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ := by
  refine ⟨ell, Fact.out, prime_odd h.val h.property,
    retainedPoint (diagonalPoint (Multiplicative.ofAdd (1 : ZMod ell))), ?_⟩
  rw [orderOf_injective retainedPoint retainedPoint_injective,
    orderOf_injective diagonalPoint diagonalPoint_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

end KaplanskyCounterexample.Prescription.Output

end

end OAI
