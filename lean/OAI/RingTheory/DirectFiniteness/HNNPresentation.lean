import Mathlib
import OAI.RingTheory.DirectFiniteness.FinitePresentation
import OAI.RingTheory.DirectFiniteness.CharacterTwist

namespace OAI

/-! Finite presentation of multiple HNN extensions and character twists. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.CurrentMain

lemma multipleHNN_finitelyPresented {H I : Type*} [Group H]
    [Group.IsFinitelyPresented H] [Finite I]
    (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i) [∀ i, Finite (A i)] :
    Group.IsFinitelyPresented (MultipleHNN.Extension A B φ) := by
  let u : (Σ i, A i) → Monoid.Coprod H (FreeGroup I) := fun j =>
    Monoid.Coprod.inr (FreeGroup.of j.1) * Monoid.Coprod.inl j.2.val
  let v : (Σ i, A i) → Monoid.Coprod H (FreeGroup I) := fun j =>
    Monoid.Coprod.inl (φ j.1 j.2).val * Monoid.Coprod.inr (FreeGroup.of j.1)
  have hc : MultipleHNN.con A B φ = conGen (fun x y => ∃ j, x=u j ∧ y=v j) := by
    unfold MultipleHNN.con
    congr 1
    funext x y
    apply propext
    constructor
    · rintro ⟨i, a, hx, hy⟩
      exact ⟨⟨i,a⟩,hx,hy⟩
    · rintro ⟨⟨i,a⟩,hx,hy⟩
      exact ⟨i,a,hx,hy⟩
  change @Group.IsFinitelyPresented (MultipleHNN.con A B φ).Quotient
    (Con.group (MultipleHNN.con A B φ))
  rw [hc]
  exact finitelyPresented_finite_relations u v

lemma characterTwist_finitelyPresented {A N C V : Type*}
    [CommGroup A] [Group N] [CommGroup C] [Finite A] [Finite C] [Finite V]
    [Group.IsFinitelyPresented N]
    (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v))
    (v₀ : V) (α : V → A →* C) :
    Group.IsFinitelyPresented (CharacterTwist.L ι hi v₀ α) := by
  let : Group.IsFinitelyPresented (N × C) := finitelyPresented_prod N C
  let (v : V) : Finite (CharacterTwist.source (C := C) ι v) :=
    Finite.of_surjective _ (CharacterTwist.src (C := C) ι v).rangeRestrict_surjective
  exact multipleHNN_finitelyPresented _ _ _

end KaplanskyCounterexample.CurrentMain

end

end OAI
