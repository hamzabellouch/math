import OAI.RingTheory.DirectFiniteness.PrescribedDirections

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CoordinateCharacters
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance modulusNeZero : NeZero ℓ := inferInstance

abbrev Plane := Multiplicative (Fin 2 → ZMod ℓ)
abbrev Cyclic := Multiplicative (ZMod ℓ)

def form (a : Fin 2 → ZMod ℓ) : Plane ℓ →* Cyclic ℓ :=
  AddMonoidHom.toMultiplicative
    ({ toFun := fun x => ∑ i : Fin 2, a i * x i
       map_zero' := by simp
       map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib] } :
      (Fin 2 → ZMod ℓ) →+ ZMod ℓ)

lemma form_injective : Function.Injective (form ℓ) := by
  intro a b hab
  funext i
  have hi := congrArg (fun φ : Plane ℓ →* Cyclic ℓ =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single i 1)))) hab
  fin_cases i <;> simpa [form, Pi.single_apply] using hi

lemma exists_slot_forms {V : Type u_1} {m : Type u_2} [Fintype V] [Fintype m]
    (hcard : Fintype.card V ≤ Fintype.card m * ℓ ^ 2) :
    ∃ (slot : V → m) (α : V → Plane ℓ →* Cyclic ℓ),
      ∀ v w, v ≠ w → slot v = slot w → α v ≠ α w := by
  have hc : Fintype.card V ≤ Fintype.card (m × (Fin 2 → ZMod ℓ)) := by
    simpa using hcard
  obtain ⟨f⟩ : Nonempty (V ↪ m × (Fin 2 → ZMod ℓ)) := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun v => (f v).1, fun v => form ℓ (f v).2, ?_⟩
  intro v w hvw hs ha
  exact hvw (f.injective (Prod.ext hs (form_injective ℓ ha)))

variable {K : Type u_3} [Field K]

def cyclicCharacter {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) : Cyclic ℓ →* Kˣ :=
  (AddChar.zmodChar ℓ hζ.pow_eq_one).toMonoidHom.toHomUnits

lemma cyclicCharacter_injective {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (cyclicCharacter ℓ hζ) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective ℓ
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun u : Kˣ => (u : K)) hab

lemma cyclicCharacter_ne_one {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    cyclicCharacter ℓ hζ ≠ 1 := by
  intro h
  have he : Multiplicative.ofAdd (1 : ZMod ℓ) = 1 :=
    (cyclicCharacter_injective ℓ hζ) (by simp [h])
  exact (one_ne_zero : (1 : ZMod ℓ) ≠ 0) (congrArg Multiplicative.toAdd he)

end KaplanskyCounterexample.CoordinateCharacters
end

end OAI
