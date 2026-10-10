import OAI.RingTheory.DirectFiniteness.GluedGroup

namespace OAI

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
variable {V F A B X : Type} [AddCommGroup A] [AddCommGroup B]
variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)} {f₀ : F}

/-- Insertions and deletions preserve the existence of the anchored lifetime drawing. -/
theorem OpenDiagram.related_iff (token : X × Bool → F × A)
    (Allowed : List (X × Bool) → Prop)
    (hA : ∀ r, Allowed r → ∃ v, (∀ t ∈ r.map token, Inc v t.1) ∧
      ((r.map token).map (fun t => ι v t.1 t.2)).sum = 0)
    {u w : List (X × Bool)} (h : WordReduction.Related Allowed u w) :
    Nonempty (OpenDiagram Inc ι f₀ (u.map token)) ↔
      Nonempty (OpenDiagram Inc ι f₀ (w.map token)) := by
  induction h with
  | rel u w h =>
    cases h with
    | block pre r post hr =>
      obtain ⟨v, hi, hs⟩ := hA r hr
      simp only [List.map_append]
      constructor
      · rintro ⟨D⟩
        exact D.deleteWordBlock _ _ _ v hi hs
      · rintro ⟨D⟩
        exact D.insertWordBlock _ _ _ v hi hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end KaplanskyCounterexample.Planar

end

end OAI
