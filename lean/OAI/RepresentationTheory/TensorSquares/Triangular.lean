import Mathlib
import OAI.RepresentationTheory.Saxl.Main

namespace OAI

/-! Irreducible embeddings and staircase tensor squares. -/

noncomputable section
open scoped TensorProduct
open scoped TensorProduct
universe u

namespace UniversalTensorSquares

theorem contains_every_irreducible_of_positive {n : ℕ}
    (lam : YoungDiagram) (hlam : lam.card = n)
    (h : ∀ (nu : YoungDiagram) (hnu : nu.card = n),
      0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
        (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau nu hnu))
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] :
    ∃ F : Representation.IntertwiningMap ρ
      ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
        (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))), Function.Injective F := by
  obtain ⟨p, ⟨e⟩⟩ := Saxl.irreducible_equiv_specht ρ
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff (Saxl.canonicalTableau lam hlam)
    (Saxl.canonicalTableau lam hlam) (Saxl.partitionTableau p)).mp
    (h (Saxl.partitionDiagram p) (Saxl.partitionDiagram_card p))
  let := Saxl.specht_irreducible (Saxl.partitionTableau p)
  have hi : Function.Injective f := by
    have hi' := @Representation.IsIrreducible.injective_or_eq_zero
      (Equiv.Perm (Fin n)) ℂ (Saxl.Specht (Saxl.partitionTableau p))
      (Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
        Saxl.Specht (Saxl.canonicalTableau lam hlam)) _ _ _ _ _ _
      (Saxl.spechtRep (Saxl.partitionTableau p))
      ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
        (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))) f inferInstance
    exact hi'.resolve_right hf
  exact ⟨f.comp e.toIntertwiningMap, hi.comp e.injective⟩

theorem universal_tensor_square_triangular (m : ℕ) (hm : 1 ≤ m) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = m * (m + 1) / 2),
      (∀ (nu : YoungDiagram) (hnu : nu.card = m * (m + 1) / 2),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau nu hnu)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin (m * (m + 1) / 2))) V)
        [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  rw [← Saxl.staircase_card m]
  refine ⟨Saxl.staircase m, rfl, ?_, Saxl.specht_irreducible _, ?_⟩
  · exact Saxl.saxl_conjecture m hm
  · intro V _ _ _ ρ _
    exact Saxl.saxl_contains_every_irreducible m hm ρ

end UniversalTensorSquares

end

end OAI
