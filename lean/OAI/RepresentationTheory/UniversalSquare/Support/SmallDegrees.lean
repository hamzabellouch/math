import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeFive
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeSeven
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeEight

namespace OAI

/-! Small Degrees. -/

section

namespace UniversalTensorSquare
open Saxl

universe u

theorem universal_tensor_square_le_ten
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9)
    (hsmall : n ≤ 10) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  have hcases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact universal_tensor_square_triangular 1 (by decide)
  · exact universal_tensor_square_triangular 2 (by decide)
  · exact universal_tensor_square_five
  · exact universal_tensor_square_triangular 3 (by decide)
  · exact universal_tensor_square_seven
  · exact universal_tensor_square_eight
  · exact universal_tensor_square_triangular 4 (by decide)

end UniversalTensorSquare
end

end OAI
