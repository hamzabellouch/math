import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.OddPath

namespace OAI

/-! Common Path. -/

section

noncomputable section
namespace Saxl.Band

def extendFourBasis (N : Module.Basis (Fin 4) ℂ Mat) (i : ℕ) : Mat :=
  if h : i < 4 then N ⟨i,h⟩ else N 3

lemma extendFourBasis_pathBasis (i : ℕ) :
    extendFourBasis pathBasis i = conjugation (basis i) := by
  unfold extendFourBasis
  split_ifs with h
  · exact pathBasis_apply ⟨i,h⟩
  · rw [pathBasis_apply]
    congr 1
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ i by omega)
    simp [basis, Nat.add_comm]

theorem odd_path_common_basis :
    ∃ N : Module.Basis (Fin 4) ℂ Mat,
      ∀ (r : ℕ) (rs : List ℕ),
        (∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) → ∀ hn : rs.sum = 2*r+1,
        dotProduct
          (fun w : Fin (2*r+1) → Fin 4 =>
            Columns.dualBlockWord rs (extendFourBasis N) (w ∘ Fin.cast hn))
          (Path.bandWord r) ≠ 0 := by
  refine ⟨pathBasis, ?_⟩
  intro r rs hrs hn
  rw [show extendFourBasis pathBasis = (fun i => conjugation (basis i)) from
    funext extendFourBasis_pathBasis]
  exact Columns.odd_path_ordered_contraction r rs hrs hn

end Saxl.Band
end
end

end OAI
