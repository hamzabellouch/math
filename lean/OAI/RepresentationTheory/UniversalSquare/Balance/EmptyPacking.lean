import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingGeometry
import OAI.RepresentationTheory.UniversalSquare.Band.OutputBands

namespace OAI

/-! Empty Packing. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.empty (d : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) :
    WordPacking [] [] d A label ∅ := by
  classical
  let e := Classical.choose (columnShape_placement [])
  have hr := (Classical.choose_spec (columnShape_placement [])).1
  have hc := (Classical.choose_spec (columnShape_placement [])).2
  let μ := columnShape []
  have h0 : μ.colLen 0 = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro h
    have hmem : (0,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr h
    exact isEmptyElim (e.symm ⟨(0,0),hmem⟩)
  let t := (enumerate []).trans e
  let f := Fin.castLE (show μ.colLen 0 ≤ d by omega)
  have he : ∀ a, ((A ∘ pairLetterMap f f) a ∧
      (label ∘ pairLetterMap f f) a = 0) ↔ output a ∈ ({0}:Set ℕ) := by
    intro a
    have hh := a.isLt
    simp only [h0,Nat.zero_mul] at hh
    omega
  have hs : SupportLE (wordRep 0 0)
      (projectedSpechtTensor t t (inOutputs {0}) (inOutputs_invariant {0})).toRepresentation :=
    (SupportLE.of_injective (letterLift (Fin.castLE (show 0 ≤ 1 by omega)))
      (letterLift_injective _ (Fin.castLE_injective _))).trans
      (constant_output_support t 0 (fun i => Fin.elim0 i))
  let w : Fin 0 → Fin 0 := Fin.elim0
  let P := boundedPacking t 0 {0} (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f)
    he hs (Pi.single w 1)
  let Q := P.lift f (fun _ => rfl) A label
  exact {
    word := w
    counts := fun j => Fin.elim0 j
    packing := Q.congr (standard_placed e hr hc (show μ.colLen 0 ≤ d by omega)).symm rfl
    marksBound := fun i => Fin.elim0 i }

def oneIf (x ε : ℕ) : List ℕ := if ε = 0 then [] else [x]

def markIf (x ε : ℕ) : Finset ℕ := if ε = 0 then ∅ else {x}

theorem WordPacking.optional {x ε d : ℕ} (hx : 0 < x) (hd : x ≤ d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ε ≠ 0 → ∀ a, (A a ∧ label a = x) ↔ output a = x) :
    Nonempty (WordPacking (oneIf x ε) (oneIf x ε) d A label (markIf x ε)) := by
  by_cases hε : ε = 0
  · simpa only [oneIf,markIf,ite_eq_left hε] using Nonempty.intro (WordPacking.empty d A label)
  · obtain ⟨P⟩ := WordPacking.repeated (m := 1) (by decide) hx hd x A label (he hε)
    simpa only [oneIf,markIf,ite_eq_right hε,List.replicate_one,one_mul] using Nonempty.intro P

end Saxl.Balance
end
end

end OAI
