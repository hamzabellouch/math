import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPacking
import OAI.RepresentationTheory.UniversalSquare.Support.PartWords

namespace OAI

/-! Word Packing Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

def placedPiece {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hd : μ.colLen 0 ≤ d) (k : ℕ) (I : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I) :
    Piece (blocks rs (standard d)) (fun _ => k) A label
      (columnOutputSums ((enumerate rs).trans e) (fun _ => k)) (singleFiberHom rs.sum k)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation := by
  let f := Fin.castLE hd
  have hlocal : ∀ a, ((A ∘ pairLetterMap f f) a ∧
      (label ∘ pairLetterMap f f) a = k) ↔ output a ∈ I := by
    intro a
    rw [Function.comp_apply,Function.comp_apply,he,output_pairLetterMap f (fun _ => rfl)]
  rw [standard_placed e hr hc hd]
  exact (projectedPiece ((enumerate rs).trans e) k I _ _ hlocal).lift f (fun _ => rfl) A label

def WordPacking.binaryBounded {rs ss ps : List ℕ} {μ ν : YoungDiagram} {d E : ℕ}
    (e : Cells rs ≃ μ.cells) (f : Cells ss ≃ ν.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hr' : ∀ c, (f c).val.1 = row c)
    (hc' : ∀ c c', (f c).val.2 = (f c').val.2 ↔ col c = col c')
    (hd : μ.colLen 0 ≤ d) (hd' : ν.colLen 0 ≤ d)
    (hsum : ps.sum = (rs++ss).sum) (hlen : ps.length ≤ E)
    (k l : ℕ) (hne : k ≠ l) (I J : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a ∈ J)
    (hs : SupportLE (wordRep (rs++ss).sum E)
      (Representation.coind (sumPermHom (appendPositions rs ss))
        (outer (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
          (inOutputs I) (inOutputs_invariant I)).toRepresentation
          (projectedSpechtTensor ((enumerate ss).trans f) ((enumerate ss).trans f)
            (inOutputs J) (inOutputs_invariant J)).toRepresentation))) :
    WordPacking (rs++ss) ps d A label {k,l} := by
  classical
  let W := projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
    (inOutputs I) (inOutputs_invariant I)
  let X := projectedSpechtTensor ((enumerate ss).trans f) ((enumerate ss).trans f)
    (inOutputs J) (inOutputs_invariant J)
  letI : AddCommGroup (W.toSubmodule ⊗[ℂ] X.toSubmodule) := Module.addCommMonoidToAddCommGroup ℂ
  let P := placedPiece e hr hc hd k I A label he
  let Q := placedPiece f hr' hc' hd' l J A label he'
  let w := Classical.choose (exists_word_of_parts ps hsum)
  have hw := Classical.choose_spec (exists_word_of_parts ps hsum)
  let R := P.join Q (appendPositions rs ss) (fun _ _ => hne)
  have ht : SupportLE (cyclic (wordRep (rs++ss).sum ps.length) (Pi.single w 1)).toRepresentation
      (wordRep (rs++ss).sum E) :=
    (SupportLE.of_injective (subrepInclusion (cyclic (wordRep (rs++ss).sum _) (Pi.single w 1)))
      Subtype.val_injective).trans (SupportLE.of_injective (letterLift (Fin.castLE hlen))
        (letterLift_injective _ (Fin.castLE_injective hlen)))
  refine {
    word := w
    counts := hw
    packing := {
      G := Equiv.Perm (Fin rs.sum) × Equiv.Perm (Fin ss.sum)
      Y := W.toSubmodule ⊗[ℂ] X.toSubmodule
      c := joinedLabels (appendPositions rs ss) (fun _ => k) (fun _ => l)
      σ := columnOutputSums ((enumerate rs).trans e) (fun _ => k) +
        columnOutputSums ((enumerate ss).trans f) (fun _ => l)
      φ := (joinedFiberHom (appendPositions rs ss) (fun _ => k) (fun _ => l)).comp
        ((singleFiberHom rs.sum k).prodMap (singleFiberHom ss.sum l))
      τ := outer W.toRepresentation X.toRepresentation
      piece := ?_
      support := ht.trans hs }
    marksBound := ?_ }
  · rw [blocks_append]
    exact R
  · intro i
    change joinedLabels (appendPositions rs ss) (fun _ => k) (fun _ => l) i ∈ ({k,l} : Finset ℕ)
    unfold joinedLabels
    cases appendPositions rs ss i <;> simp

theorem WordPacking.of_binary_shapes {rs ss ps : List ℕ} {μ ν : YoungDiagram} {d E : ℕ}
    (hp : rs.Perm μ.transpose.rowLens) (hp' : ss.Perm ν.transpose.rowLens)
    (hd : μ.colLen 0 ≤ d) (hd' : ν.colLen 0 ≤ d)
    (hsum : ps.sum = (rs++ss).sum) (hlen : ps.length ≤ E)
    (k l : ℕ) (hne : k ≠ l) (I J : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a ∈ J)
    (hs : ∀ (t : Tableau rs.sum μ) (u : Tableau ss.sum ν),
      SupportLE (wordRep (rs++ss).sum E)
        (Representation.coind (sumPermHom (appendPositions rs ss))
          (outer (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation
            (projectedSpechtTensor u u (inOutputs J) (inOutputs_invariant J)).toRepresentation))) :
    Nonempty (WordPacking (rs++ss) ps d A label {k,l}) := by
  obtain ⟨e,hr,hc⟩ := place_columns μ hp
  obtain ⟨f,hr',hc'⟩ := place_columns ν hp'
  exact ⟨WordPacking.binaryBounded e f hr hc hr' hc' hd hd' hsum hlen
    k l hne I J A label he he' (hs _ _)⟩

end Saxl.Balance
end
end

end OAI
