import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingPairs
import OAI.RepresentationTheory.UniversalSquare.Support.CountedGluing
import OAI.RepresentationTheory.UniversalSquare.Specht.YoungConverse

namespace OAI

/-! Word Packing Cone. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.cone {rs : List ℕ} {μ θ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hD : μ.colLen 0 ≤ d) (ht : θ.card = rs.sum)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : ∀ (ν : YoungDiagram) (t : Tableau rs.sum ν), Dominates ν θ →
      ∃ F : Representation.IntertwiningMap (spechtRep t)
        (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
          (inOutputs I) (inOutputs_invariant I)).toRepresentation, F ≠ 0) :
    WordPacking rs θ.rowLens d A label {k} := by
  classical
  let W := projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
    (inOutputs I) (inOutputs_invariant I)
  let φ := (fiberGroup (fun _ : Fin rs.sum => k)).subtype.comp (singleFiberHom rs.sum k)
  letI : AddCommGroup (Representation.coindV φ W.toRepresentation) := Module.addCommMonoidToAddCommGroup ℂ
  let u := canonicalTableau θ ht
  let q : Fin (θ.colLen 0) ≃ Fin θ.rowLens.length := finCongr YoungDiagram.length_rowLens.symm
  let w := q ∘ rowWord u
  let P := placedPiece e hr hc hD k I A label he
  have hh : SupportLE (tabloidSub u).toRepresentation (Representation.coind φ W.toRepresentation) :=
    (tabloid_supportLE u W.toRepresentation hs).trans
      (SupportLE.of_injective _ (single_coindLift_injective W.toRepresentation k))
  change SupportLE (cyclic (wordRep rs.sum (θ.colLen 0))
    (Pi.single (rowWord u) 1)).toRepresentation (Representation.coind φ W.toRepresentation) at hh
  have hi : SupportLE
      (cyclic (wordRep rs.sum θ.rowLens.length) ((letterLift q) (Pi.single (rowWord u) 1))).toRepresentation
      (Representation.coind φ W.toRepresentation) := by
    apply SupportLE.cyclic_image (Pi.single (rowWord u) 1) (letterLift q)
    exact hh
  rw [letterLift_single] at hi
  refine {
    word := w
    counts := ?_
    packing := {
      G := Equiv.Perm (Fin rs.sum)
      Y := W.toSubmodule
      c := fun _ => k
      σ := columnOutputSums ((enumerate rs).trans e) (fun _ => k)
      φ := singleFiberHom rs.sum k
      τ := W.toRepresentation
      piece := P
      support := hi }
    marksBound := fun _ => Finset.mem_singleton_self k }
  intro j
  rw [wordContent_lift_equiv]
  change (Finset.univ.filter (fun i => rowWord u i = q.symm j)).card = θ.rowLens.get j
  rw [rowWord_content]
  exact YoungDiagram.get_rowLens.symm

theorem WordPacking.of_cone_shape {rs : List ℕ} {μ θ : YoungDiagram} {d : ℕ}
    (hp : rs.Perm μ.transpose.rowLens) (hd : μ.colLen 0 ≤ d) (ht : θ.card = rs.sum)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : ∀ (u : Tableau rs.sum μ) (ν : YoungDiagram) (t : Tableau rs.sum ν), Dominates ν θ →
      ∃ F : Representation.IntertwiningMap (spechtRep t)
        (projectedSpechtTensor u u (inOutputs I) (inOutputs_invariant I)).toRepresentation, F ≠ 0) :
    Nonempty (WordPacking rs θ.rowLens d A label {k}) := by
  obtain ⟨e,hr,hc⟩ := place_columns μ hp
  exact ⟨WordPacking.cone e hr hc hd ht k I A label he (hs _)⟩

end Saxl.Balance
end
end

end OAI
