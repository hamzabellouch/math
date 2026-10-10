import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPacking
import OAI.RepresentationTheory.UniversalSquare.Support.PartWords

namespace OAI

/-! Word Packing Leaves. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.bounded {rs ps : List ℕ} {μ : YoungDiagram} {d E : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hD : μ.colLen 0 ≤ d) (hps : ps.sum = rs.sum) (hone : ps.length ≤ E)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : SupportLE (wordRep rs.sum E)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation) :
    WordPacking rs ps d A label {k} := by
  classical
  let f := Fin.castLE hD
  let w := Classical.choose (exists_word_of_parts ps hps)
  have hw := Classical.choose_spec (exists_word_of_parts ps hps)
  have hlocal : ∀ a, ((A ∘ pairLetterMap f f) a ∧
      (label ∘ pairLetterMap f f) a = k) ↔ output a ∈ I := by
    intro a
    rw [Function.comp_apply,Function.comp_apply,he,output_pairLetterMap f (fun _ => rfl)]
  have hs' : SupportLE (wordRep rs.sum ps.length)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation :=
    (SupportLE.of_injective (letterLift (Fin.castLE hone))
      (letterLift_injective _ (Fin.castLE_injective hone))).trans hs
  let P := boundedPacking ((enumerate rs).trans e) k I
    (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f) hlocal hs' (Pi.single w 1)
  let Q := P.lift f (fun _ => rfl) A label
  refine {
    word := w
    counts := hw
    packing := Q.congr (standard_placed e hr hc hD).symm rfl
    marksBound := ?_ }
  intro i
  change k ∈ ({k} : Finset ℕ)
  simp

theorem neighboring_word_support {n r : ℕ} (hn : n = 2*r+1)
    (a : Tableau n (ShortColumns.shape r 1).transpose) :
    SupportLE (wordRep n 4)
      (projectedSpechtTensor a a (inOutputs (Set.Icc r (r+1)))
        (inOutputs_invariant (Set.Icc r (r+1)))).toRepresentation := by
  subst n
  apply word_supportLE
  intro μ t hμ
  obtain ⟨F,hF⟩ := neighboring r a a μ t hμ
  refine ⟨F,?_⟩
  intro h0
  have hzero := hF (show F ⟨polytabloid t,mem_cyclic _ _⟩ = F 0 by rw [h0]; rfl)
  exact polytabloid_ne_zero t (congrArg Subtype.val hzero)

end Saxl.Balance
end
end

end OAI
