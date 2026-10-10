import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.StandardColumns
import OAI.RepresentationTheory.UniversalSquare.Support.WordContents

namespace OAI

/-! Word Packing. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma sum_wordContent {n d : ℕ} (w : Fin n → Fin d) :
    ∑ j, wordContent w j = n := by
  classical
  simp only [wordContent,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

lemma single_joinPositions {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin a → Fin d) (z : Fin b → Fin d) :
    positionProduct e (Pi.single w 1) (Pi.single z 1) =
      Pi.single ((positionWordsEquiv e).symm (w,z)) 1 := by
  have hl := congrArg Prod.fst ((positionWordsEquiv e).apply_symm_apply (w,z))
  have hr := congrArg Prod.snd ((positionWordsEquiv e).apply_symm_apply (w,z))
  change leftWord e ((positionWordsEquiv e).symm (w,z)) = w at hl
  change rightWord e ((positionWordsEquiv e).symm (w,z)) = z at hr
  rw [single_positionProduct e,hl,hr]

namespace Balance
open FlagColumns Columns

def Packing.congr {n d e : ℕ} {v u : WordSpace n d}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {w z : WordSpace n e}
    (P : Packing v A label w) (hv : v = u) (hw : w = z) : Packing u A label z where
  G := P.G
  Y := P.Y
  c := P.c
  σ := P.σ
  φ := P.φ
  τ := P.τ
  piece := by rw [← hv]; exact P.piece
  support := by rw [← hw]; exact P.support

structure WordPacking (rs ps : List ℕ) (d : ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ) (marks : Finset ℕ) where
  word : Fin rs.sum → Fin ps.length
  counts : ∀ j, wordContent word j = ps.get j
  packing : Packing (blocks rs (standard d)) A label (Pi.single word 1)
  marksBound : ∀ i, packing.c i ∈ marks

lemma WordPacking.total {rs ps : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) : ps.sum = rs.sum := by
  calc
    ps.sum = ∑ j, ps.get j := by rw [← List.sum_ofFn, List.ofFn_get]
    _ = ∑ j, wordContent P.word j := Finset.sum_congr rfl (fun j _ => (P.counts j).symm)
    _ = rs.sum := sum_wordContent P.word

def WordPacking.join {rs ss ps qs : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks marks' : Finset ℕ}
    (P : WordPacking rs ps d A label marks) (Q : WordPacking ss qs d A label marks')
    (hdis : Disjoint marks marks') : WordPacking (rs++ss) (ps++qs) d A label (marks ∪ marks') := by
  classical
  let e := appendPositions rs ss
  let f := appendLetters ps qs
  let wi := f.symm ∘ Sum.inl ∘ P.word
  let zi := f.symm ∘ Sum.inr ∘ Q.word
  let P' := P.packing.map (letterLift (f.symm ∘ Sum.inl))
  let Q' := Q.packing.map (letterLift (f.symm ∘ Sum.inr))
  have hd : ∀ i j, P'.c i ≠ Q'.c j := by
    intro i j hij
    have h₁ := P.marksBound i
    have h₂ := Q.marksBound j
    change P.packing.c i = Q.packing.c j at hij
    rw [← hij] at h₂
    exact Finset.disjoint_left.mp hdis h₁ h₂
  let R := P'.join Q' e hd
  have hv : positionProduct e (blocks rs (standard d)) (blocks ss (standard d)) =
      blocks (rs++ss) (standard d) := (blocks_append rs ss _).symm
  have hw : positionProduct e (letterLift (f.symm ∘ Sum.inl) (Pi.single P.word 1))
      (letterLift (f.symm ∘ Sum.inr) (Pi.single Q.word 1)) =
      Pi.single ((positionWordsEquiv e).symm (wi,zi)) 1 := by
    rw [letterLift_single,letterLift_single,single_joinPositions]
    rfl
  refine {
    word := (positionWordsEquiv e).symm (wi,zi)
    counts := ?_
    packing := R.congr hv hw
    marksBound := ?_ }
  · intro j
    change wordContent ((positionWordsEquiv e).symm
      ((fun i => f.symm (Sum.inl (P.word i))), (fun i => f.symm (Sum.inr (Q.word i))))) j = _
    rw [wordContent_position_join e f P.word Q.word j, get_appendLetters]
    rcases h : f j with j | j
    · exact P.counts j
    · exact Q.counts j
  · intro i
    change joinedLabels e P.packing.c Q.packing.c i ∈ marks ∪ marks'
    unfold joinedLabels
    rcases e i with i | i
    · exact Finset.mem_union_left _ (P.marksBound i)
    · exact Finset.mem_union_right _ (Q.marksBound i)

def WordPacking.sorted {rs ps : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) (hp : ∀ p ∈ ps, 0 < p) :
    WordPacking rs (columnShape ps).transpose.rowLens d A label marks := by
  classical
  let q := Classical.choose (list_get_equiv (columnShape_rows_permutation ps hp))
  have hq := Classical.choose_spec (list_get_equiv (columnShape_rows_permutation ps hp))
  refine {
    word := q ∘ P.word
    counts := ?_
    packing := (P.packing.map (letterLift q)).congr rfl (letterLift_single q P.word)
    marksBound := P.marksBound }
  intro j
  rw [wordContent_lift_equiv,P.counts,← hq,Equiv.apply_symm_apply]

theorem WordPacking.kronecker_pos {rs ps : List ℕ} {lam μ : YoungDiagram}
    (a : Tableau rs.sum lam) (t : Tableau rs.sum μ)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps (lam.colLen 0) A label marks)
    (hv : blocks rs (standard (lam.colLen 0)) = polytabloid a)
    (hp : ∀ p ∈ ps, 0 < p)
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hd : Dominates μ (columnShape ps).transpose) : 0 < kronecker a a t := by
  let θ := (columnShape ps).transpose
  let Q := P.sorted hp
  let q : Fin θ.rowLens.length ≃ Fin (θ.colLen 0) := finCongr YoungDiagram.length_rowLens
  let w := q ∘ Q.word
  let R := (Q.packing.map (letterLift q)).congr hv (letterLift_single q Q.word)
  apply R.kronecker_pos a t w ho _ hd (Equiv.refl _) _
  · have hc : μ.card = rs.sum := by
      simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
    rw [hc, show θ.card = ps.sum from by simp only [θ,transpose_card,columnShape_card]]
    exact P.total.symm
  · intro j
    change wordContent w j = θ.rowLen j
    rw [wordContent_lift_equiv,Q.counts]
    exact YoungDiagram.get_rowLens

end Balance
end Saxl
end
end

end OAI
