import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceFour
import OAI.RepresentationTheory.UniversalSquare.Balance.PackingPlans

namespace OAI

/-! Exceptional Packing. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

theorem candidate_refined_pos {n M b δ r : ℕ} (hM : 9 ≤ M) (hb : b ≤ M-2)
    (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
    (hn : (candidate M b δ).card = n)
    (q : List ℕ) (hq : q.SortedGE) (hqp : ∀ a ∈ q, 0 < a) (hqn : q.sum = n)
    (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
    (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hparts : p.parts.Perm q)
    (check : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
      ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
        refinedCheck n M r (d+1) (e+1) (a+1) (c+1) q)
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  let θ := YoungDiagram.ofRowLens q hq
  have hrows : θ.rowLens = q := YoungDiagram.rowLens_ofRowLens_eq_self hqp
  have ht : θ.card = n := by rw [card_eq_sum_rowLens, hrows, hqn]
  have hposn : 0 < n := by rw [← hn,candidate_card _ _ _ (by omega)]; omega
  have hp : ∀ a ∈ p.parts, 0 < a := fun a ha => hqp a (hparts.mem_iff.mp ha)
  have hshape : (columnShape p.parts).transpose = θ := by
    rw [columnShape_perm hparts, columnShape_sorted q hq hqp, YoungDiagram.transpose_transpose]
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ (by omega)]
    simp [candidateLengths]
  have hc : p.columns.Perm (candidate M b δ).transpose.rowLens := by
    rw [candidate_transpose, candidate_rowLens (by omega)]
    exact hcols
  have cone (ν : YoungDiagram) (hν : ν.card = n) (hd : Dominates ν θ) :
      0 < kronecker (canonicalTableau (candidate M b δ) hn)
        (canonicalTableau (candidate M b δ) hn) (canonicalTableau ν hν) := by
    apply packingPlan_pos p hv hbands hh hc hp
    simpa only [hshape] using hd
  have htcheck : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
      ∀ a ∈ List.range θ.rowLens.length, ∀ c ∈ List.range θ.rowLens.length,
        refinedCheck n M r (d+1) (e+1) (a+1) (c+1) θ.rowLens := by
    simpa only [hrows] using check
  rcases refined_capacity_dichotomy μ θ hposn hM hrpos hμ ht htcheck with
    h | h | h | h | h | h
  · exact balance_kronecker_pos hM hb hδ _ μ _ h
  · exact balance_kronecker_pos_or_transpose hM hb hδ hn μ hμ (Or.inr h)
  · exact band_kronecker_pos (by omega) hδ hr _ μ _ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact band_kronecker_pos (by omega) hδ hr _ μ.transpose _ h
  · exact cone μ hμ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact cone μ.transpose ((transpose_card μ).trans hμ) h

end UniversalTensorSquare
end
end

end OAI
