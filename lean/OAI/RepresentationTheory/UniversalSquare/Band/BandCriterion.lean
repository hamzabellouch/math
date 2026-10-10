import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.SubdiagramSupport
import OAI.RepresentationTheory.UniversalSquare.Band.BandAllocationLists

namespace OAI

/-! Band Criterion. -/

section

noncomputable section
namespace Saxl.ShortColumns

lemma card (b δ : ℕ) (hδ : δ ≤ 1) : (shape b δ).card = 2*b+δ := by
  have h (n : ℕ) (t : Tableau n (shape b δ)) : (shape b δ).card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe, YoungDiagram.card] using
      (Fintype.card_congr t).symm
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl | rfl
  · simpa only [Nat.add_zero] using h _ (evenTableau b)
  · exact h _ (oddTableau b)

end Saxl.ShortColumns
namespace UniversalTensorSquare
open Saxl

lemma candidateBandSize_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (t : Tableau n (candidate M b δ)) :
    candidateBandSize t = 2*M-1+2*r := by
  let s := canonicalTableau (ShortColumns.shape b δ) ((ShortColumns.card b δ hδ).trans hr.symm)
  simpa only [Fintype.card_fin, Fintype.card_sum] using
    Fintype.card_congr (candidateBandSplit hM t s s)

theorem band_kronecker_pos {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (t : Tableau n (candidate M b δ))
    (lam : YoungDiagram) (s : Tableau n lam) (hband : BandTest M r lam) :
    0 < kronecker t t s := by
  obtain ⟨d,hd₁,hd₄,q,hq,hK,hclear,hrcap⟩ := hband
  obtain ⟨μ,η,ps,hμlam,hμcard,hηcard,hp,he,ha,hb,hc,hηe,hηw,
    ⟨Eμ,Eμr,Eμc⟩,⟨Eη,Eηr,Eηc⟩⟩ :=
    band_subdiagram_columns lam (2*M-1) r d q hd₁ hK hclear hrcap
  let a := canonicalTableau (ShortColumns.shape b δ) ((ShortColumns.card b δ hδ).trans hr.symm)
  let v := canonicalTableau μ (hμcard.trans (candidateBandSize_eq hM hδ hr t).symm)
  obtain ⟨F,hF⟩ := candidateBandWord_support_of_columns hM hδ hr hd₄ t a a ps hp he ha hb hc
    μ η hηcard hηe (hηw.trans hq) Eμ Eμr Eμc Eη Eηr Eηc v
  exact candidate_kronecker_pos_of_subdiagram hM t hμlam v s F hF

theorem fixedCandidate_band_pos (n : ℕ) (hM : 4 ≤ staircaseIndex n)
    (μ : YoungDiagram) (hμ : μ.card = n)
    (hband : BandTest (staircaseIndex n) (remainderPairs n) μ) :
    0 < kronecker (canonicalTableau (fixedCandidate n) (fixedCandidate_card n (by omega)))
      (canonicalTableau (fixedCandidate n) (fixedCandidate_card n (by omega)))
      (canonicalTableau μ hμ) := by
  have hδ : remainderPairs n % 2 ≤ 1 := by omega
  have hr : remainderPairs n = 2 * (remainderPairs n / 2) + remainderPairs n % 2 := by omega
  exact band_kronecker_pos (M := staircaseIndex n) (b := remainderPairs n / 2)
    (δ := remainderPairs n % 2) (r := remainderPairs n) hM hδ hr
    (canonicalTableau (fixedCandidate n) (fixedCandidate_card n (by omega)))
    μ (canonicalTableau μ hμ) hband

end UniversalTensorSquare
end
end

end OAI
