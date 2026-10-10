import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.RowSquareTools

namespace OAI

/-! Choice Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

inductive EdgeChoices where
  | fallback
  | node (index : ℕ) (next : (ℕ × ℕ × ℕ) → EdgeChoices)

def solveChoices {rsT rsA rsB : List ℕ} : EdgeChoices → CompactDomains rsT →
    CompactDomains rsA → CompactDomains rsB → List (Edge rsT rsA rsB) →
      Finset (ℕ × ℕ × ℕ) → ℤ
  | .fallback, D, E, F, edges, flag => solveCompact edges.length D E F edges flag
  | .node i next, D, E, F, edges, flag =>
      if D.vanished || E.vanished || F.vanished then 0
      else match edges.rotate i with
        | [] => D.mass * E.mass * F.mass
        | c :: cs => ∑ v ∈ compactEdgeOptions D E F c flag,
            solveChoices (next v) (D.atValue c.1 v.1) (E.atValue c.2.1 v.2.1)
              (F.atValue c.2.2 v.2.2) cs flag

lemma solveChoices_correct {rsT rsA rsB : List ℕ} (ch : EdgeChoices)
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    solveChoices ch D E F edges flag =
      domainContraction D.describe E.describe F.describe edges flag := by
  induction ch generalizing D E F edges with
  | fallback =>
    rw [solveChoices, ← solveCompact_describe]
    exact solveDomains_correct _ _ _ _ _ _ le_rfl
  | node i next ih =>
    rw [solveChoices]
    split_ifs with hv
    · apply Eq.symm
      apply domainContraction_zero
      simpa only [CompactDomains.describe_vanished] using hv
    · rw [← domainContraction_perm D.describe E.describe F.describe (edges.rotate_perm i) flag]
      cases he : edges.rotate i with
      | nil => simp only [domainContraction_nil, CompactDomains.describe_mass]
      | cons c cs =>
        rw [domainContraction_cons_options, compactEdgeOptions_describe]
        apply Finset.sum_congr rfl
        intro v hv
        rw [ih]
        simp only [CompactDomains.describe_atValue]

lemma contractionInteger_choices {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) (ch : EdgeChoices) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveChoices ch (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [solveChoices_correct, CompactDomains.describe_full, CompactDomains.describe_full,
    CompactDomains.describe_full]
  exact contractionInteger_domains ..

end Saxl.Columns

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_choices {n : ℕ} {p q cs ts : List ℕ}
    (hp : GoodRows p) (hq : GoodRows q) (hcs : GoodRows cs) (hts : GoodRows ts)
    (he : cs = transposeRows p ∨ cs = p) (ht : ts = transposeRows q)
    (hn : cs.sum = n) (hn' : ts.sum = n)
    (eb : Fin n ≃ Fin cs.sum) (et : Fin n ≃ Fin ts.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) (ch : EdgeChoices)
    (hcert : solveChoices ch (.full ts) (.full cs) (.full cs)
      (certificateEdges cs cs ts (finCongr hn.symm) eb et) flag ≠ 0) : RowSquare p q := by
  apply rowSquare_domain hp hq hcs hts he ht hn hn' eb et flag
  rw [← contractionInteger_solve, contractionInteger_choices _ _ _ _ _ _ flag ch]
  exact hcert

end UniversalTensorSquare
end
end

end OAI
