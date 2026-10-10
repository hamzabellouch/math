import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.RowSquareTools

namespace OAI

/-! Encoded Domains. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_vectors {n : ℕ} {p q cs ts : List ℕ}
    (hp : GoodRows p) (hq : GoodRows q) (hcs : GoodRows cs) (hts : GoodRows ts)
    (he : cs = transposeRows p ∨ cs = p) (ht : ts = transposeRows q)
    (hn : cs.sum = n) (hn' : ts.sum = n)
    (eb : Fin n ≃ Fin cs.sum) (et : Fin n ≃ Fin ts.sum)
    (flag : Finset (ℕ × ℕ × ℕ))
    (hcert : solveVectors n (.full ts) (.full cs) (.full cs)
      (certificateEdges cs cs ts (finCongr hn.symm) eb et) flag ≠ 0) : RowSquare p q := by
  apply rowSquare_domain hp hq hcs hts he ht hn hn' eb et flag
  simpa only [← solveVectors_encode, Domains.encode_full] using hcert

end UniversalTensorSquare
end
end

end OAI
