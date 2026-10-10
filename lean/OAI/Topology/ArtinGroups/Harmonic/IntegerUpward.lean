import Mathlib

namespace OAI

namespace HarmonicArtin

lemma integer_upward {P:ℤ→Prop} (b d:ℤ)
    (low:∀ k,k<b→P k)
    (step:∀ k,b≤k→k<d→P (k-1)→P k) : ∀ k,k<d→P k := by
  intro k hk
  by_cases hb:k<b
  · exact low k hb
  · have go:∀ n,b-1≤n→ n<d→P n := by
      intro n hn
      refine Int.leInduction (m:=b-1) (motive:=fun n _=>n<d→P n) ?_ ?_ n hn
      · intro hn
        exact low (b-1) (by omega)
      · intro n hn ih hnd
        apply step (n+1) (by omega) hnd
        have h:=ih (by omega)
        simpa only [add_sub_cancel_right] using h
    exact go k (by omega) hk
end HarmonicArtin

end OAI
