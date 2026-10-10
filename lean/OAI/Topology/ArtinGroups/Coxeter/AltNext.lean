import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltList

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.propDecidable
variable {S : Type*}

def altNext (i j : S) (n : ℕ) : S := if n % 2 = 0 then i else j

@[simp] lemma altNext_zero (i j : S) : altNext i j 0 = i := rfl

lemma altNext_succ (i j : S) (n : ℕ) : altNext i j (n+1) = altNext j i n := by
  unfold altNext
  split_ifs <;> first | rfl | omega

lemma altList_succ_append (i j : S) (n : ℕ) :
    altList i j (n+1) = altList i j n ++ [altNext i j n] := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    rw [altList_succ, ih j i, altList_succ, List.cons_append, altNext_succ]

end HarmonicArtin.CoxeterExchange

end OAI
