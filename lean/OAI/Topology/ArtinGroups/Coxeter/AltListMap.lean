import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltList

namespace OAI

namespace HarmonicArtin.CoxeterExchange
lemma altList_map {B C : Type*} (f : B → C) (i j : B) (n : ℕ) :
    (altList i j n).map f=altList (f i) (f j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [altList_succ,List.map_cons,ih]
end HarmonicArtin.CoxeterExchange

end OAI
