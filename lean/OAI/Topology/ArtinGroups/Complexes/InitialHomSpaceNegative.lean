import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma initial_homSpace_negative (α β : V) (n v : ℤ) (h : n + v < 0) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  by_cases hn : n = 0
  · apply le_antisymm _ bot_le
    intro f hf
    change f = 0
    apply Matrix.ext
    intro i j
    have hh : Homogeneous Q v (f i j) := by
      simpa only [initialProjective, add_zero, sub_zero] using (hf.2 i j).2
    have hv : v < 0 := by omega
    apply Zigzag.ext
    · exact hh.1 (by omega)
    · exact hh.2.1 (by omega)
    · exact hh.2.2 (by omega)
  · exact initial_homSpace_nonzero_cochain Q α β n v hn

lemma frameModel_negative_pair_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α β : V)
    (n v : ℤ) (h : n + v < 0) :
    homDimension Q (frameModel Q (K := K) hn M hM x α).complex
      (frameModel Q hn M hM x β).complex n v = 0 := by
  rw [frameModel, frameModel, minimalClassModel_homDimension, unfoldedFrame_homDimension]
  exact homDimension_zero_of_homSpace_zero Q _ _ n v (initial_homSpace_negative Q α β n v h)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
