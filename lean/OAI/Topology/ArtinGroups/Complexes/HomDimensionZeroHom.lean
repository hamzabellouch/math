import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InitialProjective

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma homDimension_zero_of_homSpace_zero {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (h : homSpace Q E F n v = ⊥) : homDimension Q E F n v = 0 := by
  have hd := homDimension_le_homSpace Q E F n v
  rw [h] at hd
  simp only [finrank_bot] at hd
  exact Nat.eq_zero_of_le_zero hd

omit [DecidableEq A] in
lemma initial_homDimension_nonzero_cochain (α β : V) (n v : ℤ) (hn : n ≠ 0) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = 0 :=
  homDimension_zero_of_homSpace_zero Q _ _ n v
    (initial_homSpace_nonzero_cochain Q α β n v hn)

omit [DecidableEq A] in
lemma initial_homDimension_orthogonal {α β : V} (h : OrthogonalVertices Q α β) (n v : ℤ) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = 0 :=
  homDimension_zero_of_homSpace_zero Q _ _ n v (initial_homSpace_orthogonal Q h n v)

lemma initial_homDimension_other_internal (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (hv₀ : v ≠ 0) (hv₂ : v ≠ 2) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q α) n v = 0 :=
  homDimension_zero_of_homSpace_zero Q _ _ n v
    (initial_homSpace_other_internal Q hn α n v hv₀ hv₂)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
