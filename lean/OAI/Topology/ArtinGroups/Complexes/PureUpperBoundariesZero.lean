import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureHomSpaceHomogeneous
import OAI.Topology.ArtinGroups.Complexes.HomStep

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
lemma pure_upper_boundaries_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : k-l+2 < n+v) : homBoundaries Q E F n v = ⊥ := by
  have hb : homBoundaries Q E F n v ≤ homSpace Q E F n v :=
    (homBoundaries_le_homCycles Q E F n v).trans inf_le_left
  rw [homSpace_pure_total_degree_upper Q E F hE hF h] at hb
  exact le_antisymm hb bot_le

lemma pure_hom_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n+v=k-l) :
    Module.finrank K (homSpace Q E F n v) + Module.finrank K (homSpace Q E F (n+2) v) +
      homDimension Q E F (n+1) v =
    Module.finrank K (homSpace Q E F (n+1) v) + homDimension Q E F n v +
      homDimension Q F E (-(n+2)) (2-v) := by
  have h₀ := hom_exact_dimension Q E F n v
  have h₁ := hom_exact_dimension Q E F (n+1) v
  have h₂ := hom_exact_dimension Q E F (n+2) v
  rw [pure_coefficient_boundaries_zero Q E F hE hF h, finrank_bot] at h₀
  rw [pure_upper_boundaries_zero Q E F hE hF (n := n+2+1) (v := v) (by omega),
    finrank_bot] at h₂
  rw [homDimension_dual Q E F (n+2) v] at h₂
  have hn : n+1+1=n+2 := by omega
  rw [hn] at h₁
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
