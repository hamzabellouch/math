import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomInternalSupport
import OAI.Topology.ArtinGroups.Complexes.PureUpperBoundariesZero

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_total_hom_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    totalChainDimension Q E F (k-l) + totalChainDimension Q E F (k-l+2) +
      totalHomDimension Q E F (k-l+1) =
    totalChainDimension Q E F (k-l+1) + totalHomDimension Q E F (k-l) +
      totalHomDimension Q F E (l-k) := by
  have hp (v : ℤ) := pure_hom_euler Q E F hE hF (n := k-l-v) (v := v) (by omega)
  have he (v : ℤ) :
      Module.finrank K (homSpace Q E F (k-l-v) v) +
        Module.finrank K (homSpace Q E F (k-l+2-v) v) + homDimension Q E F (k-l+1-v) v =
      Module.finrank K (homSpace Q E F (k-l+1-v) v) +
        homDimension Q E F (k-l-v) v + homDimension Q E F (k-l+2-v) v := by
    have hh := hp v
    rw [← homDimension_dual Q E F (k-l-v+2) v] at hh
    have h₁ : k-l-v+1=k-l+1-v := by omega
    have h₂ : k-l-v+2=k-l+2-v := by omega
    rw [h₁,h₂] at hh
    exact hh
  have hs := Finset.sum_congr (s₁ := homInternalSupport Q E F) (s₂ := homInternalSupport Q E F)
    rfl (fun v _ => he v)
  simp only [Finset.sum_add_distrib] at hs
  change totalChainDimension Q E F (k-l) + totalChainDimension Q E F (k-l+2) +
    totalHomDimension Q E F (k-l+1) = totalChainDimension Q E F (k-l+1) +
    totalHomDimension Q E F (k-l) + totalHomDimension Q E F (k-l+2) at hs
  rw [totalHomDimension_dual Q E F (k-l+2)] at hs
  have h : 2-(k-l+2)=l-k := by omega
  rw [h] at hs
  exact hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
