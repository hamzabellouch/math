import Mathlib
import OAI.Topology.ArtinGroups.Quivers.VertexLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_homSpace_homogeneous (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v r : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l+r) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (i : I) (j : J) : Homogeneous Q r (f i j) := by
  by_cases hc : (F.placement j).cochain = (E.placement i).cochain + n
  · have he := hE i
    have ht := hF j
    dsimp only [GeneratorPlacement.level] at he ht
    have hh : v + (E.placement i).internal - (F.placement j).internal = r := by omega
    rw [← hh]
    exact (hf.2 i j).2
  · rw [(hf.2 i j).1 hc]
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma pure_homSpace_coefficient (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) : CoefficientMatrix Q f := by
  intro i j
  have hh := pure_homSpace_homogeneous Q E F hE hF (r := 0) (by omega) hf i j
  exact ⟨hh.2.1 (by norm_num), hh.2.2 (by norm_num)⟩

lemma pure_homSpace_linear (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l+1) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) : LinearMatrix Q f := by
  intro i j
  have hh := pure_homSpace_homogeneous Q E F hE hF h hf i j
  exact ⟨hh.1 (by norm_num), hh.2.2 (by norm_num)⟩

lemma pure_homSpace_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l+2) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) : TokenMatrix Q f := by
  intro i j
  have hh := pure_homSpace_homogeneous Q E F hE hF h hf i j
  exact ⟨hh.1 (by norm_num), hh.2.1 (by norm_num)⟩

lemma pure_coefficient_boundaries_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l) : homBoundaries Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨g, hg, rfl⟩ := hf
  rw [homSpace_pure_total_degree_lower Q E F hE hF (by omega)] at hg
  have hg' : g = 0 := hg
  rw [hg', map_zero]
  exact Submodule.zero_mem _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
