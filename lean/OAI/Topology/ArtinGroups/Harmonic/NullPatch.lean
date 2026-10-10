import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin
open Matrix

attribute [local instance] Classical.propDecidable
variable {V:Type*}

lemma null_patch [Fintype V] {C:Matrix V V ℝ} (hsym:∀ i j,C i j=C j i)
    (hoff:∀ i j,i≠j→C i j≤0) (I J:Set V) (hJI:J⊆I) (c μ:V→ℝ)
    (hc:∀ i∈I,(C *ᵥ c) i=0)
    (hext:∀ v,(v∈I ∧ v∉J) ∨ (v∉I ∧ ∃ u∈I,C v u<0)→μ v=c v) :
    ∀ j∈J,(C *ᵥ (fun v=>if v∈J then c v else μ v)) j=0 := by
  intro j hj
  rw [← hc j (hJI hj)]
  apply Finset.sum_congr rfl
  intro v _
  change C j v*(if v∈J then c v else μ v)=C j v*c v
  by_cases hv:v∈J
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    by_cases hi:v∈I
    · rw [hext v (Or.inl ⟨hi,hv⟩)]
    · by_cases hn:C v j<0
      · rw [hext v (Or.inr ⟨hi,j,hJI hj,hn⟩)]
      · have hn':C v j=0:=le_antisymm (hoff v j (fun he=>hi (he ▸ hJI hj))) (le_of_not_gt hn)
        rw [hsym j v,hn',zero_mul,zero_mul]

lemma color_region_exterior (I J:Set V) (c μ:V→ℝ)
    (hc:∀ v,v∉I→c v=0) (hext:∀ v,v∈I→v∉J→μ v=c v) :
    ∀ v,v∉J→(if v∈I then μ v else 0)=c v := by
  intro v hv
  by_cases hi:v∈I
  · rw [ite_eq_left hi,hext v hi hv]
  · rw [ite_eq_right hi,hc v hi]

end HarmonicArtin

end OAI
