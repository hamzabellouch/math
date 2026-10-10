import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomInternalSupport
import OAI.Topology.ArtinGroups.Harmonic.PlacementLevelFiberSum

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A W I J K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [Fintype J]
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype V] [DecidableEq A] in
lemma totalHomDimension_of_reading (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (f:GeneratorPlacement W→₀ℕ) (α:W)
    (he:∀n v,homDimension Q E F n v=f ⟨α,n,v-1⟩) (t:ℤ) :
    totalHomDimension Q E F t=f.mapDomain (fun p=>(p.color,p.level)) (α,t-1) := by
  rw [totalHomDimension,placementLevel_fiber_sum]
  rw [← Finset.sum_filter_ne_zero (homInternalSupport Q E F)]
  refine Finset.sum_bij (fun v _=>⟨α,t-v,v-1⟩) ?_ ?_ ?_ ?_
  · intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hs,hv⟩
    refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_,rfl,?_⟩
    · rwa [← he]
    · change t-v+(v-1)=t-1
      omega
  · intro a ha b hb hh
    have h:=congrArg GeneratorPlacement.internal hh
    dsimp only at h
    omega
  · rintro ⟨β,n,u⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
    dsimp only at hc
    subst β
    change n+u=t-1 at hd
    have hnv:t-(u+1)=n:=by omega
    have huv:u+1-1=u:=by omega
    have hnz:homDimension Q E F (t-(u+1)) (u+1)≠0:=by
      rw [hnv,he,huv]
      exact Finsupp.mem_support_iff.mp hs
    refine ⟨u+1,Finset.mem_filter.mpr ⟨?_,hnz⟩,?_⟩
    · by_contra hv
      exact hnz (homDimension_off_internal_support Q E F _ _ hv)
    · simp only [hnv,huv]
  · intro v hv
    exact he _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
