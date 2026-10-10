import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Level

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable

lemma placementLevel_fiber_sum {V:Type*} (f:GeneratorPlacement V→₀ℕ) (α:V) (d:ℤ) :
    f.mapDomain (fun p=>(p.color,p.level)) (α,d)=
      ∑ p ∈ f.support.filter (fun p=>p.color=α ∧ p.level=d), f p := by
  have h:=Finsupp.mapDomain_apply_eq_sum (fun p:GeneratorPlacement V=>(p.color,p.level)) f
    (a:=⟨α,d,0⟩)
  simp only [GeneratorPlacement.level,add_zero] at h
  apply h.trans
  apply Finset.sum_congr
  · ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hs,he⟩
      exact Finset.mem_filter.mpr ⟨hs,congrArg Prod.fst he,congrArg Prod.snd he⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
      exact Finset.mem_filter.mpr ⟨hs,Prod.ext hc hd⟩
  · intro p hp
    rfl

lemma placementLevel_dual {V:Type*} (f g:GeneratorPlacement V→₀ℕ) (α β:V)
    (he:∀ n u,f ⟨α,n,u⟩=g ⟨β,-n,-u⟩) (d:ℤ) :
    f.mapDomain (fun p=>(p.color,p.level)) (α,d)=
      g.mapDomain (fun p=>(p.color,p.level)) (β,-d) := by
  rw [placementLevel_fiber_sum,placementLevel_fiber_sum]
  refine Finset.sum_bij (fun p _ => ⟨β,-p.cochain,-p.internal⟩) ?_ ?_ ?_ ?_
  · rintro ⟨v,n,u⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
    dsimp only at hc
    subst v
    refine Finset.mem_filter.mpr ⟨?_,rfl,?_⟩
    · rw [Finsupp.mem_support_iff,← he]
      exact Finsupp.mem_support_iff.mp hs
    · change -n + -u = -d
      change n+u=d at hd
      omega
  · rintro ⟨v,n,u⟩ hp ⟨w,m,t⟩ hq hh
    rcases (Finset.mem_filter.mp hp).2 with ⟨hc,hd⟩
    rcases (Finset.mem_filter.mp hq).2 with ⟨kc,kd⟩
    dsimp only at hc kc
    have hn:=congrArg GeneratorPlacement.cochain hh
    have hu:=congrArg GeneratorPlacement.internal hh
    dsimp only at hn hu
    have hm:n=m:=by omega
    have ht:u=t:=by omega
    subst v; subst w; subst m; subst t
    rfl
  · rintro ⟨v,n,u⟩ hp
    rcases Finset.mem_filter.mp hp with ⟨hs,hc,hd⟩
    dsimp only at hc
    subst v
    refine ⟨⟨α,-n,-u⟩,Finset.mem_filter.mpr ⟨?_,rfl,?_⟩,?_⟩
    · rw [Finsupp.mem_support_iff,he,neg_neg,neg_neg]
      exact Finsupp.mem_support_iff.mp hs
    · change -n + -u=d
      change n+u= -d at hd
      omega
    · simp only [neg_neg]
  · rintro ⟨v,n,u⟩ hp
    have hc: v=α := (Finset.mem_filter.mp hp).2.1
    subst v
    exact he n u

end HarmonicArtin

end OAI
