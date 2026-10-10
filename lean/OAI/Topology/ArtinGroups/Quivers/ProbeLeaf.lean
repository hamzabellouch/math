import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorArray2
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type} (Q:ReversibleQuiver V A)

lemma probe_source_leaf {a:ProbeArrow V A} {α:V} {b:Bool}
    (h:(probeQuiver Q).source a=.inr (α,b)) : (probeQuiver Q).target a=.inl α := by
  rcases a with a|⟨v,c,d⟩
  · exact (Sum.inl_ne_inr h).elim
  · cases d
    · exact (Sum.inl_ne_inr h).elim
    · have he:(v,c)=(α,b):=Sum.inr.inj h
      cases he
      rfl

lemma probe_target_leaf {a:ProbeArrow V A} {α:V} {b:Bool}
    (h:(probeQuiver Q).target a=.inr (α,b)) : (probeQuiver Q).source a=.inl α := by
  have hh:=probe_source_leaf Q (a:=(probeQuiver Q).reverse a) (by rw [source_reverse]; exact h)
  rwa [target_reverse] at hh

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma probe_differential_row_zero (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (hc:∀j,(E.placement j).color≠.inl α)
    (hf:∀j,(E.placement j).color=.inr (α,b)→(E.placement j).cochain=0)
    (i:I) (hi:(E.placement i).color=.inr (α,b)) (j:I) : E.differential i j=0 := by
  apply (pathCoordinates R).injective
  funext p
  rw [coordinates_zero]
  by_contra hp
  have hs:=coordinates_corner R (E.entries.1 i j) (E.entries.2 i j) hp
  have hdeg:(E.placement j).cochain=(E.placement i).cochain+1 := by
    by_contra h
    exact hp (by rw [(E.degree i j).1 h,coordinates_zero])
  rcases p with v|a|v
  · have hj:(E.placement j).color=.inr (α,b):=hs.2.symm.trans (hs.1.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega
  · have hh:=probe_source_leaf Q (hs.1.trans hi)
    exact hc j (hs.2.symm.trans hh)
  · have hj:(E.placement j).color=.inr (α,b):=hs.2.symm.trans (hs.1.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega

lemma probe_differential_col_zero (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (hc:∀j,(E.placement j).color≠.inl α)
    (hf:∀j,(E.placement j).color=.inr (α,b)→(E.placement j).cochain=0)
    (i:I) (hi:(E.placement i).color=.inr (α,b)) (j:I) : E.differential j i=0 := by
  apply (pathCoordinates R).injective
  funext p
  rw [coordinates_zero]
  by_contra hp
  have hs:=coordinates_corner R (E.entries.1 j i) (E.entries.2 j i) hp
  have hdeg:(E.placement i).cochain=(E.placement j).cochain+1 := by
    by_contra h
    exact hp (by rw [(E.degree j i).1 h,coordinates_zero])
  rcases p with v|a|v
  · have hj:(E.placement j).color=.inr (α,b):=hs.1.symm.trans (hs.2.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega
  · have hh:=probe_target_leaf Q (hs.2.trans hi)
    exact hc j (hs.1.symm.trans hh)
  · have hj:(E.placement j).color=.inr (α,b):=hs.1.symm.trans (hs.2.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega

lemma classGeneratorArray_initial (α:ProbeVertex V) (p:GeneratorPlacement (ProbeVertex V)) :
    classGeneratorArray R (initialClass R (K:=K) α) p=if p=⟨α,0,0⟩ then 1 else 0 := by
  rw [initialClass,classGeneratorArray_of_minimal R _ (show (initialProjective R α).IsMinimal R from
    fun i j=>rfl)]
  change (initialProjective R α).generatorArray R p=_
  rw [generatorArray]
  simp only [initialProjective,Finset.univ_unique,Finset.sum_singleton,Finsupp.single_apply,eq_comm]

lemma generatorArray_placement_pos (E:BasedComplex R (K:=K) I) (i:I) :
    0<E.generatorArray R (E.placement i) := by
  rw [generatorArray_apply]
  change 0<Nat.card {j:I // E.placement j=E.placement i}
  have : Nonempty {j:I // E.placement j=E.placement i}:=⟨⟨i,rfl⟩⟩
  exact Nat.card_pos

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
