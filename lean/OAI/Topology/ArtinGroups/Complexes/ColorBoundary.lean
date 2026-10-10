import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual
import OAI.Topology.ArtinGroups.Complexes.BlockClosed

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_differential_arrow (E:BasedComplex Q (K:=K) I) {q:ℤ}
    (hp:∀ i,(E.placement i).level=q) {i j:I} (hne:E.differential i j≠0) :
    ∃ a:A,Q.source a=(E.placement i).color ∧ Q.target a=(E.placement j).color := by
  have hl:=pure_differential_linear Q E hp i j
  have ha:∃ a,(E.differential i j).arrow a≠0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply ext
    · exact hl.1
    · exact funext hn
    · exact hl.2
  obtain ⟨a,ha⟩:=ha
  exact ⟨a,coordinates_corner Q (E.entries.1 i j) (E.entries.2 i j)
    (p:=.inr (.inl a)) ha⟩

def colorBoundary (U:Set V) : Set V :=
  {v | v∉U ∧ ∃ a:A,Q.source a∈U ∧ Q.target a=v}

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_color_block (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    BlockClosed Q E {i | (E.placement i).color∈U} := by
  intro i j hn
  obtain ⟨a,hs,ht⟩:=pure_differential_arrow Q E hp hn
  change ((E.placement i).color∈U ↔ (E.placement j).color∈U)
  constructor
  · intro hi
    by_contra hj
    exact hb j ⟨hj,a,hs ▸ hi,ht⟩
  · intro hj
    by_contra hi
    apply hb i
    exact ⟨hi,Q.reverse a,by simpa only [Q.source_reverse,ht] using hj,
      by simpa only [Q.target_reverse] using hs⟩

noncomputable def colorRestriction (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    BasedComplex Q (K:=K) {i // (E.placement i).color∈U} :=
  blockRestriction Q E _ (pure_color_block Q E U hp hb)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_pure (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    ∀ i,((colorRestriction Q E U hp hb).placement i).level=q := fun i=>hp i

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_supported (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    ∀ i,((colorRestriction Q E U hp hb).placement i).color∈U := fun i=>i.property

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_generatorVector (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) (v:V) :
    generatorVector Q (colorRestriction Q E U hp hb) v=
      if v∈U then generatorVector Q E v else 0 := by
  rw [generatorVector_sum]
  change (∑ i:{i // (E.placement i).color∈U},
    if (E.placement i).color=v then (1:ℝ) else 0)=_
  rw [← Finset.sum_subtype (Finset.univ.filter fun i:I=>(E.placement i).color∈U)
    (by simp) (fun i:I=>if (E.placement i).color=v then (1:ℝ) else 0),
    Finset.sum_filter]
  split_ifs with hv
  · rw [generatorVector_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he:(E.placement i).color=v
    · simp only [he,hv,ite_true]
    · simp only [he,ite_false,ite_self]
  · apply Finset.sum_eq_zero
    intro i _
    by_cases he:(E.placement i).color=v
    · simp only [he,hv,ite_false]
    · simp only [he,ite_false,ite_self]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
