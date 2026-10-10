import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ColorBoundary
import OAI.Topology.ArtinGroups.Complexes.ScalarKernel
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistModern

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J T:Type u} [Fintype I] [Fintype J] [Fintype T]
  [DecidableEq I] [DecidableEq J] [DecidableEq T]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_minimal (E:BasedComplex Q (K:=K) I) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) : E.IsMinimal Q := by
  intro i j
  exact (pure_differential_linear Q E hE i j).1

noncomputable def pureLayerSelf (E:BasedComplex Q (K:=K) I) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) :
    ChainIsomorphism Q E (E.pureLayer Q (pure_minimal Q E hE) q) := by
  let e:=reindexChainIsomorphism Q (E.pureLayer Q (pure_minimal Q E hE) q) (allPureIndex Q E q hE)
  have he:(E.pureLayer Q (pure_minimal Q E hE) q).reindex Q (allPureIndex Q E q hE)=E := by
    apply ext_placement_differential Q <;> rfl
  rw [he] at e
  exact e.symm Q

noncomputable def HomotopyEquivalence.ofPure
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q) :
    ChainIsomorphism Q E F :=
  ((pureLayerSelf Q E hE).trans Q
    (e.pureLayer Q (pure_minimal Q E hE) (pure_minimal Q F hF) q)).trans Q
      ((pureLayerSelf Q F hF).symm Q)

noncomputable def TermwiseSplitInjection.trans
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J} {G:BasedComplex Q (K:=K) T}
    (a:TermwiseSplitInjection Q E F) (b:TermwiseSplitInjection Q F G) :
    TermwiseSplitInjection Q E G where
  inclusion:=Map.comp Q a.inclusion b.inclusion
  retraction:=b.retraction*a.retraction
  split:=by
    change (a.inclusion.matrix*b.inclusion.matrix)*(b.retraction*a.retraction)=_
    rw [Matrix.mul_assoc,← Matrix.mul_assoc b.inclusion.matrix,b.split,← Matrix.mul_assoc]
    exact (congrArg (fun X=>X*a.retraction) (mul_projectiveIdentity Q a.inclusion.entries)).trans a.split

noncomputable def ChainIsomorphism.termwiseSplit
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:ChainIsomorphism Q E F) : TermwiseSplitInjection Q E F :=
  ⟨e.forward,e.backward.matrix,e.sourceEquation⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma pureMap_zero_off_colors
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) {q:ℤ} (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (U:Set V) (hs:∀ i,(E.placement i).color∈U)
    (i:I) (j:J) (hj:(F.placement j).color∉U) : f.matrix i j=0 := by
  rw [map_coefficient_entry Q f (pureMap_coefficient Q f q hE hF)]
  have hne:(F.placement j).color≠(E.placement i).color:=fun h=>hj (h.symm ▸ hs i)
  change (f.matrix i j).vertex (F.placement j).color • _=0
  rw [entry_vertex_left_support Q f.entries i j _ hne,zero_smul]

noncomputable def TermwiseSplitInjection.colorTarget
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (a:TermwiseSplitInjection Q E F) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) (hF:∀ j,(F.placement j).level=q)
    (U:Set V) (hs:∀ i,(E.placement i).color∈U)
    (hb:∀ j,(F.placement j).color∉colorBoundary Q U) :
    TermwiseSplitInjection Q E (colorRestriction Q F U hF hb) where
  inclusion:=Map.comp Q a.inclusion (blockProjectionMap Q F
    {j:J | (F.placement j).color∈U} (pure_color_block Q F U hF hb))
  retraction:=a.retraction.submatrix Subtype.val id
  split:=by
    apply Matrix.ext
    intro i j
    change (∑ k:{k:J // (F.placement k).color∈U},
      (a.inclusion.matrix*blockProjection Q F {j:J | (F.placement j).color∈U}) i k * a.retraction k j)=_
    rw [mul_blockProjection Q F {j:J | (F.placement j).color∈U} _ _ a.inclusion.entries,← a.split]
    change (∑ k:{k:J // (F.placement k).color∈U},a.inclusion.matrix i k*a.retraction k j)=
      ∑ k:J,a.inclusion.matrix i k*a.retraction k j
    apply Fintype.sum_of_injective (Subtype.val : {k:J // (F.placement k).color∈U}→J) Subtype.val_injective
    · intro k hk
      have hn:(F.placement k).color∉U:=fun h=>hk ⟨⟨k,h⟩,rfl⟩
      rw [pureMap_zero_off_colors Q a.inclusion hE hF U hs i k hn,zero_mul]
    · intro k;rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
