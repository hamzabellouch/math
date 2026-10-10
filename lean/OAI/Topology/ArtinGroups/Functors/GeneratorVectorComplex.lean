import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector
import OAI.Topology.ArtinGroups.Functors.ZigzagLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I:Type u} [Fintype I]
local notation "R" => probeQuiver Q

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
lemma generatorVector_complex (E:BasedComplex Q (K:=K) I) :
    generatorVector R (complex Q E)=Sum.elim (generatorVector Q E) (fun _=>0) := by
  classical
  funext v
  cases v with
  | inl v=>simp only [generatorVector_sum,complex,Function.comp_apply,placement,Sum.inl.injEq,Sum.elim_inl]
  | inr v=>simp only [generatorVector_sum,complex,Function.comp_apply,placement,Sum.inl_ne_inr,
      ite_false,Finset.sum_const_zero,Sum.elim_inr]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
