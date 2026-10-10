import Mathlib
import OAI.Topology.ArtinGroups.Functors.TermwiseSplitInjection
import OAI.Topology.ArtinGroups.Complexes.GeneratorArrayZeroCap

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

omit [DecidableEq A] in
lemma top_zero_of_probe_socle (y:FiniteHomotopyClass R (K:=K))
    (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (l q:ℤ)
    (hy:ClassLowerBound R l y) (hx:ClassCapOn Q x U q)
    (hsupport:∀i α,((minimalClassModel R y).complex.placement i).color=.inl α→α∈U)
    (hz:∀n v,n+v=q-l+2→classHomDimension R n v y (classMap Q x)=0)
    (α:V) (d:ℤ) (hs:0<classLayerSocleDimension R l (.inl α) d y) :
    ∀c,classLayerTopDimension Q q α c x=0 := by
  let E:=minimalClassModel R y
  let F:=minimalClassModel Q x
  have hE:E.complex.IsMinimal R:=minimalClassModel_minimal R y
  have hF:F.complex.IsMinimal Q:=minimalClassModel_minimal Q x
  have hs':coefficientSocle R (E.complex.pureLayer R hE l) (.inl α) d≠⊥ := by
    intro h
    change 0<Module.finrank K (coefficientSocle R (E.complex.pureLayer R hE l) (.inl α) d) at hs
    rw [h,finrank_bot] at hs
    omega
  have hb:∀i j,(E.complex.placement i).color=((complex Q F.complex).placement j).color→
      ((complex Q F.complex).placement j).level-(E.complex.placement i).level≤q-l := by
    intro i j he
    have hc:=hsupport i (F.complex.placement j).color he
    have hi:=hy i
    have hj:=hx j hc
    change l≤(E.complex.placement i).level at hi
    change (F.complex.placement j).level≤q at hj
    change (F.complex.placement j).level-(E.complex.placement i).level≤q-l
    omega
  have hhom:∀n v,n+v=q-l+2→homDimension R E.complex (complex Q F.complex) n v=0 := by
    intro n v hnv
    have he:classOfComplex R E.complex=y:=minimalClassModel_class R y
    have hf:classOfComplex R (complex Q F.complex)=classMap Q x:=by
      rw [← classMap_complex]
      exact congrArg (classMap Q) (minimalClassModel_class Q x)
    change classHomDimension R n v (classOfComplex R _) (classOfComplex R _)=0
    erw [he,hf]
    exact hz n v hnv
  intro c
  have ht:=extremal_socle_forces_top_zero R E.complex (complex Q F.complex)
    hE (complex_minimal Q hF) l q hb hhom (.inl α) c d hs'
  erw [pureLayer_complex Q F.complex hF q,coefficientTopDual_complex] at ht
  change Module.finrank K (coefficientTopDual Q (F.complex.pureLayer Q hF q) α c)=0
  erw [ht,finrank_bot]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
