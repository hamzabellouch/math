import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UnfoldedCartanSymm
import OAI.Topology.ArtinGroups.Complexes.ColorSupport
import OAI.Topology.ArtinGroups.Complexes.ColorReduction
import OAI.Topology.ArtinGroups.Complexes.ScalarKernel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem canonicalReducedWordLow_termwiseSplit (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    Nonempty (TermwiseSplitInjection Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex
      (minimalClassModel Q x).complex) := by
  obtain ⟨f,hm⟩:=canonicalReducedWordLow_monic Q hn U hU x q hlo hhi w hw hr
  have hp:=canonicalReducedWordLow_pure Q hn U hU x q hlo hhi w hw hr
  obtain ⟨g,_⟩:=pureMap_termwiseSplit Q _ _
    (fun i=>le_antisymm (hp.2 i) (hp.1 i)) (fun i=>le_antisymm (hhi i) (hlo i)) f hm
  exact ⟨g⟩

theorem canonicalReducedWordLow_multiplicity_le (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) (p:GeneratorPlacement V) :
    multiplicity Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex p ≤
      multiplicity Q (minimalClassModel Q x).complex p := by
  obtain ⟨f⟩:=canonicalReducedWordLow_termwiseSplit Q hn U hU x q hlo hhi w hw hr
  exact f.multiplicity_le Q p

theorem canonicalReducedWordLow_generator_bounds (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) (α:V) :
    0≤generatorVector Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex α ∧
      generatorVector Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex α≤
        generatorVector Q (minimalClassModel Q x).complex α := by
  obtain ⟨f⟩:=canonicalReducedWordLow_termwiseSplit Q hn U hU x q hlo hhi w hw hr
  exact ⟨generatorVector_nonneg Q _ α,f.generatorVector_le Q α⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
