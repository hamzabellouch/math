import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightHomeomorph

namespace OAI

namespace HarmonicArtin
open Topology
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P : Type u} [PartialOrder P]

noncomputable instance finiteWeightsCompact [Finite P] : CompactSpace (OrderWeights P) := by
  let _ := Fintype.ofFinite P
  let C := {c : Finset P // IsChain (· ≤ ·) (↑c : Set P) ∧ c.Nonempty}
  let f := fun c : C => orderWeightsOfChain (finiteChainOrder c.val c.property.1 c.property.2)
  have cover : (Set.univ : Set (OrderWeights P)) = ⋃ c : C, Set.range (f c) := by
    apply Set.Subset.antisymm
    · intro w _
      let c : C := ⟨w.weights.support, (fun p hp q hq _ => w.chain p hp q hq),w.support_nonempty⟩
      apply Set.mem_iUnion.mpr
      refine ⟨c,carrierSimplex c.val c.property.1 c.property.2 w (Finset.Subset.refl _),?_⟩
      exact carrierSimplex_reconstruct c.val c.property.1 c.property.2 w _
    · exact Set.subset_univ _
  apply isCompact_univ_iff.mp
  rw [cover]
  exact isCompact_iUnion fun c => isCompact_range (chainWeightsChart_continuous _)

lemma weightFiniteInclusion_closedEmbedding (A : Set P) (hA : A.Finite) :
    IsClosedEmbedding (weightMap (weightInclusion A)) := by
  let : Finite A := hA.to_subtype
  exact (weightMap_continuous _).isClosedEmbedding
    (weightMap_injective _ Subtype.val_injective)

lemma weightRestrict_continuous_finite {X : Type v} [TopologicalSpace X]
    (A : Set P) (hA : A.Finite) (f : C(X,OrderWeights P))
    (hf : ∀ x, ∀ p ∈ (f x).weights.support, p ∈ A) :
    Continuous (fun x => weightRestrict A (f x) (hf x)) := by
  apply (weightFiniteInclusion_closedEmbedding A hA).isEmbedding.isInducing.continuous_iff.mpr
  exact f.continuous.congr fun x => (weightRestrict_map A (f x) (hf x)).symm

theorem compact_map_finite_carrier {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f : C(X,OrderWeights P)) :
    ∃ (A : Set P) (_ : A.Finite) (g : C(X,OrderWeights A)),
      (weightMapContinuous (weightInclusion A)).comp g = f := by
  let A := weightCarrier (Set.range f)
  have hA : A.Finite := weightCarrier_finite_of_isCompact (isCompact_range f.continuous)
  have hf : ∀ x, ∀ p ∈ (f x).weights.support, p ∈ A := by
    intro x p hp
    exact ⟨f x,⟨x,rfl⟩,hp⟩
  let g : C(X,OrderWeights A) :=
    ⟨fun x => weightRestrict A (f x) (hf x),weightRestrict_continuous_finite A hA f hf⟩
  refine ⟨A,hA,g,?_⟩
  apply ContinuousMap.ext
  intro x
  exact weightRestrict_map A (f x) (hf x)

theorem compact_map_factors_cover {X : Type v} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} (B : ι → Set P)
    (hB : ∀ A : Set P, A.Finite → ∃ i, A ⊆ B i)
    (f : C(X,OrderWeights P)) :
    ∃ i, ∃ g : C(X,OrderWeights (B i)),
      (weightMapContinuous (weightInclusion (B i))).comp g = f := by
  obtain ⟨A,hA,g,hg⟩ := compact_map_finite_carrier f
  obtain ⟨i,hi⟩ := hB A hA
  refine ⟨i,(weightMapContinuous (weightSubset A (B i) hi)).comp g,?_⟩
  apply ContinuousMap.ext
  intro x
  change weightMap (weightInclusion (B i)) (weightMap (weightSubset A (B i) hi) (g x)) = f x
  rw [weightMap_comp]
  exact congrArg (fun h : C(X,OrderWeights P) => h x) hg

end HarmonicArtin

end OAI
