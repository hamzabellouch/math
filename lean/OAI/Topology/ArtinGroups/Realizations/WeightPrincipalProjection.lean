import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightAffineValue

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite Topology

attribute [local instance] Classical.decEq Classical.propDecidable
variable {P : Type*} [PartialOrder P]

noncomputable def weightPrincipalProjection : (Σ p : P,OrderWeights (Set.Iic p)) → OrderWeights P :=
  fun x => weightMap (weightInclusion (Set.Iic x.1)) x.2

lemma weightPrincipalProjection_continuous : Continuous (weightPrincipalProjection (P := P)) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact weightMap_continuous (weightInclusion (Set.Iic p))

lemma weightPrincipalProjection_surjective : Function.Surjective (weightPrincipalProjection (P := P)) := by
  intro w
  exact ⟨⟨weightMax w,weightRestrict (Set.Iic (weightMax w)) w (le_weightMax w)⟩,
    weightRestrict_map _ w (le_weightMax w)⟩

theorem weightPrincipalProjection_quotient : IsQuotientMap (weightPrincipalProjection (P := P)) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨weightPrincipalProjection_surjective,fun A => ⟨fun h => h.preimage weightPrincipalProjection_continuous,?_⟩⟩
  intro h
  rw [orderWeights_isClosed_iff]
  intro n x
  let c := nerveChain x
  let a := c (Fin.last n.len)
  let d : Fin (n.len+1) →o Set.Iic a :=
    ⟨fun i => ⟨c i,c.monotone (Fin.le_last i)⟩,fun _ _ h => c.monotone h⟩
  have hc : Continuous (fun z : Convexity.StdSimplex ℝ (Fin (n.len+1)) =>
      (⟨a,orderWeightsOfChain d z⟩ : Σ p : P,OrderWeights (Set.Iic p))) :=
    (continuous_sigmaMk (i := a)).comp (chainWeightsChart_continuous d)
  have he : ∀ z,weightPrincipalProjection (⟨a,orderWeightsOfChain d z⟩ : Σp,OrderWeights (Set.Iic p)) =
      orderWeightsOfChain (nerveChain x) z := by
    intro z
    exact weightMap_chain (weightInclusion (Set.Iic a)) d z
  simpa only [Set.preimage_preimage,Function.comp_def,he] using h.preimage hc

end HarmonicArtin

end OAI
