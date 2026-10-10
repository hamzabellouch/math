import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellUnion

namespace OAI

namespace HarmonicArtin
open Topology

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {S : Type u} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

noncomputable def sourceSalvettiProjection : SalvettiCover M → SourceSalvetti M :=
  sourceUniversalProjection M ∘ nerveWeightsHomeomorph

theorem sourceSalvettiProjection_covering : IsCoveringMap (sourceSalvettiProjection M) :=
  (sourceUniversalProjection_quotientCovering M).isCoveringMap.comp_homeomorph
    nerveWeightsHomeomorph

theorem sourceSalvettiProjection_surjective : Function.Surjective (sourceSalvettiProjection M) :=
  (sourceUniversalProjection_quotientCovering M).surjective.comp
    nerveWeightsHomeomorph.surjective

theorem sourceSalvettiProjection_universal :
    IsCoveringMap (sourceSalvettiProjection M) ∧
    Function.Surjective (sourceSalvettiProjection M) ∧
    SimplyConnectedSpace (SalvettiCover M) ∧
    ContractibleSpace (SalvettiCover M) := by
  let := salvetti_cover_contractible M
  exact ⟨sourceSalvettiProjection_covering M,sourceSalvettiProjection_surjective M,
    inferInstance,salvetti_cover_contractible M⟩

noncomputable def sourceFundamentalGroupEquiv (x : SourceSalvetti M) :
    FundamentalGroup (SourceSalvetti M) x ≃* Artin M := by
  letI := liftedWeights_contractible M
  let p := sourceUniversalProjection_quotientCovering M
  let e : (sourceUniversalProjection M) ⁻¹' {x} :=
    ⟨(p.surjective x).choose,(p.surjective x).choose_spec⟩
  exact (p.fundamentalGroupEquiv e).trans (MulEquiv.inv' (Artin M)).symm

end HarmonicArtin

end OAI
