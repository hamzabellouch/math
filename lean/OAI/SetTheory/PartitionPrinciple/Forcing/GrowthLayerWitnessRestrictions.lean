import OAI.SetTheory.PartitionPrinciple.Definability.TaggedGrowthLayerFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace CopyEmbeddingFamilyCode

theorem restrict_sources_iff
    {Qs rs μs L r μ t I Indices Maps S : ZFSet.{u}} (before : t ⊆ S) :
    CopyEmbeddingFamilyCode (graphRestriction S Qs) (graphRestriction S rs)
      (graphRestriction S μs) L r μ t I Indices Maps ↔
    CopyEmbeddingFamilyCode Qs rs μs L r μ t I Indices Maps := by
  constructor
  · intro code i hi s hs e P R V index map qField rField mField
    exact code i hi s hs e P R V index map
      (pair_mem_graphRestriction.2 ⟨qField, before hs⟩)
      (pair_mem_graphRestriction.2 ⟨rField, before hs⟩)
      (pair_mem_graphRestriction.2 ⟨mField, before hs⟩)
  · intro code i hi s hs e P R V index map qField rField mField
    exact code i hi s hs e P R V index map
      (pair_mem_graphRestriction.1 qField).1 (pair_mem_graphRestriction.1 rField).1
      (pair_mem_graphRestriction.1 mField).1

end CopyEmbeddingFamilyCode

namespace CopyImageCoverCode

theorem restrict_sources_iff
    {Qs L t I parts Indices Maps S : ZFSet.{u}} (before : t ⊆ S) :
    CopyImageCoverCode (graphRestriction S Qs) L t I parts Indices Maps ↔
      CopyImageCoverCode Qs L t I parts Indices Maps := by
  constructor
  · intro code i hi s hs e P x hx index map qField part
    exact code i hi s hs e P x hx index map (pair_mem_graphRestriction.2 ⟨qField, before hs⟩) part
  · intro code i hi s hs e P x hx index map qField part
    exact code i hi s hs e P x hx index map (pair_mem_graphRestriction.1 qField).1 part

end CopyImageCoverCode

namespace ComponentImageCoverCode

theorem restrict_sources_iff
    {Qs L t I Components Indices Maps S : ZFSet.{u}} (before : t ⊆ S) :
    ComponentImageCoverCode (graphRestriction S Qs) L t I Components Indices Maps ↔
      ComponentImageCoverCode Qs L t I Components Indices Maps := by
  constructor
  · intro code i hi s hs e P x hx index map qField component
    exact code i hi s hs e P x hx index map
      (pair_mem_graphRestriction.2 ⟨qField, before hs⟩) component
  · intro code i hi s hs e P x hx index map qField component
    exact code i hi s hs e P x hx index map (pair_mem_graphRestriction.1 qField).1 component

end ComponentImageCoverCode

namespace CopyLayerCode

theorem restrict_sources_iff
    {Qs rs μs L r μ birth t I parts Indices Maps W N injection S : ZFSet.{u}}
    (before : t ⊆ S) :
    CopyLayerCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t I parts Indices Maps W N injection ↔
    CopyLayerCode Qs rs μs L r μ birth t I parts Indices Maps W N injection := by
  constructor
  · intro code
    exact ⟨code.small, code.indices, code.maps,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).1 code.embedding,
      code.cover, (CopyImageCoverCode.restrict_sources_iff before).1 code.inCopy⟩
  · intro code
    exact ⟨code.small, code.indices, code.maps,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).2 code.embedding,
      code.cover, (CopyImageCoverCode.restrict_sources_iff before).2 code.inCopy⟩

end CopyLayerCode

namespace SeparatedLayerCode

theorem restrict_sources_iff
    {Qs rs μs L r μ birth t I Indices Maps W Components F S : ZFSet.{u}}
    (before : t ⊆ S) :
    SeparatedLayerCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t I Indices Maps W Components F ↔
    SeparatedLayerCode Qs rs μs L r μ birth t I Indices Maps W Components F := by
  constructor
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).1 code.embedding,
      (ComponentImageCoverCode.restrict_sources_iff before).1 code.cover, code.separated⟩
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).2 code.embedding,
      (ComponentImageCoverCode.restrict_sources_iff before).2 code.cover, code.separated⟩

end SeparatedLayerCode

namespace GrowthLayerWitnessCode

theorem restrict_sources_iff {Qs rs μs L r μ birth t N z S : ZFSet.{u}}
    (before : t ⊆ S) :
    GrowthLayerWitnessCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t N z ↔ GrowthLayerWitnessCode Qs rs μs L r μ birth t N z := by
  simp only [GrowthLayerWitnessCode, CopyLayerCode.restrict_sources_iff before,
    SeparatedLayerCode.restrict_sources_iff before]

theorem restrict_sources {Qs rs μs L r μ birth t N z S : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z)
    (transitive : setTransitive S) (ht : t ∈ S) :
    GrowthLayerWitnessCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t N z :=
  (restrict_sources_iff (fun _ hs => transitive t ht _ hs)).2 code

end GrowthLayerWitnessCode
end PartitionPilot.Forcing

end

end OAI
