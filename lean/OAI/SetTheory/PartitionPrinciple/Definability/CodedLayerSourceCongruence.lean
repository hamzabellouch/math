import OAI.SetTheory.PartitionPrinciple.Geometry.GrowthLayerSourceCongruence

namespace OAI

section

namespace PartitionPilot.Forcing.CodedGrowthLayer
universe u

def congr_sources {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet Space' sourceOrder' sourceMeet' : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (spaces : ∀ s ∈ t, Space s = Space' s)
    (orders : ∀ s ∈ t, sourceOrder s = sourceOrder' s)
    (meets : ∀ s ∈ t, sourceMeet s = sourceMeet' s) :
    CodedGrowthLayer M Space' sourceOrder' sourceMeet' L r μ birth t :=
  layer.congr_sources_below spaces orders meets

end PartitionPilot.Forcing.CodedGrowthLayer

end

end OAI
