import OAI.SetTheory.PartitionPrinciple.Geometry.GrowthLayerSourceCongruence
import OAI.SetTheory.PartitionPrinciple.Geometry.TemplateHeightRangeCodes

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem MeetEmbeddingCode.restrictTarget {A L Q rA rL μA μL e : ZFSet.{u}}
    (code : MeetEmbeddingCode A L rA rL μA μL e)
    (values : ∀ x y, ZFSet.pair x y ∈ e → y ∈ Q) :
    MeetEmbeddingCode A Q rA (heightOrderRestriction Q rL) μA
      (graphRestriction (ZFSet.prod Q Q) μL) e := by
  refine ⟨⟨⟨?_, code.injection.function.2⟩, code.injection.injective⟩, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (code.injection.function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, values x y hz⟩
  · intro x y x' y' lower first second
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨code.monotone x y x' y' lower first second, values x x' first, values y y' second⟩
  · intro x y z x' y' z' meet first second third
    exact pair_mem_graphRestriction.2
      ⟨code.map_meet x y z x' y' z' meet first second third,
        ZFSet.pair_mem_prod.2 ⟨values x x' first, values y y' second⟩⟩

def CodedGrowthLayer.restrictBirth
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (meet : MeetOrderCode L r μ) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ (graphRestriction L birth) t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D ground small
      (fun x hx entry => cover x hx (pair_mem_graphRestriction.1 entry).1)
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    exact .copies I parts groundI small groundParts index e earlier groundCopy embedding
      (fun x hx entry => cover x hx (pair_mem_graphRestriction.1 entry).1) inCopy
  | separated I index e earlier groundCopy embedding component cover separated =>
    let original (x : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ graphRestriction L birth}) :
        {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
      ⟨x.val, x.property.1, (pair_mem_graphRestriction.1 x.property.2).1⟩
    refine .separated I index e earlier groundCopy embedding (fun x => component (original x))
      (fun x => cover (original x)) ?_
    intro x y different
    rcases separated (original x) (original y) different with
      ⟨z, a, entry, born, before⟩ | ⟨z, hz, a, born, before, between⟩
    · exact Or.inl ⟨z, a, entry, pair_mem_graphRestriction.2
        ⟨born, (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2⟩, before⟩
    · exact Or.inr ⟨z, hz, a, pair_mem_graphRestriction.2 ⟨born, hz⟩, before, between⟩

end PartitionPilot.Forcing

end

end OAI
