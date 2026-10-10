import OAI.SetTheory.PartitionPrinciple.Forcing.GrowthLayerWitnessRestrictions

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem graphRestriction_eq_of_entries {S f g : ZFSet.{u}}
    (entries : ∀ s ∈ S, ∀ y, ZFSet.pair s y ∈ f ↔ ZFSet.pair s y ∈ g) :
    graphRestriction S f = graphRestriction S g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨s, hs, y, rfl, entry⟩ := mem_graphRestriction.1 member
    exact pair_mem_graphRestriction.2 ⟨(entries s hs y).1 entry, hs⟩
  · intro member
    obtain ⟨s, hs, y, rfl, entry⟩ := mem_graphRestriction.1 member
    exact pair_mem_graphRestriction.2 ⟨(entries s hs y).2 entry, hs⟩

namespace GrowthLayerWitnessCode

theorem congr_sources_below_iff
    {Qs rs μs Qs' rs' μs' L r μ birth t N z : ZFSet.{u}}
    (spaces : graphRestriction t Qs = graphRestriction t Qs')
    (orders : graphRestriction t rs = graphRestriction t rs')
    (meets : graphRestriction t μs = graphRestriction t μs') :
    GrowthLayerWitnessCode Qs rs μs L r μ birth t N z ↔
      GrowthLayerWitnessCode Qs' rs' μs' L r μ birth t N z := by
  have self : t ⊆ t := fun _ h => h
  rw [← restrict_sources_iff self, ← restrict_sources_iff (Qs := Qs') self]
  rw [spaces, orders, meets]

theorem congr_sources_below
    {Qs rs μs Qs' rs' μs' L r μ birth t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z)
    (spaces : graphRestriction t Qs = graphRestriction t Qs')
    (orders : graphRestriction t rs = graphRestriction t rs')
    (meets : graphRestriction t μs = graphRestriction t μs') :
    GrowthLayerWitnessCode Qs' rs' μs' L r μ birth t N z :=
  (congr_sources_below_iff spaces orders meets).1 code

theorem congr_source_entries
    {Qs rs μs Qs' rs' μs' L r μ birth t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z)
    (spaces : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ Qs ↔ ZFSet.pair s y ∈ Qs')
    (orders : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ rs ↔ ZFSet.pair s y ∈ rs')
    (meets : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ μs ↔ ZFSet.pair s y ∈ μs') :
    GrowthLayerWitnessCode Qs' rs' μs' L r μ birth t N z :=
  code.congr_sources_below (graphRestriction_eq_of_entries spaces)
    (graphRestriction_eq_of_entries orders) (graphRestriction_eq_of_entries meets)

end GrowthLayerWitnessCode

end PartitionPilot.Forcing

end

end OAI
