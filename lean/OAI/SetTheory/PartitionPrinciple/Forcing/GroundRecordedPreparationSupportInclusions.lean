import OAI.SetTheory.PartitionPrinciple.Definability.GroundPreparationEventSupportGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCertificateBasisUnions

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparationUsedSupportUnion (nodes E events : ZFSet.{u}) : ZFSet.{u} :=
  (relationImage ZFSet.omega (M.groundPower nodes)
    (M.preparationUsedSupportSequence nodes E events)).sUnion

theorem preparationUsedSupportUnion_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {nodes E events : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (whole : events ∈ M.sets) (function : ZFSet.IsFunc ZFSet.omega E events)
    (certificates : ∀ i event, ZFSet.pair i event ∈ events → event = ∅ ∨
      ∃ alpha r k enumerations J N,
        event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
        J ∈ M.sets ∧ N ∈ M.sets ∧ k ∈ M.sets ∧
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k ∧
        M.groundEmbeddable J ZFSet.omega) :
    M.preparationUsedSupportUnion nodes E events ∈ M.sets ∧
      M.groundEmbeddable (M.preparationUsedSupportUnion nodes E events) ZFSet.omega := by
  have omega := M.omega_mem separation infinite
  let g := M.preparationUsedSupportSequence nodes E events
  have grounded := M.preparationUsedSupportSequence_ground_function pairing unions powers separation
    hNodes hE omega whole function
  have valueSmall {i support : ZFSet.{u}} (edge : ZFSet.pair i support ∈ g) :
      M.groundEmbeddable support ZFSet.omega := by
    obtain ⟨event, eventEdge, rfl⟩ :=
      (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).1 edge
    rcases certificates i event eventEdge with idle | active
    · rw [idle, preparationEventUsedSupports_idle]
      exact M.empty_groundEmbeddable ZFSet.omega ⟨nodes, hNodes⟩
    · obtain ⟨alpha, r, k, enumerations, J, N, rfl, hJ, hN, hk, selected, smallJ⟩ := active
      rw [preparationEventUsedSupports_active]
      exact (M.certificateUsedSupports_ground_countable pairing unions powers separation infinite choice
        hJ hNodes hN hk selected smallJ).2
  let bases := M.groundSmallSubsets nodes ZFSet.omega
  have narrowed : ZFSet.IsFunc ZFSet.omega bases g := by
    refine ⟨?_, grounded.2.2⟩
    intro z hz
    obtain ⟨i, hi, support, hs, rfl⟩ := ZFSet.mem_prod.1 (grounded.2.1 hz)
    have fields := (M.mem_groundPower nodes support).1 hs
    exact ZFSet.pair_mem_prod.2 ⟨hi, (M.mem_groundSmallSubsets nodes ZFSet.omega support).2
      ⟨fields.1, fields.2, valueSmall hz⟩⟩
  have equal : relationImage ZFSet.omega (M.groundPower nodes) g =
      relationImage ZFSet.omega bases g := by
    apply ZFSet.ext
    intro support
    rw [mem_relationImage, mem_relationImage]
    constructor
    · rintro ⟨_, i, hi, edge⟩
      exact ⟨(ZFSet.pair_mem_prod.1 (narrowed.1 edge)).2, i, hi, edge⟩
    · rintro ⟨_, i, hi, edge⟩
      exact ⟨(ZFSet.pair_mem_prod.1 (grounded.2.1 edge)).2, i, hi, edge⟩
  change (relationImage ZFSet.omega (M.groundPower nodes) g).sUnion ∈ M.sets ∧
    M.groundEmbeddable (relationImage ZFSet.omega (M.groundPower nodes) g).sUnion ZFSet.omega
  rw [equal]
  exact M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    (M.groundSmallSubsets_mem powers separation hNodes omega) hNodes grounded.1 narrowed
    (fun B hB => ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).2.1)
    (fun B hB => ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).2.2)

theorem mem_preparationUsedSupportUnion
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) (v : ZFSet.{u}) :
    v ∈ M.preparationUsedSupportUnion nodes E events ↔
      v ∈ nodes ∧ ∃ i ∈ ZFSet.omega, ∃ alpha r k enumerations z F B f,
        ZFSet.pair i (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) ∈ events ∧
          ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B := by
  rw [preparationUsedSupportUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨support, hs, member⟩
    obtain ⟨_, i, hi, edge⟩ := (mem_relationImage _ _ _ _).1 hs
    obtain ⟨event, eventEdge, rfl⟩ :=
      (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).1 edge
    obtain ⟨hv, alpha, r, k, enumerations, rfl, z, F, B, f, certificate, inside⟩ := ZFSet.mem_sep.1 member
    exact ⟨hv, i, hi, alpha, r, k, enumerations, z, F, B, f, eventEdge, certificate, inside⟩
  · rintro ⟨hv, i, hi, alpha, r, k, enumerations, z, F, B, f, eventEdge, certificate, inside⟩
    let event := ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))
    let support := preparationEventUsedSupports nodes event
    have edge := (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).2
      ⟨event, eventEdge, rfl⟩
    have hs := (pair_mem_relationCompose _ _ _ _ _ _ _).1 edge |>.2.1
    exact ⟨support, (mem_relationImage _ _ _ _).2 ⟨hs, i, hi, edge⟩,
      ZFSet.mem_sep.2 ⟨hv, alpha, r, k, enumerations, rfl, z, F, B, f, certificate, inside⟩⟩

theorem preparationUsedSupportUnion_subset
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) :
    M.preparationUsedSupportUnion nodes E events ⊆ nodes := by
  intro v member
  exact ((M.mem_preparationUsedSupportUnion separation hNodes hE function v).1 member).1

theorem recordedCertificateUsedSupports_subset
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events)
    {i alpha r k enumerations : ZFSet.{u}}
    (edge : ZFSet.pair i (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) ∈ events) :
    certificateUsedSupports nodes k ⊆ M.preparationUsedSupportUnion nodes E events := by
  intro v member
  obtain ⟨hv, z, F, B, f, certificate, inside⟩ :=
    (mem_certificateUsedSupports nodes k v).1 member
  exact (M.mem_preparationUsedSupportUnion separation hNodes hE function v).2
    ⟨hv, i, (ZFSet.pair_mem_prod.1 (function.1 edge)).1,
      alpha, r, k, enumerations, z, F, B, f, edge, certificate, inside⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
