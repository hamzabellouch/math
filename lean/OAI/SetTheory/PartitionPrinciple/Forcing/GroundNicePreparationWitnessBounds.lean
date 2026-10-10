import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCertificateProfileImageFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundRelations_mono {A B C D : ZFSet.{u}} (left : A ⊆ C) (right : B ⊆ D) :
    M.groundRelations A B ⊆ M.groundRelations C D := by
  intro f member
  obtain ⟨ground, shape⟩ := (M.mem_groundRelations A B f).1 member
  refine (M.mem_groundRelations C D f).2 ⟨ground, ?_⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact ZFSet.pair_mem_prod.2 ⟨left ha, right hb⟩

theorem supportedEqualityCertificateBound_mono {nodes N W : ZFSet.{u}} (inside : N ⊆ W) :
    M.supportedEqualityCertificateBound nodes N ⊆ M.supportedEqualityCertificateBound nodes W := by
  intro z hz
  obtain ⟨F, hF, tail, htail, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 htail
  exact ZFSet.pair_mem_prod.2 ⟨hF, ZFSet.pair_mem_prod.2
    ⟨hB, M.groundRelations_mono (fun _ h => h) inside hf⟩⟩

theorem synchronizedEnumerationBound_mono {nodes N W : ZFSet.{u}} (inside : N ⊆ W) :
    M.synchronizedEnumerationBound nodes N ⊆ M.synchronizedEnumerationBound nodes W := by
  intro z hz
  obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 hz
  exact ZFSet.pair_mem_prod.2 ⟨he, M.groundRelations_mono (fun _ h => h) inside hn⟩

noncomputable def preparationWitnessBound (nodes T Q : ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  ZFSet.prod Q (ZFSet.prod
    (M.groundRelations W (M.supportedEqualityCertificateBound nodes W))
    (M.groundRelations W (M.synchronizedEnumerationBound nodes W)))

theorem mem_preparationWitnessBound (nodes T Q r k enumerations : ZFSet.{u}) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q ↔
      r ∈ Q ∧ k ∈ M.groundRelations (M.groundRelations T Q)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q)) ∧
      enumerations ∈ M.groundRelations (M.groundRelations T Q)
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) := by
  simp only [preparationWitnessBound, ZFSet.pair_mem_prod]

theorem preparationWitnessBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes T Q : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.preparationWitnessBound nodes T Q ∈ M.sets := by
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  exact M.prod_mem pairing unions powers separation hQ
    (M.prod_mem pairing unions powers separation
      (M.groundRelations_mem pairing unions powers separation hW
        (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega))
      (M.groundRelations_mem pairing unions powers separation hW
        (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)))

theorem preparationWitness_mem_of_local {nodes T Q J N r k enumerations : ZFSet.{u}}
    (requestBound : J ⊆ M.groundRelations T Q) (nameBound : N ⊆ M.groundRelations T Q)
    (hr : r ∈ Q) (hk : k ∈ M.sets) (he : enumerations ∈ M.sets)
    (certificates : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (enumerated : ZFSet.IsFunc J (M.synchronizedEnumerationBound nodes N) enumerations) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q := by
  have localK := (M.mem_groundRelations J (M.supportedEqualityCertificateBound nodes N) k).2
    ⟨hk, certificates.1⟩
  have localE := (M.mem_groundRelations J (M.synchronizedEnumerationBound nodes N) enumerations).2
    ⟨he, enumerated.1⟩
  exact (M.mem_preparationWitnessBound nodes T Q r k enumerations).2
    ⟨hr, M.groundRelations_mono requestBound (M.supportedEqualityCertificateBound_mono nameBound) localK,
      M.groundRelations_mono requestBound (M.synchronizedEnumerationBound_mono nameBound) localE⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (T : ZFSet.{u}) (K : I → Subgroup G)

theorem niceSupportNameCodes_subset_groundRelations {Q : ZFSet.{u}} (carrier : s.carrier ⊆ Q) :
    M.niceSupportNameCodes a s T K ⊆ M.groundRelations T Q := by
  intro z member
  obtain ⟨ground, i, code⟩ := (M.mem_niceSupportNameCodes a s T K z).1 member
  have localBound := (M.mem_groundRelations T s.carrier z).2 ⟨ground, niceNameCode_subset a s code⟩
  exact M.groundRelations_mono (fun _ h => h) carrier localBound

theorem nicePreparationWitness_mem {nodes Q J r k enumerations : ZFSet.{u}}
    (carrier : s.carrier ⊆ Q) (requests : J ⊆ M.groundRelations T s.carrier)
    (hr : r ∈ Q) (hk : k ∈ M.sets) (he : enumerations ∈ M.sets)
    (certificates : ZFSet.IsFunc J
      (M.supportedEqualityCertificateBound nodes (M.niceSupportNameCodes a s T K)) k)
    (enumerated : ZFSet.IsFunc J
      (M.synchronizedEnumerationBound nodes (M.niceSupportNameCodes a s T K)) enumerations) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q :=
  M.preparationWitness_mem_of_local
    (fun _ h => M.groundRelations_mono (fun _ h => h) carrier (requests h))
    (M.niceSupportNameCodes_subset_groundRelations a s T K carrier)
    hr hk he certificates enumerated

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
