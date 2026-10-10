import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPreparedWitnessSelections
import OAI.SetTheory.PartitionPrinciple.Forcing.PreparedWitnessCertificateGraphs

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparedSelectionProfiles (A stages Q nodes T selections : ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  let K := M.groundRelations W (M.supportedEqualityCertificateBound nodes W)
  let E := M.groundRelations W (M.synchronizedEnumerationBound nodes W)
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let witnesses := relationImage A L selections
  let certificates := relationImage witnesses K (preparedWitnessCertificateGraph stages Q K E)
  ⋃₀ relationImage certificates (M.groundPower (M.groundPower nodes))
    (M.certificateProfileImageFamily nodes W)

theorem preparedSelectionProfiles_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages packed nodes nodeOrder p A selections : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets) (hStages : stages ∈ M.sets)
    (hPacked : packed ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (data : RefinementDataHistory stages packed T)
    (selected : selections ⊆ M.preparedWitnessSelections rows T stages packed nodes p A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound nodes T (M.refinementHistoryForcing rows T stages packed))) selections ∈ M.sets)
    (small : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound nodes T (M.refinementHistoryForcing rows T stages packed))) selections) ZFSet.omega)
    (localData : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
      fields 10 = nodes ∧ fields 11 = nodeOrder ∧
      fields 14 ⊆ M.groundRelations T (M.refinementHistoryForcing rows T stages packed) ∧
      ∀ sourceRow sourceA,
        ZFSet.pair sourceRow sourceA ∈ M.refinementHistoryForcing rows T stages packed →
        M.storedPreparationRequests sourceA fields ∈ M.sets ∧
        M.groundEmbeddable (M.storedPreparationRequests sourceA fields) ZFSet.omega) :
    let Q := M.refinementHistoryForcing rows T stages packed
    let Profiles := M.preparedSelectionProfiles A stages Q nodes T selections
    Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
      (∀ F ∈ Profiles, MeetFilterCode nodes nodeOrder (canonicalMeetGraph nodes nodeOrder) F) ∧
      ∀ x alpha sourceRow sourceA k enumerations z F B f,
        ZFSet.pair x (ZFSet.pair alpha
          (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
        ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles := by
  let Q := M.refinementHistoryForcing rows T stages packed
  let W := M.groundRelations T Q
  let K := M.groundRelations W (M.supportedEqualityCertificateBound nodes W)
  let E := M.groundRelations W (M.synchronizedEnumerationBound nodes W)
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let witnesses := relationImage A L selections
  let projection := preparedWitnessCertificateGraph stages Q K E
  let certificates := relationImage witnesses K projection
  let images := relationImage certificates (M.groundPower (M.groundPower nodes))
    (M.certificateProfileImageFamily nodes W)
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hPacked omega
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hK := M.groundRelations_mem pairing unions powers separation hW
    (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega)
  have hE := M.groundRelations_mem pairing unions powers separation hW
    (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)
  have hProjection := M.preparedWitnessCertificateGraph_mem pairing unions powers separation hStages hQ hK hE
  have hCertificates := M.relationImage_mem separation whole hK hProjection
  have smallCertificates := M.groundEmbeddable_function_image pairing unions powers separation choice
    whole hK omega hProjection (preparedWitnessCertificateGraph_function stages Q K E) small
  have hFamily := M.certificateProfileImageFamily_mem pairing unions powers separation collection hNodes hW omega
  have hImageBound := M.groundPower_mem powers (M.groundPower_mem powers hNodes)
  have familyFunction := M.certificateProfileImageFamily_function pairing unions powers separation hNodes hW omega
  have hImages := M.relationImage_mem separation hCertificates hImageBound hFamily
  have smallImages := M.groundEmbeddable_function_image pairing unions powers separation choice
    hCertificates hImageBound omega hFamily familyFunction smallCertificates
  have certificateData (k : ZFSet.{u}) (member : k ∈ certificates) :
      ∃ J, J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧ J ⊆ W ∧
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k ∧
        ∀ F ∈ M.certificateProfileImage J nodes W k,
          MeetFilterCode nodes nodeOrder (canonicalMeetGraph nodes nodeOrder) F := by
    obtain ⟨_, y, hy, projected⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_, x, _hx, edge⟩ := (mem_relationImage _ _ _ _).1 hy
    obtain ⟨_, alpha, _ha, source, hs, enumerations, _he, rfl⟩ :=
      (pair_mem_preparedWitnessCertificateGraph stages Q K E y k).1 projected
    obtain ⟨sourceRow, _, sourceA, _, rfl⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages packed hs)
    obtain ⟨_, sourceCondition, _, _, _, fields, stored, _terms, nodeCarrier, _meet,
      _assignment, q, _hq, _cut, family⟩ := M.preparedWitnessSelection_entry data (selected edge)
    obtain ⟨_nodes, orderEq, nameBound, requests⟩ := localData alpha fields stored
    obtain ⟨hJ, smallJ⟩ := requests sourceRow sourceA sourceCondition
    have Jbound : M.storedPreparationRequests sourceA fields ⊆ W := by
      intro z hz
      apply nameBound
      rcases ZFSet.mem_union.1 hz with left | right
      · exact (mem_relationImage _ _ _ _).1 left |>.1
      · exact (mem_relationImage _ _ _ _).1 right |>.1
    refine ⟨_, hJ, smallJ, Jbound, family.1, ?_⟩
    intro F hF
    have aligned := family
    rw [nodeCarrier, orderEq] at aligned
    exact M.certificateProfileImage_meetFilter aligned hF
  have imagesSmall (image : ZFSet.{u}) (member : image ∈ images) :
      M.groundEmbeddable image ZFSet.omega := by
    obtain ⟨_, k, hk, edge⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_, rfl⟩ := (M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge
    obtain ⟨J, hJ, smallJ, Jbound, function, _filters⟩ := certificateData k hk
    rw [M.certificateProfileImage_eq_of_domain_subset function Jbound]
    exact (M.certificateProfileImage_mem_small pairing unions powers separation choice hJ hNodes hW
      (((M.mem_groundRelations _ _ k).1 ((mem_relationImage _ _ _ _).1 hk).1).1)
      omega function smallJ).2
  change (⋃₀ images) ∈ M.sets ∧ M.groundEmbeddable (⋃₀ images) ZFSet.omega ∧ _
  refine ⟨M.union_mem unions hImages,
    M.groundCountable_family_union pairing unions powers separation infinite choice hImages smallImages imagesSmall,
    ?_, ?_⟩
  · intro F member
    obtain ⟨image, hi, hF⟩ := ZFSet.mem_sUnion.1 member
    obtain ⟨_, k, hk, edge⟩ := (mem_relationImage _ _ _ _).1 hi
    obtain ⟨_, rfl⟩ := (M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge
    obtain ⟨J, _, _, Jbound, function, filters⟩ := certificateData k hk
    apply filters F
    exact M.certificateProfileImage_eq_of_domain_subset function Jbound ▸ hF
  · intro x alpha sourceRow sourceA k enumerations z F B f edge certificate
    have selectedEdge := selected edge
    dsimp only [preparedWitnessSelections, retainedPreparationSelections] at selectedEdge
    have bounded := (ZFSet.mem_sep.1 selectedEdge).1
    have pairBounds := ZFSet.pair_mem_prod.1 bounded
    have yBound := ZFSet.pair_mem_prod.1 pairBounds.2
    have outputBound := ZFSet.pair_mem_prod.1 yBound.2
    have tailBound := ZFSet.pair_mem_prod.1 outputBound.2
    have hk : k ∈ certificates := (mem_relationImage _ _ _ _).2 ⟨tailBound.1,
      _, (mem_relationImage _ _ _ _).2 ⟨pairBounds.2, x, pairBounds.1, edge⟩,
      (pair_mem_preparedWitnessCertificateGraph stages Q K E _ k).2
        ⟨tailBound.1, alpha, yBound.1, _, outputBound.1, enumerations, tailBound.2, rfl⟩⟩
    obtain ⟨J, _, _, Jbound, function, _⟩ := certificateData k hk
    have familyEdge := (M.pair_mem_certificateProfileImageFamily nodes W k _).2 ⟨tailBound.1, rfl⟩
    have imageBound := (ZFSet.pair_mem_prod.1 (familyFunction.1 familyEdge)).2
    refine ZFSet.mem_sUnion.2 ⟨_, (mem_relationImage _ _ _ _).2 ⟨imageBound, k, hk, familyEdge⟩, ?_⟩
    rw [M.certificateProfileImage_eq_of_domain_subset function Jbound]
    exact (M.mem_certificateProfileImage function F).2 ⟨z, B, f, certificate⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
