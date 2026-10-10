import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStoredPreparedFamilyActions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def certificateBasisGraph (J nodes N k : ZFSet.{u}) : ZFSet.{u} :=
  let bases := M.groundSmallSubsets nodes ZFSet.omega
  let functions := M.groundRelations nodes N
  let tail := ZFSet.prod bases functions
  relationCompose J tail bases
    (relationCompose J (M.supportedEqualityCertificateBound nodes N) tail k
      (productSecond (M.groundPower nodes) tail))
    (productFirst bases functions)

theorem certificateBasisGraph_function {J nodes N k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k) :
    ZFSet.IsFunc J (M.groundSmallSubsets nodes ZFSet.omega)
      (M.certificateBasisGraph J nodes N k) :=
  relationCompose_function_of_subset
    (relationCompose_function_of_subset function (productSecond_function _ _) (fun _ h => h))
    (productFirst_function _ _) (fun _ h => h)

theorem pair_mem_certificateBasisGraph {J nodes N k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (z B : ZFSet.{u}) :
    ZFSet.pair z B ∈ M.certificateBasisGraph J nodes N k ↔
      ∃ F f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  dsimp only [certificateBasisGraph]
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, tail, _, first, projected⟩
    obtain ⟨B', hB, f, hf, equal⟩ := (mem_productFirst _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, c, _, edge, projected⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨F, hF, tail', ht, equal⟩ := (mem_productSecond _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨F, f, edge⟩
  · rintro ⟨F, f, edge⟩
    have bound := ZFSet.pair_mem_prod.1 (function.1 edge)
    have fields := ZFSet.pair_mem_prod.1 bound.2
    have tail := ZFSet.pair_mem_prod.1 fields.2
    exact ⟨bound.1, tail.1, _, fields.2,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bound.1, fields.2, _, bound.2, edge,
          (mem_productSecond _ _ _).2 ⟨F, fields.1, _, fields.2, rfl⟩⟩,
      (mem_productFirst _ _ _).2 ⟨B, tail.1, f, tail.2, rfl⟩⟩

theorem certificateBasisGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (hk : k ∈ M.sets) :
    M.certificateBasisGraph J nodes N k ∈ M.sets := by
  have hBases := M.groundSmallSubsets_mem powers separation hNodes omega
  have hFunctions := M.groundRelations_mem pairing unions powers separation hNodes hN
  have hTail := M.prod_mem pairing unions powers separation hBases hFunctions
  exact M.relationCompose_mem pairing unions powers separation hJ hTail hBases
    (M.relationCompose_mem pairing unions powers separation hJ
      (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hN omega)
      hTail hk (M.productSecond_mem pairing unions powers separation
        (M.groundPower_mem powers hNodes) hTail))
    (M.productFirst_mem pairing unions powers separation hBases hFunctions)

theorem certificateUsedSupports_eq_basisUnion {J nodes N k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k) :
    certificateUsedSupports nodes k = (relationImage J
      (M.groundSmallSubsets nodes ZFSet.omega) (M.certificateBasisGraph J nodes N k)).sUnion := by
  apply ZFSet.ext
  intro v
  rw [mem_certificateUsedSupports, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨_, z, F, B, f, edge, member⟩
    have bound := ZFSet.pair_mem_prod.1 (function.1 edge)
    have hB := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 bound.2).2).1
    exact ⟨B, (mem_relationImage _ _ _ _).2
      ⟨hB, z, bound.1, (M.pair_mem_certificateBasisGraph function z B).2 ⟨F, f, edge⟩⟩, member⟩
  · rintro ⟨B, hB, member⟩
    obtain ⟨hB, z, _, edge⟩ := (mem_relationImage _ _ _ _).1 hB
    obtain ⟨F, f, original⟩ := (M.pair_mem_certificateBasisGraph function z B).1 edge
    exact ⟨((M.mem_groundSmallSubsets _ _ _).1 hB).2.1 member, z, F, B, f, original, member⟩

theorem certificateUsedSupports_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hk : k ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (smallJ : M.groundEmbeddable J ZFSet.omega) :
    certificateUsedSupports nodes k ∈ M.sets ∧
      M.groundEmbeddable (certificateUsedSupports nodes k) ZFSet.omega := by
  have omega := M.omega_mem separation infinite
  have hBases := M.groundSmallSubsets_mem powers separation hNodes omega
  have hGraph := M.certificateBasisGraph_mem pairing unions powers separation hJ hNodes hN omega hk
  have graphFunction := M.certificateBasisGraph_function function
  have hRange := M.relationImage_mem separation hJ hBases hGraph
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hJ hBases omega hGraph graphFunction smallJ
  rw [M.certificateUsedSupports_eq_basisUnion function]
  exact ⟨M.union_mem unions hRange,
    M.groundCountable_family_union pairing unions powers separation infinite choice hRange rangeSmall
      (fun B hB => ((M.mem_groundSmallSubsets _ _ _).1
        ((mem_relationImage _ _ _ _).1 hB).1).2.2)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
