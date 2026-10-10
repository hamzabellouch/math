import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProductActions

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u
variable {I G : Type u} [Group G]

noncomputable def supportBasisCode (b : Presentation I) (t : Presentation G)
    (K : I → Subgroup G) : ZFSet.{u} := (b.product t).subset (fun z => z.2 ∈ K z.1)

theorem pair_mem_supportBasisCode (b : Presentation I) (t : Presentation G)
    (K : I → Subgroup G) (i : I) (g : G) :
    ZFSet.pair (b.encode i) (t.encode g) ∈ supportBasisCode b t K ↔ g ∈ K i :=
  (b.product t).encode_mem_subset (fun z => z.2 ∈ K z.1) (i, g)

theorem finalSupportFamily_basis (Label : Type 1) (H : Subgroup (MainStage.OrdinalRun.FinalActor Label)) :
    (MainStage.OrdinalRun.supportFamily Label).mem H ↔
      ∃ C, (MainStage.OrdinalRun.finalAction Label).fixSubgroup C ≤ H := Iff.rfl

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.SetFormula

def nameSupportFormula : SetFormula 6 :=
  allConditions 3 (imp (pairMembershipFormula 2 0 5)
    (atomicApplication nameActionFormula (extend 3 (extend 6 Fin.elim0)) 0 1 1))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem realize_nameSupportFormula (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (hi : b.encode i ∈ M.sets) (τ : Name s) (hτ : τ.val ∈ M.sets) :
    Realize M.sets nameSupportFormula
      (extend τ.val (extend (b.encode i) (extend s.carrier (extend t.carrier
        (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      K i ≤ a.stabilizer s τ := by
  let env := extend τ.val (extend (b.encode i) (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))))
  rw [nameSupportFormula, M.realize_allConditions t 3 _ env group rfl]
  change (∀ g, Realize M.sets _ _) ↔ ∀ g, g ∈ K i → a.act s g τ = τ
  apply forall_congr'
  intro g
  let e := extend (t.encode g) env
  rw [realize_imp, M.realize_pairMembershipFormula pairing 2 0 5 e hi
    (M.transitive group (t.encode_mem g)) supports]
  change (ZFSet.pair (b.encode i) (t.encode g) ∈ supportBasisCode b t K → Realize M.sets _ e) ↔ _
  rw [pair_mem_supportBasisCode]
  apply forall_congr'
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  exact M.realize_nameActionFormula a s t pairing unions powers separation collection
    carrier group maps g τ τ hτ hτ

end PartitionPilot.Forcing.TransitiveGround

end OAI
