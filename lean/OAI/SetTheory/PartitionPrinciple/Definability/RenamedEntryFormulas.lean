import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProductActions

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def renamedChildFormula : SetFormula 4 :=
  ex (exConditions 3 (.conj (orderedPairFormula 2 1 0)
    (.conj (domainApplication uniformNameFormula (extend 4 Fin.elim0) 3)
      (binaryApplication uniformRenameFormula (extend 4 (extend 5 Fin.elim0)) 1 3))))

def renamedEntryFormula : SetFormula 4 :=
  ex (exConditions 3 (.conj (pairMembershipFormula 1 0 3)
    (ex (exConditions 5 (.conj (orderedPairFormula 4 1 0)
      (.conj (pairMembershipFormula 2 0 7)
        (.conj (domainApplication uniformNameFormula (extend 6 Fin.elim0) 1)
          (binaryApplication uniformRenameFormula (extend 6 (extend 7 Fin.elim0)) 3 1))))))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_renamedChildFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ : Name s) (hσ : σ.val ∈ M.sets) (p : P) (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets renamedChildFormula
      (extend (ZFSet.pair σ.val (s.encode p)) (extend y (renameParameters s f))) ↔
      y = (Name.rename s f σ).val := by
  let base := extend (ZFSet.pair σ.val (s.encode p)) (extend y (renameParameters s f))
  have hp := M.transitive carrier (s.encode_mem p)
  have hz := M.orderedPair_mem pairing hσ hp
  rw [renamedChildFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨r, shape, name, renamed⟩ := (M.realize_exConditions s 3 _ (extend x base) carrier rfl).1 rest
    let e := extend (s.encode r) (extend x base)
    have raw := (M.realize_orderedPairFormula pairing 2 1 0 e hz hx
      (M.transitive carrier (s.encode_mem r))).1 shape
    change ZFSet.pair σ.val (s.encode p) = ZFSet.pair x (s.encode r) at raw
    obtain ⟨sx, pr⟩ := ZFSet.pair_inj.1 raw
    have cond := s.injective pr
    subst x
    subst r
    rw [realize_domainApplication, map_extend, map_empty] at name
    have nameY := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier y hy).1 name
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
    have eq := (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph
      σ ⟨y, nameY⟩ hσ hy).1 renamed
    exact (congrArg Subtype.val eq).symm
  · intro eq
    subst y
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 3 _ (extend σ.val base) carrier rfl).2
    refine ⟨p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hp).2 rfl
    · rw [realize_domainApplication, map_extend, map_empty]
      exact (M.realize_uniformNameFormula s pairing unions powers separation collection carrier _ hy).2
        (Name.rename s f σ).property
    · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
      exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph
        σ (Name.rename s f σ) hσ hy).2 rfl

theorem realize_renamedEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets renamedEntryFormula (extend z (extend τ.val (renameParameters s f))) ↔
      z ∈ (Name.rename s f τ).val := by
  let base := extend z (extend τ.val (renameParameters s f))
  rw [renamedEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨p, old, rest⟩ := (M.realize_exConditions s 3 _ (extend x base) carrier rfl).1 rest
    have entry := (M.realize_pairMembershipFormula pairing 1 0 3
      (extend (s.encode p) (extend x base)) hx (M.transitive carrier (s.encode_mem p)) hτ).1 old
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ x p entry⟩
    obtain ⟨y, hy, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨q, shape, condition, name, renamed⟩ := (M.realize_exConditions s 5 _
      (extend y (extend (s.encode p) (extend x base))) carrier rfl).1 rest
    let e := extend (s.encode q) (extend y (extend (s.encode p) (extend x base)))
    have raw := (M.realize_orderedPairFormula pairing 4 1 0 e hz hy
      (M.transitive carrier (s.encode_mem q))).1 shape
    have cond := (M.realize_pairMembershipFormula pairing 2 0 7 e
      (M.transitive carrier (s.encode_mem p)) (M.transitive carrier (s.encode_mem q)) graph).1 condition
    have pq := (s.pair_mem_graph s f p q).1 cond
    rw [realize_domainApplication, map_extend, map_empty] at name
    have nameY := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier y hy).1 name
    let ν : Name s := ⟨y, nameY⟩
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
    have eq := (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph σ ν hx hy).1 renamed
    have member := (Name.entry_rename s f τ ν q).2 ⟨σ, p, entry, eq, pq⟩
    change z = ZFSet.pair y (s.encode q) at raw
    rw [raw]
    exact member
  · intro member
    obtain ⟨ν, q, rfl⟩ := Name.entries_cover (Name.rename s f τ) member
    obtain ⟨σ, p, entry, image, cond⟩ := (Name.entry_rename s f τ ν q).1 member
    have hσ := (M.nameDomain s).children hτ entry
    have hν := M.pair_left hz
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 3 _ (extend σ.val base) carrier rfl).2
    refine ⟨p, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 1 0 3 _ hσ
        (M.transitive carrier (s.encode_mem p)) hτ).2 entry
    · rw [realize_ex]
      refine ⟨ν.val, hν, ?_⟩
      apply (M.realize_exConditions s 5 _ (extend ν.val (extend (s.encode p) (extend σ.val base))) carrier rfl).2
      let e := extend (s.encode q) (extend ν.val (extend (s.encode p) (extend σ.val base)))
      refine ⟨q, ?_, ?_, ?_, ?_⟩
      · exact (M.realize_orderedPairFormula pairing 4 1 0 e hz hν
          (M.transitive carrier (s.encode_mem q))).2 rfl
      · exact (M.realize_pairMembershipFormula pairing 2 0 7 e
          (M.transitive carrier (s.encode_mem p)) (M.transitive carrier (s.encode_mem q)) graph).2
          ((s.pair_mem_graph s f p q).2 cond)
      · rw [realize_domainApplication, map_extend, map_empty]
        exact (M.realize_uniformNameFormula s pairing unions powers separation collection carrier ν.val hν).2 ν.property
      · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
        exact (M.realize_uniformRenameFormula s pairing unions powers separation collection carrier f graph σ ν hσ hν).2 image

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
