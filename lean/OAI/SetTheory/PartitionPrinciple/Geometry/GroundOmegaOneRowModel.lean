import OAI.SetTheory.PartitionPrinciple.Models.GroundInternalRowChoice

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

noncomputable def groundOmegaOne : ZFSet.{u} :=
  Classical.choose (M.exists_groundHartogs pairing unions powers separation collection
    (M.omega_mem separation infinite))

theorem groundOmegaOne_spec :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    C ∈ M.sets ∧ ordinalSetProperty C ∧
      (∀ A : ZFSet.{u}, A ∈ C ↔ A ∈ M.sets ∧ ordinalSetProperty A ∧
        M.groundEmbeddable A ZFSet.omega) ∧ ¬ M.groundEmbeddable C ZFSet.omega :=
  Classical.choose_spec (M.exists_groundHartogs pairing unions powers separation collection
    (M.omega_mem separation infinite))

theorem groundOmegaOne_eq_code_rank :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    C = ordinalCode (ZFSet.rank C) :=
  ordinalSetProperty_eq_code_rank _
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.1

theorem groundOmegaOne_nonempty :
    (M.groundOmegaOne pairing unions powers separation collection infinite).Nonempty := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  exact ⟨∅, (spec.2.2.1 ∅).2
    ⟨M.empty_mem ⟨ZFSet.omega, M.omega_mem separation infinite⟩, ordinalSetProperty_empty,
      M.empty_groundEmbeddable ZFSet.omega ⟨ZFSet.omega, M.omega_mem separation infinite⟩⟩⟩

theorem groundOmegaOne_successor {A : ZFSet.{u}}
    (hA : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite) :
    insert A A ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨hAM, ordinal, small⟩ := (spec.2.2.1 A).1 hA
  exact (spec.2.2.1 _).2 ⟨M.insert_mem pairing unions hAM hAM,
    ordinalSetProperty_succ ordinal,
    M.groundEmbeddable_insert pairing unions powers separation infinite hAM hAM small⟩

theorem groundOmegaOne_countable_bound
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (subset : R ⊆ M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ B ∈ M.groundOmegaOne pairing unions powers separation collection infinite,
      ∀ A ∈ R, A ∈ B := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have ordinals : ∀ A ∈ R, ordinalSetProperty A := fun A hA => ((spec.2.2.1 A).1 (subset hA)).2.1
  have membersSmall : ∀ A ∈ R, M.groundEmbeddable A ZFSet.omega :=
    fun A hA => ((spec.2.2.1 A).1 (subset hA)).2.2
  have hU := M.union_mem unions hR
  have ordU := ordinalSetProperty_sUnion ordinals
  have smallU := M.groundCountable_family_union pairing unions powers separation infinite choice
    hR small membersSmall
  have uC := (spec.2.2.1 (⋃₀ R)).2 ⟨hU, ordU, smallU⟩
  refine ⟨insert (⋃₀ R) (⋃₀ R),
    M.groundOmegaOne_successor pairing unions powers separation collection infinite uC, ?_⟩
  intro A hA
  have included : A ⊆ ⋃₀ R := fun x hx => ZFSet.mem_sUnion.2 ⟨A, hA, hx⟩
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff A).1 (ordinals A hA)
  obtain ⟨b, eqB⟩ := (ordinalSetProperty_iff (⋃₀ R)).1 ordU
  rw [eqA, eqB] at included ⊢
  rw [← ordinalCode_succ, mem_ordinalCode_iff]
  exact Order.lt_succ_iff.2 ((ordinalCode_subset_iff a b).1 included)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

theorem exists_internalRow_ZF_not_choice_groundOmegaOne
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G)
    (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (unbounded : ∀ B : L, ∃ i : L, ¬ i ≤ B)
    (countableBound : ∀ A ∈ M.sets, A ⊆ s.carrier → M.groundEmbeddable A ZFSet.omega →
      ∃ D : L, ∀ i : L, s.encode i ∈ A → i ≤ D)
    (separate : ∀ B D : L, B ≤ D → ∃ g : G, g ∈ a.principalFix B ∧
      ∀ x : L, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier
      (M.groundOmegaOne pairing unions powers separation collection infinite))
      (natSetCode 2) ZFSet.omega)) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    let hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : L) directed
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
        (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
        SetFormula.choice Fin.elim0 := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  exact M.exists_internalRow_ZF_not_choice a s b
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    directed unbounded countableBound separate small pairing unions powers separation collection infinite
    groundChoice hL spec.1 hG order graph spec.2.2.2 p

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
