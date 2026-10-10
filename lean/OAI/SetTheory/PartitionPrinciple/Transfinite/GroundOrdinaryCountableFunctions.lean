import OAI.SetTheory.PartitionPrinciple.Geometry.GroundOrdinarySubmodelReflection

namespace OAI

section

namespace PartitionPilot.Forcing.GroundSequenceReflection
open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {U : ZFSet.{u}}

theorem countable_domain_function (reflection : GroundSequenceReflection M N U)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (included : M.sets ⊆ N.sets) {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hU : U ∈ M.sets)
    (small : M.groundEmbeddable A ZFSet.omega)
    (hf : f ∈ N.sets) (function : ZFSet.IsFunc A U f) : f ∈ M.sets := by
  classical
  by_cases nonempty : A.Nonempty
  · obtain ⟨e, he, enumeration, onto⟩ := M.groundCountable_enumeration
      pairing unions powers separation infinite hA nonempty small
    have omega := M.omega_mem separation infinite
    let sequence := relationCompose ZFSet.omega A U e f
    have sequenceFunction : ZFSet.IsFunc ZFSet.omega U sequence :=
      relationCompose_function_of_subset enumeration function (fun _ member => member)
    have sequenceGround := reflection sequence
      (N.relationCompose_mem pairingN unionsN powersN separationN
        (included omega) (included hA) (included hU) (included he) hf) sequenceFunction
    have recovered : relationCompose A ZFSet.omega U
        (relationConverse ZFSet.omega A e) sequence = f := by
      apply ZFSet.ext
      intro z
      constructor
      · intro member
        obtain ⟨a, ha, n, hn, v, _, rfl, inverse, value⟩ :=
          (mem_relationCompose _ _ _ _ _ z).1 member
        have na := ((pair_mem_relationConverse ZFSet.omega A e n a).1 inverse).2.2
        obtain ⟨_, _, a', _, na', av⟩ := (pair_mem_relationCompose _ _ _ _ _ n v).1 value
        obtain ⟨x, _, unique⟩ := enumeration.2 n hn
        have equal : a' = a := (unique a' na').trans (unique a na).symm
        exact equal ▸ av
      · intro member
        obtain ⟨a, ha, v, hv, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
        obtain ⟨n, hn, entry⟩ := onto a ha
        exact (pair_mem_relationCompose _ _ _ _ _ a v).2
          ⟨ha, hv, n, hn, (pair_mem_relationConverse ZFSet.omega A e n a).2 ⟨hn, ha, entry⟩,
            (pair_mem_relationCompose _ _ _ _ _ n v).2 ⟨hn, hv, a, ha, entry, member⟩⟩
    rw [← recovered]
    exact M.relationCompose_mem pairing unions powers separation hA omega hU
      (M.relationConverse_mem pairing unions powers separation omega hA he) sequenceGround
  · have empty : f = ∅ := by
      apply ZFSet.ext
      intro z
      constructor
      · intro member
        obtain ⟨a, ha, _, _, _⟩ := ZFSet.mem_prod.1 (function.1 member)
        exact False.elim (nonempty ⟨a, ha⟩)
      · intro member
        exact False.elim (ZFSet.notMem_empty z member)
    rw [empty]
    exact M.empty_mem ⟨A, hA⟩

end PartitionPilot.Forcing.GroundSequenceReflection



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)

theorem ordinaryExtension_countableDomainFunction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) {A U : ZFSet.{u}} (hA : A ∈ M.sets) (hU : U ∈ M.sets)
    (domainSmall : M.groundEmbeddable A ZFSet.omega)
    (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {f : ZFSet.{u}} (hf : f ∈ (M.ordinaryExtension s H).sets)
    (function : ZFSet.IsFunc A U f) : f ∈ M.sets := by
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice carrier order small hU closed H genericCoded genericFormula
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  exact reflection.countable_domain_function pairing unions powers separation infinite
    zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1 zf.2.1
    (M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H)
    hA hU domainSmall hf function

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
