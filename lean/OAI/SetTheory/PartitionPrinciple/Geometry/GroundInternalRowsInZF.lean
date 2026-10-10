import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowNameCodes
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionZF

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

theorem exists_internalRow_ZF_with_distinct_rows
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega)) :
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
      ZFSet.IsFunc (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2)
        (M.countableGenericGraph (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) H) ∧
      Function.Injective (fun i : SetMembers s.nonbottom.carrier =>
        M.binaryGenericRow s.nonbottom.carrier C H (SetMembers.raw i)) := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  have hRows := M.nonbottom_carrier_mem s separation hL
  have hCoordinates := M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC
  have hAction := M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph
  have values : (natSetCode 2 : ZFSet.{u}).Nonempty :=
    ⟨natSetCode 0, (mem_two_iff _).2 (Or.inl rfl)⟩
  obtain ⟨H, hp, ground, ordinary, symmetric, includes, zf, total⟩ :=
    M.exists_countableFunction_ZF (a.rowCoordinates C) a
      (s.nonbottom.product (SetMembers.presentation C)) (natInitialPresentation 2) b s
      (⊥ : L) directed small pairing unions powers separation collection infinite
      hCoordinates (M.natSetCode_mem separation infinite 2) values hG hL hAction order graph p
  exact ⟨H, hp, ground, ordinary, symmetric, includes, zf, total,
    M.binaryGenericRows_injective pairing unions powers separation infinite choice
      hRows hC uncountable H ground⟩

theorem internalRowName_mem (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets)
    (i : {i : L // i ≠ ⊥}) : (M.internalRowName s C hL i).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowName_mem pairing unions powers separation collection infinite
    (M.nonbottom_carrier_mem s separation hL) hC ⊤ (s.encode i.val)
    (M.transitive hL (s.encode_mem i.val))

theorem eval_internalRowName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.eval {p | H.mem p} (M.internalRowName s C hL i) =
        M.binaryGenericRow s.nonbottom.carrier C H (s.encode i.val) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H
  exact M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem (s.encode i.val)

theorem internalRow_mem_symmetric_values
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      M.binaryGenericRow s.nonbottom.carrier C H (s.encode i.val) ∈
        (act.symmetricDomain c (M.nameDomain c) (a.principalSupportFamily ⊥ directed)).values
          {p | H.mem p} := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c H
  exact (act.mem_symmetric_values c (M.nameDomain c) (a.principalSupportFamily ⊥ directed)
    {p | H.mem p} _).2 ⟨M.internalRowName s C hL i,
    M.internalRowName_mem s C pairing unions powers separation collection infinite hL hC i,
    M.internalRowName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed i,
    M.eval_internalRowName s C hL i H⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
