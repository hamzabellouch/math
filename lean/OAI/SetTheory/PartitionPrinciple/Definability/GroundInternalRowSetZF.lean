import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInternalRowsInZF

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

theorem internalRowSetName_mem (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) :
    (M.internalRowSetName s C hL).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSetName_mem pairing unions powers separation collection infinite
    (M.nonbottom_carrier_mem s separation hL) hC ⊤

theorem eval_internalRowSetName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.eval {p | H.mem p} (M.internalRowSetName s C hL) =
        ZFSet.range (fun i : SetMembers s.nonbottom.carrier =>
          M.binaryGenericRow s.nonbottom.carrier C H (SetMembers.raw i)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H
  exact M.eval_binaryRowSetName s.nonbottom.carrier C ⊤ H H.top_mem

theorem internalRowSet_mem_symmetric_values
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      ZFSet.range (fun i : SetMembers s.nonbottom.carrier =>
        M.binaryGenericRow s.nonbottom.carrier C H (SetMembers.raw i)) ∈
        (act.symmetricDomain c (M.nameDomain c) (a.principalSupportFamily ⊥ directed)).values
          {p | H.mem p} := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c H
  exact (act.mem_symmetric_values c (M.nameDomain c) (a.principalSupportFamily ⊥ directed)
    {p | H.mem p} _).2 ⟨M.internalRowSetName s C hL,
    M.internalRowSetName_mem s C pairing unions powers separation collection infinite hL hC,
    M.internalRowSetName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed,
    M.eval_internalRowSetName s C hL H⟩

theorem exists_internalRow_ZF_with_rowSet
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
        M.binaryGenericRow s.nonbottom.carrier C H (SetMembers.raw i)) ∧
      ZFSet.range (fun i : SetMembers s.nonbottom.carrier =>
        M.binaryGenericRow s.nonbottom.carrier C H (SetMembers.raw i)) ∈
          (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ∀ i : {i : L // i ≠ ⊥}, M.binaryGenericRow s.nonbottom.carrier C H (s.encode i.val) ∈
        (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  obtain ⟨H, hp, ground, ordinary, symmetric, includes, zf, total, distinct⟩ :=
    M.exists_internalRow_ZF_with_distinct_rows a s b C directed small pairing unions powers
      separation collection infinite choice hL hC hG order graph uncountable p
  exact ⟨H, hp, ground, ordinary, symmetric, includes, zf, total, distinct,
    M.internalRowSet_mem_symmetric_values a s b C directed pairing unions powers separation collection
      infinite hL hC hG graph H,
    fun i => M.internalRow_mem_symmetric_values a s b C directed pairing unions powers separation
      collection infinite hL hC hG graph i H⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
