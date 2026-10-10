import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinalEnumerationFamilies

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem exists_groundSupportEnumerationChoices
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W →
      HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) tau) :
    ∃ supportChoice ∈ M.sets, ∃ B ∈ M.sets, ∃ enumerationChoice ∈ M.sets,
      ZFSet.IsFunc W b.carrier supportChoice ∧ ZFSet.IsFunc b.carrier B enumerationChoice ∧
      let selected := relationCompose W b.carrier B supportChoice enumerationChoice
      selected ∈ M.sets ∧ ZFSet.IsFunc W B selected ∧
      ∀ (tau : Name s) z, ZFSet.pair tau.val z ∈ selected →
        ∃ D : L, ZFSet.pair tau.val (b.encode D) ∈ supportChoice ∧
          ZFSet.pair (b.encode D) z ∈ enumerationChoice ∧
          d.principalFix D ≤ a.stabilizer s tau ∧
          ∃ delta ∈ M.sets, ∃ f ∈ M.sets, z = ZFSet.pair delta f ∧
            ordinalSetProperty delta ∧
            InjectionCode delta (relationFiber b.nonbottom.carrier
              (relationConverse b.carrier b.carrier b.conditionOrder) (b.encode D)) f ∧
            ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i ∈ delta, ZFSet.pair i (b.encode v) ∈ f := by
  have hNonbottom := M.nonbottom_carrier_mem b separation nodes
  let reverse := relationConverse b.carrier b.carrier b.conditionOrder
  have hReverse := M.relationConverse_mem pairing unions powers separation nodes nodes nodeOrder
  let fibers := M.relationFiberFamily b.carrier b.nonbottom.carrier reverse
  have hFibers : fibers ∈ M.sets := M.relationFiberFamily_mem pairing unions powers separation
    nodes hNonbottom hReverse
  have fibersFunction := M.relationFiberFamily_function separation nodes hNonbottom hReverse
  have hPower := M.groundPower_mem powers hNonbottom
  obtain ⟨B, hB, enumerations, hEnumerations, enumFunction, enumValues⟩ :=
    M.exists_groundOrdinalEnumerationFamily pairing unions powers separation collection choice
      (M.groundPower b.nonbottom.carrier) hPower
  let enumerationChoice := relationCompose b.carrier (M.groundPower b.nonbottom.carrier) B fibers enumerations
  have enumerationGround : enumerationChoice ∈ M.sets := M.relationCompose_mem pairing unions powers
    separation nodes hPower hB hFibers hEnumerations
  have enumerationFunction : ZFSet.IsFunc b.carrier B enumerationChoice :=
    relationCompose_function_of_subset fibersFunction enumFunction (fun _ h => h)
  obtain ⟨supportChoice, hSupportChoice, supportFunction, supported⟩ :=
    M.exists_groundNameSupportChoice a s t b d ⊥ directed pairing unions powers separation collection
      choice carrier group nodes supports maps W hW valid symmetric
  refine ⟨supportChoice, hSupportChoice, B, hB, enumerationChoice, enumerationGround,
    supportFunction, enumerationFunction, ?_⟩
  dsimp only
  refine ⟨M.relationCompose_mem pairing unions powers separation hW nodes hB hSupportChoice enumerationGround,
    relationCompose_function_of_subset supportFunction enumerationFunction (fun _ h => h), ?_⟩
  intro tau z entry
  obtain ⟨_, _, v, hv, supportEdge, enumEdge⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
  obtain ⟨D, rfl⟩ := (b.mem_carrier v).1 hv
  have fixes := (supported tau D supportEdge).2
  obtain ⟨_, _, ideal, _, idealEdge, chosen⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 enumEdge
  have idealEq := ((M.pair_mem_relationFiberFamily b.carrier b.nonbottom.carrier reverse
    (b.encode D) ideal).1 idealEdge).2.2
  obtain ⟨delta, hDelta, f, hf, shape, ordinal, injection, onto⟩ := enumValues ideal z chosen
  rw [idealEq] at injection onto
  refine ⟨D, supportEdge, enumEdge, fixes, delta, hDelta, f, hf, shape, ordinal, injection, ?_⟩
  intro v nonzero below
  have member : b.encode v ∈ relationFiber b.nonbottom.carrier reverse (b.encode D) := by
    apply (mem_relationFiber _ _ _ _).2
    refine ⟨?_, (pair_mem_relationConverse _ _ _ _ _).2
      ⟨b.encode_mem v, b.encode_mem D, (b.pair_mem_conditionOrder v D).2 below⟩⟩
    exact (b.nonbottom.mem_carrier _).2 ⟨⟨v, nonzero⟩, rfl⟩
  exact onto (b.encode v) member

end PartitionPilot.Forcing.TransitiveGround

end OAI
