import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBinaryRowRecordedPreparationBounds

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStructuralCondition_nameSupportBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2

    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      ZFSet.pair (c.encode p) A ∈
        M.structuralForcingCarrier c.carrier G s.carrier s.conditionOrder basis lifted T2 stages history →
    ∀ {G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
      (lower : Presentation P) (action : PosetAction G P) (nodeAction : PosetAction G L)
      (base : L) (names : Fin 2 → Name lower),
      (∀ i, HereditarilySymmetric action lower (nodeAction.principalSupportFamily base directed) (names i)) →
    ∀ E : L, ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      E ≤ D ∧ ∀ i, nodeAction.principalFix D ≤ action.stabilizer lower (names i) := by
  intro c rows S T valid lifted tuples hLifted Gcode basis T2 stages history
    hG hb hT2 hs hh I anchors row A member G P instG instP instTop lower action nodeAction base names symmetric E
  obtain ⟨first, firstSupport⟩ := (symmetric 0).symmetric
  obtain ⟨second, secondSupport⟩ := (symmetric 1).symmetric
  obtain ⟨common, firstBelow, secondBelow⟩ := directed first second
  let extra : ZFSet.{u} := {s.encode E, s.encode common}
  have hE := M.transitive hL (s.encode_mem E)
  have hCommon := M.transitive hL (s.encode_mem common)
  have extraGround : extra ∈ M.sets := M.unorderedPair_mem pairing hE hCommon
  have extraSubset : extra ⊆ s.carrier := by
    intro x hx
    rcases ZFSet.mem_pair.1 hx with rfl | rfl
    · exact s.encode_mem E
    · exact s.encode_mem common
  have extraSmall : M.groundEmbeddable extra ZFSet.omega :=
    M.unorderedPair_countable pairing unions powers separation infinite hE hCommon
  obtain ⟨D, rowBound, assignmentBound, extraBound⟩ :=
    M.binaryRowStructuralConditionDataBound s C pairing unions powers separation collection
      infinite choice hL order hC directed countable_bound hmu one valid hLifted
      Gcode basis T2 stages history hG hb hT2 hs hh row A member extra extraGround extraSubset extraSmall
  have commonBelow : common ≤ D := extraBound common (ZFSet.mem_pair.2 (Or.inr rfl))
  have atCommon : ∀ i : Fin 2, nodeAction.principalFix common ≤ action.stabilizer lower (names i) :=
    Fin.cases ((nodeAction.principalFix_antitone firstBelow).trans firstSupport)
      (Fin.cases ((nodeAction.principalFix_antitone secondBelow).trans secondSupport) (fun j => Fin.elim0 j))
  exact ⟨D, rowBound, assignmentBound, extraBound E (ZFSet.mem_pair.2 (Or.inl rfl)),
    fun i => (nodeAction.principalFix_antitone commonBelow).trans (atCommon i)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
