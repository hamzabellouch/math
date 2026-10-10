import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNameSequenceValues

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include order choice in
theorem forcedSequence_groundReadings_dense (small : M.sets.Countable)
    {U : ZFSet.{u}} (hU : U ∈ M.sets) (closed : InternallyCountablyClosed M s)
    (tau : (M.nameDomain s).names) {base : P}
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier
        (M.omega_mem separation infinite) hU tau) base) :
    let D := Name.sequenceDecisionRelation s ⊤ tau.val ZFSet.omega U
    D ∈ M.sets ∧ DenseBelow base {q | ∃ f ∈ M.sets,
      ZFSet.IsFunc ZFSet.omega U f ∧ f = decisionValues U D (s.encode q) ∧
      Name.ForcesEq q tau.val (Name.check s ⊤ f)} := by
  let D := Name.sequenceDecisionRelation s ⊤ tau.val ZFSet.omega U
  have hN := M.omega_mem separation infinite
  have hD : D ∈ M.sets := M.sequenceDecisionRelation_mem s ⊤ pairing unions powers
    separation collection carrier order tau hN hU
  have persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D := by
    intro p q before n hn a ha entry
    exact (Name.sequenceDecisionRelation_entry s ⊤ tau.val ZFSet.omega U q n a).2
      ⟨hn, ha, Name.sequenceDecision_mono s ⊤ tau.val before
        ((Name.sequenceDecisionRelation_entry s ⊤ tau.val ZFSet.omega U p n a).1 entry).2.2⟩
  have unique : ∀ p : P, p ≤ base → ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ∀ b ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D → a = b := by
    intro p before n hn a ha b hb first second
    exact M.sequenceDecision_unique_below s pairing unions powers separation collection carrier
      small hN hU tau forced before hn ha hb
      ((Name.sequenceDecisionRelation_entry s ⊤ tau.val ZFSet.omega U p n a).1 first).2.2
      ((Name.sequenceDecisionRelation_entry s ⊤ tau.val ZFSet.omega U p n b).1 second).2.2
  have dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D} := by
    intro n hn p before
    obtain ⟨q, qp, a, ha, decision⟩ := M.sequenceDecision_dense_below s pairing unions powers
      separation collection carrier small hN hU tau forced hn p before
    exact ⟨q, qp, a, ha,
      (Name.sequenceDecisionRelation_entry s ⊤ tau.val ZFSet.omega U q n a).2 ⟨hn, ha, decision⟩⟩
  have common := M.internally_commonDecisions_denseBelow s pairing unions powers separation
    infinite choice carrier order hU hD closed base persistent dense
  refine ⟨hD, ?_⟩
  intro p before
  obtain ⟨q, qp, qbase, total⟩ := common p before
  let f := decisionValues U D (s.encode q)
  have hf : f ∈ M.sets := M.decisionValues_mem pairing unions powers separation infinite
    hU hD (M.transitive carrier (s.encode_mem q))
  have function : ZFSet.IsFunc ZFSet.omega U f :=
    decisionValues_function total (unique q qbase)
  have hcheck := M.check_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) f hf
  have equal : Name.ForcesEq q tau.val (Name.check s ⊤ f) := by
    change Forces (M.nameDomain s) (.equal 0 1 : SetFormula 2) ![tau, ⟨_, hcheck⟩] q
    apply (M.ordinaryForces_iff_all_generics s small carrier
      (.equal 0 1 : SetFormula 2) ![tau, ⟨_, hcheck⟩] q).2
    intro H hq generic
    have actual := M.sequenceFunction_eval s pairing unions powers separation collection carrier
      hN hU tau H generic (H.upward hq qbase) forced
    have reading := decisionValues_eq_reading s base persistent unique H hq qbase total actual
      (fun n hn a ha entry => by
        obtain ⟨r, hr, decision⟩ := (M.sequenceDecision_reading s pairing unions powers separation
          collection carrier tau n a (M.transitive hN hn) (M.transitive hU ha) H generic).1 entry
        exact ⟨r, hr, (Name.sequenceDecisionRelation_entry s ⊤ tau.val ZFSet.omega U r n a).2
          ⟨hn, ha, decision⟩⟩)
    change Name.eval {r | H.mem r} tau.val = Name.eval {r | H.mem r} (Name.check s ⊤ f)
    rw [Name.eval_check (s := s) {r | H.mem r} ⊤ H.top_mem]
    exact reading.symm
  exact ⟨q, qp, f, hf, function, rfl, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
