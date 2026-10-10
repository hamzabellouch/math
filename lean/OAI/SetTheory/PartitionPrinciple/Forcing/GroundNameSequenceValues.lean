import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNameSequenceForcingWitness
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSerialOrbits

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def decisionStepGraph (P r U D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ p ∈ P,
    ∃ m ∈ ZFSet.omega, ∃ q ∈ P, ∃ a ∈ U,
      z = ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∧
      m = insert n n ∧ ZFSet.pair q p ∈ r ∧ ZFSet.pair (ZFSet.pair q n) a ∈ D)
    (ZFSet.prod (ZFSet.prod ZFSet.omega P) (ZFSet.prod ZFSet.omega P))

theorem decisionStepGraph_subset (P r U D : ZFSet.{u}) :
    decisionStepGraph P r U D ⊆
      ZFSet.prod (ZFSet.prod ZFSet.omega P) (ZFSet.prod ZFSet.omega P) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_decisionStepGraph (P r U D n p m q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∈ decisionStepGraph P r U D ↔
      n ∈ ZFSet.omega ∧ p ∈ P ∧ m ∈ ZFSet.omega ∧ q ∈ P ∧
        m = insert n n ∧ ZFSet.pair q p ∈ r ∧
          ∃ a ∈ U, ZFSet.pair (ZFSet.pair q n) a ∈ D := by
  rw [decisionStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, p', hp, m', hm, q', hq, a, ha, equal, clock, stronger, decision⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hn, hp, hm, hq, clock, stronger, a, ha, decision⟩
  · rintro ⟨hn, hp, hm, hq, clock, stronger, a, ha, decision⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hp⟩,
      ZFSet.pair_mem_prod.2 ⟨hm, hq⟩⟩, n, hn, p, hp, m, hm, q, hq,
      a, ha, rfl, clock, stronger, decision⟩

namespace BoundedFormula
open SetFormula

def decisionStepEntryFormula : BoundedFormula 6 :=
  exMem 1 (exMem 3 (exMem 3 (exMem 5 (exMem 8
    (.conj (pairOfPairsFormula 5 4 3 2 1)
      (.conj (successorFormula 2 4)
        (.conj (pairMembershipFormula 1 3 8) (tripleMembershipFormula 1 4 0 10))))))))

theorem truth_decisionStepEntryFormula (env : Fin 6 → ZFSet.{u}) :
    Truth decisionStepEntryFormula env ↔
      ∃ n ∈ env 1, ∃ p ∈ env 2, ∃ m ∈ env 1, ∃ q ∈ env 2, ∃ a ∈ env 4,
        env 0 = ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∧
        m = insert n n ∧ ZFSet.pair q p ∈ env 3 ∧
          ZFSet.pair (ZFSet.pair q n) a ∈ env 5 := by
  simp only [decisionStepEntryFormula, truth_exMem, Truth, truth_pairOfPairsFormula,
    truth_successorFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem decisionStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {P r U D : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hU : U ∈ M.sets) (hD : D ∈ M.sets) : decisionStepGraph P r U D ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hW := M.prod_mem pairing unions powers separation hw hP
  let params := extend ZFSet.omega (extend P (extend r (extend U (extend D Fin.elim0))))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hw (Fin.cases hP (Fin.cases hr (Fin.cases hU (Fin.cases hD (fun j => Fin.elim0 j)))))
  have selected := M.bounded_separation_mem separation BoundedFormula.decisionStepEntryFormula
    params members (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.decisionStepEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod ZFSet.omega P) (ZFSet.prod ZFSet.omega P)) =
        decisionStepGraph P r U D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, decisionStepGraph, ZFSet.mem_sep,
      BoundedFormula.truth_decisionStepEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_groundDecisionChain
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (order : s.conditionOrder ∈ M.sets) {S U D : ZFSet.{u}}
    (hS : S ∈ M.sets) (hU : U ∈ M.sets) (hD : D ∈ M.sets) (subset : S ⊆ s.carrier)
    (p : P) (hp : s.encode p ∈ S)
    (dense : ∀ n : Nat, ∀ p : P, s.encode p ∈ S →
      ∃ q, q ≤ p ∧ s.encode q ∈ S ∧
        ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) (natSetCode n)) a ∈ D) :
    ∃ seq : Nat → P, seq 0 = p ∧
      natPresentation.graph s (fun n => seq n.down) ∈ M.sets ∧ Antitone seq ∧
      (∀ n, s.encode (seq n) ∈ S) ∧
      ∀ n, ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode (seq (n + 1))) (natSetCode n)) a ∈ D := by
  have hw := M.omega_mem separation infinite
  let W := ZFSet.prod ZFSet.omega S
  let R := decisionStepGraph S s.conditionOrder U D
  have hW : W ∈ M.sets := M.prod_mem pairing unions powers separation hw hS
  have hR : R ∈ M.sets := M.decisionStepGraph_mem pairing unions powers separation infinite hS order hU hD
  have serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R := by
    intro x hx
    obtain ⟨n, hn, raw, hraw, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨q, rfl⟩ := (s.mem_carrier raw).1 (subset hraw)
    obtain ⟨r, stronger, hr, a, ha, decision⟩ := dense k q hraw
    exact ⟨ZFSet.pair (natSetCode (k + 1)) (s.encode r),
      ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _, hr⟩,
      (pair_mem_decisionStepGraph _ _ _ _ _ _ _ _).2
        ⟨natSetCode_mem_omega _, hraw, natSetCode_mem_omega _, hr, rfl,
          (s.pair_mem_conditionOrder r q).2 stronger, a, ha, decision⟩⟩
  obtain ⟨history, hHistory, function, zero, next⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice hW hR
      (ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega 0, hp⟩) serial
  let t := natPresentation.product (SetMembers.presentation S)
  let state : Nat → ULift.{u} Nat × SetMembers S :=
    fun n => natPresentation.decodeFunction t history function ⟨n⟩
  have entry (n : Nat) : ZFSet.pair (natSetCode n)
      (ZFSet.pair (natSetCode (state n).1.down) (SetMembers.raw (state n).2)) ∈ history :=
    natPresentation.decodeFunction_mem t history function ⟨n⟩
  have initial : natSetCode (state 0).1.down = natSetCode 0 ∧
      SetMembers.raw (state 0).2 = s.encode p :=
    ZFSet.pair_inj.1 ((zero _).1 (entry 0))
  have steps (n : Nat) := (pair_mem_decisionStepGraph S s.conditionOrder U D
    (natSetCode (state n).1.down) (SetMembers.raw (state n).2)
    (natSetCode (state (n + 1)).1.down) (SetMembers.raw (state (n + 1)).2)).1
      (next (natSetCode n) (natSetCode_mem_omega n) _ _ (entry n) (entry (n + 1)))
  have clock (n : Nat) : (state n).1.down = n := by
    induction n with
    | zero => exact natSetCode_injective initial.1
    | succ n ih =>
      have h : natSetCode (state (n + 1)).1.down = natSetCode ((state n).1.down + 1) :=
        (steps n).2.2.2.2.1
      exact (natSetCode_injective h).trans (congrArg (fun k => k + 1) ih)
  let graph := relationCompose ZFSet.omega W S history (productSecond ZFSet.omega S)
  have graphGround : graph ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hw hW hS hHistory (M.productSecond_mem pairing unions powers separation hw hS)
  have smallFunction : ZFSet.IsFunc ZFSet.omega S graph :=
    relationCompose_function_of_subset function (productSecond_function ZFSet.omega S) (fun _ h => h)
  have graphFunction : ZFSet.IsFunc ZFSet.omega s.carrier graph := by
    refine ⟨?_, smallFunction.2⟩
    intro z hz
    obtain ⟨n, hn, q, hq, rfl⟩ := ZFSet.mem_prod.1 (smallFunction.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, subset hq⟩
  let seq : Nat → P := fun n => natPresentation.decodeFunction s graph graphFunction ⟨n⟩
  have projected (n : Nat) : ZFSet.pair (natSetCode n) (SetMembers.raw (state n).2) ∈ graph :=
    (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨natSetCode_mem_omega n, SetMembers.raw_mem _, _,
        ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _, SetMembers.raw_mem _⟩, entry n,
        (mem_productSecond _ _ _).2 ⟨_, natSetCode_mem_omega _, _, SetMembers.raw_mem _, rfl⟩⟩
  have value (n : Nat) : s.encode (seq n) = SetMembers.raw (state n).2 := by
    obtain ⟨_, _, unique⟩ := graphFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique _ (natPresentation.decodeFunction_mem s graph graphFunction ⟨n⟩)).trans
      (unique _ (projected n)).symm
  refine ⟨seq, s.injective ((value 0).trans initial.2),
    M.decoded_function_graph_mem natPresentation s graphGround graphFunction, ?_, ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    apply (s.pair_mem_conditionOrder _ _).1
    rw [value, value]
    exact (steps n).2.2.2.2.2.1
  · intro n
    rw [value]
    exact SetMembers.raw_mem _
  · intro n
    obtain ⟨a, ha, decision⟩ := (steps n).2.2.2.2.2.2
    refine ⟨a, ha, ?_⟩
    rw [value]
    rw [clock] at decision
    exact decision

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def decisionValues (U D p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ a ∈ U,
    z = ZFSet.pair n a ∧ ZFSet.pair (ZFSet.pair p n) a ∈ D)
    (ZFSet.prod ZFSet.omega U)

noncomputable def commonDecisionConditions (P U D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∀ n ∈ ZFSet.omega, ∃ a ∈ U,
    ZFSet.pair (ZFSet.pair p n) a ∈ D) P

noncomputable def decisionDenseCode (P r U D base : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => (ZFSet.pair p base ∈ r ∧ p ∈ commonDecisionConditions P U D) ∨
    ¬ ∃ q ∈ P, ZFSet.pair q p ∈ r ∧ ZFSet.pair q base ∈ r) P

theorem pair_mem_decisionValues (U D p n a : ZFSet.{u}) :
    ZFSet.pair n a ∈ decisionValues U D p ↔
      n ∈ ZFSet.omega ∧ a ∈ U ∧ ZFSet.pair (ZFSet.pair p n) a ∈ D := by
  rw [decisionValues, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, m, hm, b, hb, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hm, hb, entry⟩
  · rintro ⟨hn, ha, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hn, ha⟩, n, hn, a, ha, rfl, entry⟩

theorem mem_commonDecisionConditions (P U D p : ZFSet.{u}) :
    p ∈ commonDecisionConditions P U D ↔
      p ∈ P ∧ ∀ n ∈ ZFSet.omega, ∃ a ∈ U, ZFSet.pair (ZFSet.pair p n) a ∈ D :=
  ZFSet.mem_sep

theorem mem_decisionDenseCode (P r U D base p : ZFSet.{u}) :
    p ∈ decisionDenseCode P r U D base ↔
      p ∈ P ∧ ((ZFSet.pair p base ∈ r ∧ p ∈ commonDecisionConditions P U D) ∨
        ¬ ∃ q ∈ P, ZFSet.pair q p ∈ r ∧ ZFSet.pair q base ∈ r) :=
  ZFSet.mem_sep

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem decisionValues_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {U D p : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets) (hp : p ∈ M.sets) :
    decisionValues U D p ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.exMem 1 (BoundedFormula.exMem 3
    (.conj (BoundedFormula.orderedPairFormula 2 1 0)
      (BoundedFormula.tripleMembershipFormula 6 1 0 5)))
  let params := extend ZFSet.omega (extend U (extend D (extend p Fin.elim0)))
  have hw := M.omega_mem separation infinite
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hw (Fin.cases hU (Fin.cases hD (Fin.cases hp (fun j => Fin.elim0 j))))
  have ground := M.bounded_separation_mem separation formula params members
    (M.prod_mem pairing unions powers separation hw hU)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params))
      (ZFSet.prod ZFSet.omega U) = decisionValues U D p := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, decisionValues, formula, BoundedFormula.truth_exMem,
      BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rfl
  exact equal ▸ ground

theorem commonDecisionConditions_mem
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P U D : ZFSet.{u}} (hP : P ∈ M.sets) (hU : U ∈ M.sets) (hD : D ∈ M.sets) :
    commonDecisionConditions P U D ∈ M.sets := by
  let formula : BoundedFormula 4 := .allMem 1 (BoundedFormula.exMem 3
    (BoundedFormula.tripleMembershipFormula 2 1 0 5))
  let params := extend ZFSet.omega (extend U (extend D Fin.elim0))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases (M.omega_mem separation infinite) (Fin.cases hU (Fin.cases hD (fun j => Fin.elim0 j)))
  have ground := M.bounded_separation_mem separation formula params members hP
  have equal : ZFSet.sep (fun p => BoundedFormula.Truth formula (extend p params)) P =
      commonDecisionConditions P U D := by
    apply ZFSet.ext
    intro p
    simp only [ZFSet.mem_sep, commonDecisionConditions, formula, BoundedFormula.Truth,
      BoundedFormula.truth_exMem, BoundedFormula.truth_tripleMembershipFormula]
    rfl
  exact equal ▸ ground

theorem decisionDenseCode_mem
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r U D base : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hU : U ∈ M.sets) (hD : D ∈ M.sets) (hbase : base ∈ M.sets) :
    decisionDenseCode P r U D base ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.disj
    (.conj (BoundedFormula.pairMembershipFormula 0 3 2) (.mem 0 4))
    (.neg (BoundedFormula.exMem 1 (.conj (BoundedFormula.pairMembershipFormula 0 1 3)
      (BoundedFormula.pairMembershipFormula 0 4 3))))
  let common := commonDecisionConditions P U D
  let params := extend P (extend r (extend base (extend common Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hP (Fin.cases hr (Fin.cases hbase
      (Fin.cases (M.commonDecisionConditions_mem separation infinite hP hU hD) (fun j => Fin.elim0 j))))
  have ground := M.bounded_separation_mem separation formula params members hP
  have equal : ZFSet.sep (fun p => BoundedFormula.Truth formula (extend p params)) P =
      decisionDenseCode P r U D base := by
    apply ZFSet.ext
    intro p
    simp only [ZFSet.mem_sep, decisionDenseCode, formula, BoundedFormula.truth_disj,
      BoundedFormula.Truth, BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem internally_commonDecisions_denseBelow
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D}) :
    DenseBelow base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D} := by
  intro p below
  let S := attachmentIdeal s.carrier s.conditionOrder (s.encode base)
  have hS : S ∈ M.sets := M.attachmentIdeal_mem separation carrier order
    (M.transitive carrier (s.encode_mem base))
  have subset : S ⊆ s.carrier := fun _ h => (ZFSet.mem_sep.1 h).1
  have cone (q : P) : s.encode q ∈ S ↔ q ≤ base := by
    rw [mem_attachmentIdeal, s.pair_mem_conditionOrder]
    exact ⟨And.right, fun h => ⟨s.encode_mem q, h⟩⟩
  obtain ⟨seq, initial, graph, decreasing, _, decisions⟩ :=
    M.exists_groundDecisionChain s pairing unions powers separation infinite choice order
      hS hU hD subset p ((cone p).2 below) (fun n q hq => by
        obtain ⟨r, stronger, a, ha, decided⟩ := dense (natSetCode n) (natSetCode_mem_omega n)
          q ((cone q).1 hq)
        exact ⟨r, stronger, (cone r).2 (stronger.trans ((cone q).1 hq)), a, ha, decided⟩)
  obtain ⟨q, lower⟩ := closed seq graph decreasing
  have stronger : q ≤ p := initial ▸ lower 0
  refine ⟨q, stronger, stronger.trans below, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨a, ha, decided⟩ := decisions k
  exact ⟨a, ha, persistent _ q (lower (k + 1)) _ (natSetCode_mem_omega k) a ha decided⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

private noncomputable def enumeratedFamilyDecisions (Q J B g f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ Q, ∃ n ∈ ZFSet.omega, ∃ j ∈ J, ∃ E ∈ B,
    z = ZFSet.pair (ZFSet.pair p n) j ∧ ZFSet.pair n j ∈ g ∧
      ZFSet.pair j E ∈ f ∧ p ∈ E) (ZFSet.prod (ZFSet.prod Q ZFSet.omega) J)

private theorem enumeratedFamilyDecisions_entry (Q J B g f p n j : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p n) j ∈ enumeratedFamilyDecisions Q J B g f ↔
      p ∈ Q ∧ n ∈ ZFSet.omega ∧ j ∈ J ∧ ZFSet.pair n j ∈ g ∧
        ∃ E ∈ B, ZFSet.pair j E ∈ f ∧ p ∈ E := by
  rw [enumeratedFamilyDecisions, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, p', hp, n', hn, j', hj, E, hE, eq, ng, ef, member⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    exact ⟨hp, hn, hj, ng, E, hE, ef, member⟩
  · rintro ⟨hp, hn, hj, ng, E, hE, ef, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hp, hn⟩, hj⟩,
      p, hp, n, hn, j, hj, E, hE, rfl, ng, ef, member⟩

private def enumeratedFamilyDecisionFormula : BoundedFormula 7 :=
  .exMem 1 (.exMem 3 (.exMem 5 (.exMem 7
    (.conj (BoundedFormula.orderedTripleFormula 4 3 2 1)
      (.conj (BoundedFormula.pairMembershipFormula 2 1 9)
        (.conj (BoundedFormula.pairMembershipFormula 1 0 10) (.mem 3 0)))))))

private theorem enumeratedFamilyDecisionFormula_truth (env : Fin 7 → ZFSet.{u}) :
    BoundedFormula.Truth enumeratedFamilyDecisionFormula env ↔
      ∃ p ∈ env 1, ∃ n ∈ env 2, ∃ j ∈ env 3, ∃ E ∈ env 4,
        env 0 = ZFSet.pair (ZFSet.pair p n) j ∧ ZFSet.pair n j ∈ env 5 ∧
          ZFSet.pair j E ∈ env 6 ∧ p ∈ E := by
  simp only [enumeratedFamilyDecisionFormula, BoundedFormula.truth_exMem,
    BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
    BoundedFormula.truth_pairMembershipFormula]
  rfl

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem internally_countableDenseFamily_denseBelow
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {J f : ZFSet.{u}} (hJ : J ∈ M.sets) (hf : f ∈ M.sets)
    (small : M.groundEmbeddable J ZFSet.omega)
    (function : ZFSet.IsFunc J (M.groundPower s.carrier) f)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ j E, ZFSet.pair j E ∈ f → ∀ p q : P,
      q ≤ p → s.encode p ∈ E → s.encode q ∈ E)
    (dense : ∀ j E, ZFSet.pair j E ∈ f → DenseBelow base {q | s.encode q ∈ E}) :
    DenseBelow base {q | q ≤ base ∧ ∀ j E, ZFSet.pair j E ∈ f → s.encode q ∈ E} := by
  classical
  by_cases nonempty : J.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ := M.groundCountable_enumeration
      pairing unions powers separation infinite hJ nonempty small
    let B := M.groundPower s.carrier
    let D := enumeratedFamilyDecisions s.carrier J B g f
    have hN := M.omega_mem separation infinite
    have hB : B ∈ M.sets := M.groundPower_mem powers carrier
    let params := ![s.carrier, ZFSet.omega, J, B, g, f]
    have members : ∀ i, params i ∈ M.sets := Fin.cases carrier (Fin.cases hN
      (Fin.cases hJ (Fin.cases hB (Fin.cases hg (Fin.cases hf (fun i => Fin.elim0 i))))))
    have selected := M.bounded_separation_mem separation enumeratedFamilyDecisionFormula
      params members (M.prod_mem pairing unions powers separation
        (M.prod_mem pairing unions powers separation carrier hN) hJ)
    have hD : D ∈ M.sets := by
      have equal : ZFSet.sep (fun z => BoundedFormula.Truth enumeratedFamilyDecisionFormula
          (extend z params)) (ZFSet.prod (ZFSet.prod s.carrier ZFSet.omega) J) = D := by
        apply ZFSet.ext
        intro z
        change _ ↔ z ∈ enumeratedFamilyDecisions s.carrier J B g f
        rw [ZFSet.mem_sep, enumeratedFamilyDecisions, ZFSet.mem_sep,
          enumeratedFamilyDecisionFormula_truth]
        rfl
      exact equal ▸ selected
    have persistD : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ j ∈ J,
        ZFSet.pair (ZFSet.pair (s.encode p) n) j ∈ D →
          ZFSet.pair (ZFSet.pair (s.encode q) n) j ∈ D := by
      intro p q qp n hn j hj entry
      obtain ⟨_, _, _, ng, E, hE, ef, member⟩ :=
        (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode p) n j).1 entry
      exact (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode q) n j).2
        ⟨s.encode_mem q, hn, hj, ng, E, hE, ef, persistent j E ef p q qp member⟩
    have denseD : ∀ n ∈ ZFSet.omega, DenseBelow base
        {q | ∃ j ∈ J, ZFSet.pair (ZFSet.pair (s.encode q) n) j ∈ D} := by
      intro n hn p pb
      obtain ⟨j, ng, _⟩ := enumeration.2 n hn
      have hj := (ZFSet.pair_mem_prod.1 (enumeration.1 ng)).2
      obtain ⟨E, ef, _⟩ := function.2 j hj
      have hE := (ZFSet.pair_mem_prod.1 (function.1 ef)).2
      obtain ⟨q, qp, member⟩ := dense j E ef p pb
      exact ⟨q, qp, j, hj,
        (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode q) n j).2
          ⟨s.encode_mem q, hn, hj, ng, E, hE, ef, member⟩⟩
    have common := M.internally_commonDecisions_denseBelow s pairing unions powers separation
      infinite choice carrier order hJ hD closed base persistD denseD
    intro p pb
    obtain ⟨q, qp, qb, decisions⟩ := common p pb
    refine ⟨q, qp, qb, ?_⟩
    intro j E ef
    have hj := (ZFSet.pair_mem_prod.1 (function.1 ef)).1
    obtain ⟨n, hn, ng⟩ := onto j hj
    obtain ⟨j', _, entry⟩ := decisions n hn
    obtain ⟨_, _, _, ng', E', _, ef', member⟩ :=
      (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode q) n j').1 entry
    obtain ⟨_, _, uniqueJ⟩ := enumeration.2 n hn
    have sameJ : j' = j := (uniqueJ _ ng').trans (uniqueJ _ ng).symm
    subst j'
    obtain ⟨_, _, uniqueE⟩ := function.2 j hj
    have sameE : E' = E := (uniqueE _ ef').trans (uniqueE _ ef).symm
    exact sameE ▸ member
  · intro p pb
    refine ⟨p, le_rfl, pb, ?_⟩
    intro j E ef
    exact False.elim (nonempty ⟨j, (ZFSet.pair_mem_prod.1 (function.1 ef)).1⟩)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
variable {P : Type u} [Preorder P] (s : Presentation P)

theorem decisionDenseCode_eq (U D : ZFSet.{u}) (base : P) :
    s.subset (Localized base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D}) =
      decisionDenseCode s.carrier s.conditionOrder U D (s.encode base) := by
  have compatible (p : P) :
      (∃ q ∈ s.carrier, ZFSet.pair q (s.encode p) ∈ s.conditionOrder ∧
        ZFSet.pair q (s.encode base) ∈ s.conditionOrder) ↔ Compatible p base := by
    constructor
    · rintro ⟨q, hq, below, belowBase⟩
      obtain ⟨q, rfl⟩ := (s.mem_carrier q).1 hq
      exact ⟨q, (s.pair_mem_conditionOrder _ _).1 below,
        (s.pair_mem_conditionOrder _ _).1 belowBase⟩
    · rintro ⟨q, below, belowBase⟩
      exact ⟨s.encode q, s.encode_mem q, (s.pair_mem_conditionOrder _ _).2 below,
        (s.pair_mem_conditionOrder _ _).2 belowBase⟩
  have each (p : P) :
      s.encode p ∈ decisionDenseCode s.carrier s.conditionOrder U D (s.encode base) ↔
        p ∈ Localized base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
          ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D} := by
    simp only [mem_decisionDenseCode, mem_commonDecisionConditions,
      s.pair_mem_conditionOrder, s.encode_mem, true_and, compatible, Localized, Set.mem_ofPred_eq]
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := (s.mem_subset _ z).1 hz
    exact (each p).2 hp
  · intro hz
    have bound := (mem_decisionDenseCode _ _ _ _ _ z).1 hz
    obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 bound.1
    exact (s.encode_mem_subset _ p).2 ((each p).1 hz)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem generic_common_decisions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D})
    (H : ConditionFilter P) (generic : H.GenericFor (M.codedFamily s)) (hbase : H.mem base) :
    ∃ q, H.mem q ∧ q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D := by
  have density := M.internally_commonDecisions_denseBelow s pairing unions powers separation infinite choice
    carrier order hU hD closed base persistent dense
  have code := M.decisionDenseCode_mem separation infinite carrier order hU hD
    (M.transitive carrier (s.encode_mem base))
  rw [← decisionDenseCode_eq s U D base] at code
  exact H.meets_below generic hbase (M.codedFamily_of_code s code) density

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem decisionValues_function {U D p : ZFSet.{u}}
    (total : ∀ n ∈ ZFSet.omega, ∃ a ∈ U, ZFSet.pair (ZFSet.pair p n) a ∈ D)
    (unique : ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ∀ b ∈ U,
      ZFSet.pair (ZFSet.pair p n) a ∈ D → ZFSet.pair (ZFSet.pair p n) b ∈ D → a = b) :
    ZFSet.IsFunc ZFSet.omega U (decisionValues U D p) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro n hn
  obtain ⟨a, ha, decision⟩ := total n hn
  refine ⟨a, (pair_mem_decisionValues _ _ _ _ _).2 ⟨hn, ha, decision⟩, ?_⟩
  intro b hb
  have actual := (pair_mem_decisionValues _ _ _ _ _).1 hb
  exact unique n hn b actual.2.1 a ha actual.2.2 decision

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem decisionValues_eq_reading {U D f : ZFSet.{u}} (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (unique : ∀ p : P, p ≤ base → ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ∀ b ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D → a = b)
    (H : ConditionFilter P) {q : P} (hq : H.mem q) (below : q ≤ base)
    (total : ∀ n ∈ ZFSet.omega, ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (function : ZFSet.IsFunc ZFSet.omega U f)
    (realizes : ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ZFSet.pair n a ∈ f →
      ∃ p, H.mem p ∧ ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D) :
    decisionValues U D (s.encode q) = f := by
  have agree (p : P) (hp : H.mem p) (n : ZFSet.{u}) (hn : n ∈ ZFSet.omega)
      (a b : ZFSet.{u}) (ha : a ∈ U) (hb : b ∈ U)
      (first : ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
      (second : ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D) : a = b := by
    obtain ⟨r, _, rq, rp⟩ := H.directed hq hp
    exact unique r (rq.trans below) n hn a ha b hb
      (persistent q r rq n hn a ha first) (persistent p r rp n hn b hb second)
  have same (n : ZFSet.{u}) (hn : n ∈ ZFSet.omega) (a : ZFSet.{u}) (ha : a ∈ U) :
      ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D ↔ ZFSet.pair n a ∈ f := by
    constructor
    · intro decision
      obtain ⟨b, entry, _⟩ := function.2 n hn
      have hb := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
      obtain ⟨p, hp, read⟩ := realizes n hn b hb entry
      exact (agree p hp n hn a b ha hb decision read).symm ▸ entry
    · intro entry
      obtain ⟨b, hb, decision⟩ := total n hn
      obtain ⟨p, hp, read⟩ := realizes n hn a ha entry
      exact agree p hp n hn b a hb ha decision read ▸ decision
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, a, ha, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    exact (same n hn a ha).1 ((pair_mem_decisionValues _ _ _ _ _).1 hz).2.2
  · intro hz
    obtain ⟨n, hn, a, ha, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact (pair_mem_decisionValues _ _ _ _ _).2 ⟨hn, ha, (same n hn a ha).2 hz⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem generic_decision_reading_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (unique : ∀ p : P, p ≤ base → ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ∀ b ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D → a = b)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D})
    (H : ConditionFilter P) (generic : H.GenericFor (M.codedFamily s)) (hbase : H.mem base)
    {f : ZFSet.{u}} (function : ZFSet.IsFunc ZFSet.omega U f)
    (realizes : ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ZFSet.pair n a ∈ f →
      ∃ p, H.mem p ∧ ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D) :
    f ∈ M.sets ∧ ∃ q, H.mem q ∧ q ≤ base ∧ decisionValues U D (s.encode q) = f := by
  obtain ⟨q, hq, below, total⟩ := M.generic_common_decisions s pairing unions powers separation
    infinite choice carrier order hU hD closed base persistent dense H generic hbase
  have equal := decisionValues_eq_reading s base persistent unique H hq below total function realizes
  exact ⟨equal ▸ M.decisionValues_mem pairing unions powers separation infinite hU hD
    (M.transitive carrier (s.encode_mem q)), q, hq, below, equal⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
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

include pairing unions powers separation collection infinite choice carrier order in
theorem sequence_value_ground (small : M.sets.Countable)
    {U : ZFSet.{u}} (hU : U ∈ M.sets) (closed : InternallyCountablyClosed M s)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {base : P} (hbase : H.mem base)
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier
        (M.omega_mem separation infinite) hU τ) base) :
    Name.eval {q | H.mem q} τ.val ∈ M.sets ∧
      ∃ q, H.mem q ∧ q ≤ base ∧ decisionValues U
        (Name.sequenceDecisionRelation s ⊤ τ.val ZFSet.omega U) (s.encode q) =
          Name.eval {q | H.mem q} τ.val := by
  have hN := M.omega_mem separation infinite
  have hD := M.sequenceDecisionRelation_mem s ⊤ pairing unions powers separation collection
    carrier order τ hN hU
  have function := M.sequenceFunction_eval s pairing unions powers separation collection carrier
    hN hU τ H genericFormula hbase forced
  refine M.generic_decision_reading_ground s pairing unions powers separation infinite choice
    carrier order hU hD closed base ?_ ?_ ?_ H genericCoded hbase function ?_
  · intro p q before n hn a ha entry
    have decision := (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n a).1 entry
    exact (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U q n a).2
      ⟨hn, ha, Name.sequenceDecision_mono s ⊤ τ.val before decision.2.2⟩
  · intro p before n hn a ha b hb first second
    exact M.sequenceDecision_unique_below s pairing unions powers separation collection carrier
      small hN hU τ forced before hn ha hb
      ((Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n a).1 first).2.2
      ((Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n b).1 second).2.2
  · intro n hn q before
    obtain ⟨r, rq, a, ha, decision⟩ := M.sequenceDecision_dense_below s pairing unions powers
      separation collection carrier small hN hU τ forced hn q before
    exact ⟨r, rq, a, ha,
      (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U r n a).2 ⟨hn, ha, decision⟩⟩
  · intro n hn a ha entry
    obtain ⟨p, hp, decision⟩ := (M.sequenceDecision_reading s pairing unions powers separation
      collection carrier τ n a (M.transitive hN hn) (M.transitive hU ha) H genericFormula).1 entry
    exact ⟨p, hp,
      (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n a).2 ⟨hn, ha, decision⟩⟩

include pairing unions powers separation collection infinite choice carrier order in
theorem sequence_value_ground_of_function (small : M.sets.Countable)
    {U : ZFSet.{u}} (hU : U ∈ M.sets) (closed : InternallyCountablyClosed M s)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (function : ZFSet.IsFunc ZFSet.omega U (Name.eval {q | H.mem q} τ.val)) :
    Name.eval {q | H.mem q} τ.val ∈ M.sets ∧
      ∃ q, H.mem q ∧ decisionValues U
        (Name.sequenceDecisionRelation s ⊤ τ.val ZFSet.omega U) (s.encode q) =
          Name.eval {q | H.mem q} τ.val := by
  obtain ⟨base, hbase, forced⟩ := M.exists_sequenceFunction_forcing s pairing unions powers
    separation collection carrier (M.omega_mem separation infinite) hU τ H genericFormula function
  obtain ⟨ground, q, hq, _, equal⟩ := M.sequence_value_ground s pairing unions powers separation
    collection infinite choice carrier order small hU closed τ H genericCoded genericFormula hbase forced
  exact ⟨ground, q, hq, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
