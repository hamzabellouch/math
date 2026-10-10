import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFairPreparationMonotonicity

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def fairPreparationConditionGraph
    (Q stages U E0 orbit : ZFSet.{u}) : ZFSet.{u} :=
  let tail := ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U))
  let middle := ZFSet.prod Q tail
  let bound := ZFSet.prod ZFSet.omega middle
  relationCompose ZFSet.omega middle Q
    (relationCompose ZFSet.omega bound middle orbit (productSecond ZFSet.omega middle))
    (productFirst Q tail)

theorem fairPreparationConditionGraph_function
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit) :
    ZFSet.IsFunc ZFSet.omega Q (M.fairPreparationConditionGraph Q stages U E0 orbit) := by
  let tail := ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U))
  let middle := ZFSet.prod Q tail
  have widened : ZFSet.IsFunc ZFSet.omega (ZFSet.prod ZFSet.omega middle) orbit := by
    refine ⟨?_, function.2⟩
    intro z member
    obtain ⟨i, hi, state, hs, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hi, ((M.mem_fairPreparationStates _ _ _ _ _ _).1 hs).1⟩
  exact relationCompose_function_of_subset
    (relationCompose_function_of_subset widened
      (productSecond_function ZFSet.omega middle) (fun _ h => h))
    (productFirst_function Q tail) (fun _ h => h)

theorem pair_mem_fairPreparationConditionGraph
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (i p : ZFSet.{u}) :
    ZFSet.pair i p ∈ M.fairPreparationConditionGraph Q stages U E0 orbit ↔
      ∃ clock births event,
        ZFSet.pair i (ZFSet.pair clock (ZFSet.pair p (ZFSet.pair births event))) ∈ orbit := by
  dsimp only [fairPreparationConditionGraph]
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, middle, _, first, second⟩
    obtain ⟨_, _, state, _, edge, projected⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨p', hp', tail, ht, eq⟩ := (mem_productFirst _ _ _).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨clock, hc, rest, hr, eq⟩ := (mem_productSecond _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨births, hb, event, he, rfl⟩ := ZFSet.mem_prod.1 ht
    exact ⟨clock, births, event, edge⟩
  · rintro ⟨clock, births, event, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have stateBound := ((M.mem_fairPreparationStates _ _ _ _ _ _).1 bounds.2).1
    have split := ZFSet.pair_mem_prod.1 stateBound
    have rest := ZFSet.pair_mem_prod.1 split.2
    refine ⟨bounds.1, rest.1, _, split.2, ?_, ?_⟩
    · exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bounds.1, split.2, _, stateBound, edge,
          (mem_productSecond _ _ _).2 ⟨clock, split.1, _, split.2, rfl⟩⟩
    · exact (mem_productFirst _ _ _).2 ⟨p, rest.1, _, rest.2, rfl⟩

theorem fairPreparationConditionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages U E0 orbit : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets) :
    M.fairPreparationConditionGraph Q stages U E0 orbit ∈ M.sets := by
  have hTail := M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hE0)
    (M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
      (M.prod_mem pairing unions powers separation hStages hU))
  have hMiddle := M.prod_mem pairing unions powers separation hQ hTail
  exact M.relationCompose_mem pairing unions powers separation omega hMiddle hQ
    (M.relationCompose_mem pairing unions powers separation omega
      (M.prod_mem pairing unions powers separation omega hMiddle) hMiddle whole
      (M.productSecond_mem pairing unions powers separation omega hMiddle))
    (M.productFirst_mem pairing unions powers separation hQ hTail)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem fairPreparationOrbit_conditionSequence
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages U E0 enumSelector prepSelector grid packed nodes T orbit : ZFSet.{u}}
    (hQ : s.carrier ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates s.carrier stages U E0 enumSelector) orbit)
    (selected : prepSelector ⊆
      M.varyingPreparationRelation stages packed s.carrier s.conditionOrder nodes T)
    (p : P) (e : ZFSet.{u})
    (initial : ∀ state, ZFSet.pair ∅ state ∈ orbit ↔
      state = ZFSet.pair ∅ (ZFSet.pair (s.encode p) (ZFSet.pair {ZFSet.pair ∅ e} ∅)))
    (steps : ∀ n ∈ ZFSet.omega, ∀ state next,
      ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
      FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector grid state next) :
    ∃ seq : Nat → P, seq 0 = p ∧
      natPresentation.graph s (fun n => seq n.down) ∈ M.sets ∧ Antitone seq ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, ZFSet.pair (natSetCode k)
          (ZFSet.pair (clocks k) (ZFSet.pair (s.encode (seq k))
            (ZFSet.pair (births k) (events k)))) ∈ orbit) ∧
        ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector grid
          (ZFSet.pair (clocks k) (ZFSet.pair (s.encode (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (s.encode (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1))))) := by
  let graph := M.fairPreparationConditionGraph s.carrier stages U E0 orbit
  have graphGround : graph ∈ M.sets :=
    M.fairPreparationConditionGraph_mem pairing unions powers separation hQ hStages hU hE0 omega whole
  have graphFunction : ZFSet.IsFunc ZFSet.omega s.carrier graph :=
    M.fairPreparationConditionGraph_function function
  let seq : Nat → P := fun n => natPresentation.decodeFunction s graph graphFunction ⟨n⟩
  have represented (k : Nat) : ∃ clock births event,
      ZFSet.pair (natSetCode k)
        (ZFSet.pair clock (ZFSet.pair (s.encode (seq k)) (ZFSet.pair births event))) ∈ orbit :=
    (M.pair_mem_fairPreparationConditionGraph function _ _).1
      (natPresentation.decodeFunction_mem s graph graphFunction ⟨k⟩)
  choose clocks births events entries using represented
  have atZero := (initial _).1 (entries 0)
  have zeroClock := (ZFSet.pair_inj.1 atZero).1
  have zeroCondition := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 atZero).2).1
  have zeroTail := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 atZero).2).2
  have rawSteps (k : Nat) := steps (natSetCode k) (natSetCode_mem_omega k)
    _ _ (entries k) (entries (k + 1))
  have decreasing : Antitone seq := by
    apply antitone_nat_of_succ_le
    intro k
    apply (s.pair_mem_conditionOrder _ _).1
    exact M.fairPreparationStep_strengthens ZFSet.omega E0 stages U enumSelector prepSelector
      grid packed s.carrier s.conditionOrder nodes T selected
      (clocks k) (s.encode (seq k)) (births k) (events k)
      (clocks (k + 1)) (s.encode (seq (k + 1))) (births (k + 1)) (events (k + 1))
      ((s.pair_mem_conditionOrder _ _).2 le_rfl) (rawSteps k)
  exact ⟨seq, s.injective zeroCondition,
    M.decoded_function_graph_mem natPresentation s graphGround graphFunction, decreasing,
    clocks, births, events, zeroClock, zeroTail.1, zeroTail.2, entries, rawSteps⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
