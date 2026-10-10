import OAI.SetTheory.PartitionPrinciple.Definability.GroundVaryingPreparationRelations
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFiniteBirthHistories
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementBirthEnumerationFairness

namespace OAI


namespace PartitionPilot.Forcing
universe u

def FairPreparationStateCode (omega E0 enumSelector state : ZFSet.{u}) : Prop :=
  ∃ n p births last, state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
    n ∈ omega ∧ insert n n ∈ omega ∧ ZFSet.IsFunc (insert n n) E0 births ∧
    ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧ ZFSet.pair n e ∈ births

namespace BoundedFormula
open SetFormula

def exFairStateFields {n} (state : Fin n) (body : BoundedFormula (n + 4)) : BoundedFormula n :=
  exPairFields state (exPairFields 0 (exPairFields 0
    (reindex (Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (Fin.cases 5
      (fun j => j.succ.succ.succ.succ.succ.succ))))) body)))

theorem truth_exFairStateFields {n} (state : Fin n) (body : BoundedFormula (n + 4))
    (env : Fin n → ZFSet.{u}) :
    Truth (exFairStateFields state body) env ↔
      ∃ n p births last, env state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
        Truth body (extend last (extend births (extend p (extend n env)))) := by
  simp only [exFairStateFields, truth_exPairFields, truth_reindex]
  have rearrange (n tail p inner births last : ZFSet.{u}) :
      (fun i => extend last (extend births (extend inner (extend p (extend tail (extend n env)))))
        (Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (Fin.cases 5
          (fun j => j.succ.succ.succ.succ.succ.succ)))) i)) =
        extend last (extend births (extend p (extend n env))) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
      (fun l => Fin.cases ?_ (fun m => ?_) l) k) j) i <;> rfl
  simp only [rearrange]
  constructor
  · rintro ⟨n, tail, eq, p, inner, rfl, births, last, rfl, holds⟩
    exact ⟨n, p, births, last, eq, holds⟩
  · rintro ⟨n, p, births, last, eq, holds⟩
    exact ⟨n, _, eq, p, _, rfl, births, last, rfl, holds⟩

def fairPreparationStateFormula {n} (omega E0 enumSelector state : Fin n) : BoundedFormula n :=
  let old := fun j : Fin n => j.succ.succ.succ.succ
  exFairStateFields state (.conj (.mem 3 (old omega))
    (exMem (old omega) (.conj (successorFormula 0 4)
      (.conj (functionFormula 0 (old E0).succ 2)
        (exMem (old E0).succ (.conj
          (pairMembershipFormula 4 0 (old enumSelector).succ.succ)
          (pairMembershipFormula 5 0 3)))))))

theorem truth_fairPreparationStateFormula {n} (omega E0 enumSelector state : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fairPreparationStateFormula omega E0 enumSelector state) env ↔
      FairPreparationStateCode (env omega) (env E0) (env enumSelector) (env state) := by
  simp only [fairPreparationStateFormula, truth_exFairStateFields, Truth, truth_exMem,
    truth_successorFormula, truth_functionFormula, truth_pairMembershipFormula]
  change (∃ n p births last, env state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
    n ∈ env omega ∧ ∃ next ∈ env omega, next = insert n n ∧
      ZFSet.IsFunc next (env E0) births ∧ ∃ e ∈ env E0,
        ZFSet.pair p e ∈ env enumSelector ∧ ZFSet.pair n e ∈ births) ↔ _
  constructor
  · rintro ⟨n, p, births, last, shape, hn, next, hm, rfl, function, witness⟩
    exact ⟨n, p, births, last, shape, hn, hm, function, witness⟩
  · rintro ⟨n, p, births, last, shape, hn, hm, function, witness⟩
    exact ⟨n, p, births, last, shape, hn, insert n n, hm, rfl, function, witness⟩

end BoundedFormula






def FairPreparationStepCode
    (omega E0 stages U enumSelector prepSelector gridGraph state next : ZFSet.{u}) : Prop :=
  ∃ n p births last m q nextBirths event,
    state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
    next = ZFSet.pair m (ZFSet.pair q (ZFSet.pair nextBirths event)) ∧
    m = insert n n ∧
    ∃ i ∈ omega, ∃ j ∈ omega, ∃ e ∈ E0, ∃ newE ∈ E0,
      ZFSet.pair n (ZFSet.pair i j) ∈ gridGraph ∧
      ZFSet.pair i e ∈ births ∧ ZFSet.pair q newE ∈ enumSelector ∧
      nextBirths = insert (ZFSet.pair m newE) births ∧
      ((e = ∅ ∧ q = p ∧ event = ∅) ∨
        (∃ alpha ∈ stages, ∃ y ∈ U, (∃ payload, y = ZFSet.pair q payload) ∧
          ZFSet.pair j alpha ∈ e ∧ ZFSet.pair (ZFSet.pair alpha p) y ∈ prepSelector ∧
          event = ZFSet.pair alpha y))

namespace BoundedFormula
open SetFormula

private def insertPairFormula {n} (output graph x y : Fin n) : BoundedFormula n :=
  .conj (.allMem output (disj (.mem 0 graph.succ) (orderedPairFormula 0 x.succ y.succ)))
    (.conj (subsetFormula graph output) (pairMembershipFormula x y output))

private theorem truth_insertPairFormula {n} (output graph x y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (insertPairFormula output graph x y) env ↔
      env output = insert (ZFSet.pair (env x) (env y)) (env graph) := by
  simp only [insertPairFormula, Truth, truth_disj, truth_orderedPairFormula,
    truth_subsetFormula, truth_pairMembershipFormula]
  constructor
  · rintro ⟨inside, includes, entry⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨fun hz => (inside z hz).symm,
      fun hz => hz.elim (fun eq => eq ▸ entry) (fun hz => includes hz)⟩
  · intro eq
    rw [eq]
    exact ⟨fun z hz => (ZFSet.mem_insert_iff.1 hz).symm,
      fun _ hz => ZFSet.mem_insert_of_mem _ hz, ZFSet.mem_insert _ _⟩

private def activePreparationFormula {n}
    (stages U e j p q event prepSelector : Fin n) : BoundedFormula n :=
  let old := fun i : Fin n => i.succ.succ.succ.succ
  exMem stages (exMem U.succ (exPairFields 0
    (.conj (.equal 1 (old q))
      (.conj (pairMembershipFormula (old j) 3 (old e))
        (.conj (tripleMembershipFormula 3 (old p) 2 (old prepSelector))
          (orderedPairFormula (old event) 3 2))))))

private theorem truth_activePreparationFormula {n}
    (stages U e j p q event prepSelector : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (activePreparationFormula stages U e j p q event prepSelector) env ↔
      ∃ alpha ∈ env stages, ∃ y ∈ env U, (∃ payload, y = ZFSet.pair (env q) payload) ∧
        ZFSet.pair (env j) alpha ∈ env e ∧
        ZFSet.pair (ZFSet.pair alpha (env p)) y ∈ env prepSelector ∧
        env event = ZFSet.pair alpha y := by
  simp only [activePreparationFormula, truth_exMem, truth_exPairFields, Truth,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, truth_orderedPairFormula]
  constructor
  · rintro ⟨alpha, ha, y, hy, q', payload, shape, equal, entry, selected, eventEq⟩
    change q' = env q at equal
    exact ⟨alpha, ha, y, hy, ⟨payload, equal ▸ shape⟩, entry, selected, eventEq⟩
  · rintro ⟨alpha, ha, y, hy, ⟨payload, shape⟩, entry, selected, eventEq⟩
    exact ⟨alpha, ha, y, hy, env q, payload, shape, rfl, entry, selected, eventEq⟩

private def fairStepFieldsFormula {arity}
    (omega E0 stages U enumSelector prepSelector gridGraph n p births m q nextBirths event : Fin arity) :
    BoundedFormula arity :=
  let old := fun i : Fin arity => i.succ.succ.succ.succ
  .conj (successorFormula m n)
    (exMem omega (exMem omega.succ (exMem E0.succ.succ (exMem E0.succ.succ.succ
      (.conj (rightTripleMembershipFormula (old n) 3 2 (old gridGraph))
        (.conj (pairMembershipFormula 3 1 (old births))
          (.conj (pairMembershipFormula (old q) 0 (old enumSelector))
            (.conj (insertPairFormula (old nextBirths) (old births) (old m) 0)
              (disj (.conj (emptyFormula 1) (.conj (.equal (old q) (old p)) (emptyFormula (old event))))
                (activePreparationFormula (old stages) (old U) 1 2 (old p) (old q)
                  (old event) (old prepSelector)))))))))))

private theorem truth_fairStepFieldsFormula {arity}
    (omega E0 stages U enumSelector prepSelector gridGraph n p births m q nextBirths event : Fin arity)
    (env : Fin arity → ZFSet.{u}) :
    Truth (fairStepFieldsFormula omega E0 stages U enumSelector prepSelector gridGraph
      n p births m q nextBirths event) env ↔
    env m = insert (env n) (env n) ∧
    ∃ i ∈ env omega, ∃ j ∈ env omega, ∃ e ∈ env E0, ∃ newE ∈ env E0,
      ZFSet.pair (env n) (ZFSet.pair i j) ∈ env gridGraph ∧
      ZFSet.pair i e ∈ env births ∧ ZFSet.pair (env q) newE ∈ env enumSelector ∧
      env nextBirths = insert (ZFSet.pair (env m) newE) (env births) ∧
      ((e = ∅ ∧ env q = env p ∧ env event = ∅) ∨
        (∃ alpha ∈ env stages, ∃ y ∈ env U, (∃ payload, y = ZFSet.pair (env q) payload) ∧
          ZFSet.pair j alpha ∈ e ∧ ZFSet.pair (ZFSet.pair alpha (env p)) y ∈ env prepSelector ∧
          env event = ZFSet.pair alpha y)) := by
  simp only [fairStepFieldsFormula, Truth, truth_successorFormula, truth_exMem,
    truth_rightTripleMembershipFormula, truth_pairMembershipFormula, truth_insertPairFormula,
    truth_disj, truth_emptyFormula, truth_activePreparationFormula]
  rfl

def fairPreparationStepFormula {n}
    (omega E0 stages U enumSelector prepSelector gridGraph state next : Fin n) : BoundedFormula n :=
  let old := fun i : Fin n => i.succ.succ.succ.succ.succ.succ.succ.succ
  exFairStateFields state (exFairStateFields next.succ.succ.succ.succ
    (fairStepFieldsFormula (old omega) (old E0) (old stages) (old U) (old enumSelector)
      (old prepSelector) (old gridGraph) 7 6 5 3 2 1 0))

theorem truth_fairPreparationStepFormula {n}
    (omega E0 stages U enumSelector prepSelector gridGraph state next : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fairPreparationStepFormula omega E0 stages U enumSelector prepSelector gridGraph state next) env ↔
      FairPreparationStepCode (env omega) (env E0) (env stages) (env U) (env enumSelector)
        (env prepSelector) (env gridGraph) (env state) (env next) := by
  simp only [fairPreparationStepFormula, truth_exFairStateFields, truth_fairStepFieldsFormula]
  constructor
  · rintro ⟨n, p, births, last, shape, m, q, nextBirths, event, nextShape, rest⟩
    exact ⟨n, p, births, last, m, q, nextBirths, event, shape, nextShape, rest⟩
  · rintro ⟨n, p, births, last, m, q, nextBirths, event, shape, nextShape, rest⟩
    exact ⟨n, p, births, last, shape, m, q, nextBirths, event, nextShape, rest⟩

end BoundedFormula

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def fairPreparationStates (Q stages U E0 enumSelector : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (FairPreparationStateCode ZFSet.omega E0 enumSelector)
    (ZFSet.prod ZFSet.omega (ZFSet.prod Q
      (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U)))))

theorem mem_fairPreparationStates (Q stages U E0 enumSelector state : ZFSet.{u}) :
    state ∈ M.fairPreparationStates Q stages U E0 enumSelector ↔
      state ∈ ZFSet.prod ZFSet.omega (ZFSet.prod Q
        (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U)))) ∧
      FairPreparationStateCode ZFSet.omega E0 enumSelector state := ZFSet.mem_sep

noncomputable def fairPreparationTransition
    (Q stages U E0 enumSelector prepSelector gridGraph : ZFSet.{u}) : ZFSet.{u} :=
  let states := M.fairPreparationStates Q stages U E0 enumSelector
  ZFSet.sep (fun z => ∃ state next, z = ZFSet.pair state next ∧
    FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector gridGraph state next)
    (ZFSet.prod states states)

theorem pair_mem_fairPreparationTransition
    (Q stages U E0 enumSelector prepSelector gridGraph state next : ZFSet.{u}) :
    ZFSet.pair state next ∈ M.fairPreparationTransition Q stages U E0 enumSelector prepSelector gridGraph ↔
      state ∈ M.fairPreparationStates Q stages U E0 enumSelector ∧
      next ∈ M.fairPreparationStates Q stages U E0 enumSelector ∧
      FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector gridGraph state next := by
  rw [fairPreparationTransition, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hs, hn⟩, state', next', eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hs, hn, code⟩
  · rintro ⟨hs, hn, code⟩
    exact ⟨⟨hs, hn⟩, state, next, rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem fairPreparationStates_mem
    {Q stages U E0 enumSelector : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (hEnum : enumSelector ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.fairPreparationStates Q stages U E0 enumSelector ∈ M.sets := by
  have history := M.groundRelations_mem pairing unions powers separation omega hE0
  have events := M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
    (M.prod_mem pairing unions powers separation hStages hU)
  have bound := M.prod_mem pairing unions powers separation omega
    (M.prod_mem pairing unions powers separation hQ
      (M.prod_mem pairing unions powers separation history events))
  let params : Fin 3 → ZFSet.{u} := ![ZFSet.omega, E0, enumSelector]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases omega
    (Fin.cases hE0 (Fin.cases hEnum (fun j => Fin.elim0 j)))
  let formula : BoundedFormula 4 := BoundedFormula.fairPreparationStateFormula 1 2 3 0
  have selected := M.bounded_separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params))
      (ZFSet.prod ZFSet.omega (ZFSet.prod Q
        (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U))))) =
      M.fairPreparationStates Q stages U E0 enumSelector := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, fairPreparationStates, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_fairPreparationStateFormula 1 2 3 0 _)
  exact equal ▸ selected

include pairing unions powers separation in
theorem fairPreparationTransition_mem
    {Q stages U E0 enumSelector prepSelector gridGraph : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (hEnum : enumSelector ∈ M.sets)
    (hPrep : prepSelector ∈ M.sets) (hGrid : gridGraph ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.fairPreparationTransition Q stages U E0 enumSelector prepSelector gridGraph ∈ M.sets := by
  have states := M.fairPreparationStates_mem pairing unions powers separation hQ hStages hU hE0 hEnum omega
  let params : Fin 7 → ZFSet.{u} := ![ZFSet.omega, E0, stages, U, enumSelector, prepSelector, gridGraph]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases omega (Fin.cases hE0
    (Fin.cases hStages (Fin.cases hU (Fin.cases hEnum (Fin.cases hPrep
      (Fin.cases hGrid (fun j => Fin.elim0 j)))))))
  let formula : BoundedFormula 8 := BoundedFormula.exPairFields 0
    (BoundedFormula.fairPreparationStepFormula 3 4 5 6 7 8 9 1 0)
  have selected := M.bounded_separation_mem separation formula params ground
    (M.prod_mem pairing unions powers separation states states)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params))
      (ZFSet.prod (M.fairPreparationStates Q stages U E0 enumSelector)
        (M.fairPreparationStates Q stages U E0 enumSelector)) =
      M.fairPreparationTransition Q stages U E0 enumSelector prepSelector gridGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, fairPreparationTransition, ZFSet.mem_sep]
    apply and_congr Iff.rfl
    simp only [formula, BoundedFormula.truth_exPairFields, BoundedFormula.truth_fairPreparationStepFormula]
    rfl
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

private theorem finiteHistory_bound (k : Nat) {E history : ZFSet.{u}}
    (ground : history ∈ M.sets) (function : ZFSet.IsFunc (natSetCode k) E history) :
    history ∈ M.groundRelations ZFSet.omega E := by
  refine (M.mem_groundRelations _ _ _).2 ⟨ground, ?_⟩
  intro z member
  obtain ⟨i, hi, e, he, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
  obtain ⟨n, _, rfl⟩ := (mem_natSetCode i k).1 hi
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, he⟩

theorem exists_fairPreparation_initial
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (stages U : ZFSet.{u}) {Q E0 enumSelector p : ZFSet.{u}}
    (hE0 : E0 ∈ M.sets) (enumerated : ZFSet.IsFunc Q E0 enumSelector) (member : p ∈ Q) :
    ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧
      ZFSet.pair ∅ (ZFSet.pair p (ZFSet.pair {ZFSet.pair ∅ e} ∅)) ∈
        M.fairPreparationStates Q stages U E0 enumSelector := by
  obtain ⟨e, selected, _⟩ := enumerated.2 p member
  have he := (ZFSet.pair_mem_prod.1 (enumerated.1 selected)).2
  have initial := finiteBirthHistory_initial he
  have historyBound := M.finiteHistory_bound 1
    (M.finiteBirthHistory_initial_mem pairing (M.transitive hE0 he)) initial.1
  refine ⟨e, he, selected, (M.mem_fairPreparationStates _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
  · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.omega_zero, ZFSet.pair_mem_prod.2
      ⟨member, ZFSet.pair_mem_prod.2 ⟨historyBound, ZFSet.mem_insert _ _⟩⟩⟩
  · exact ⟨∅, p, {ZFSet.pair ∅ e}, ∅, rfl, ZFSet.omega_zero,
      ZFSet.omega_succ ZFSet.omega_zero, initial.1, e, he, selected, (initial.2 e).2 rfl⟩

theorem fairPreparationTransition_serial
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {Q stages U E0 enumSelector prepSelector : ZFSet.{u}}
    (hE0 : E0 ∈ M.sets)
    (enumerated : ZFSet.IsFunc Q E0 enumSelector)
    (enumerationCases : ∀ e ∈ E0, e = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages e)
    (prepared : ZFSet.IsFunc (ZFSet.prod stages Q) U prepSelector)
    (outputs : ∀ y ∈ U, ∃ p ∈ Q, ∃ payload, y = ZFSet.pair p payload) :
    let grid := natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv
    ∀ state ∈ M.fairPreparationStates Q stages U E0 enumSelector,
      ∃ next ∈ M.fairPreparationStates Q stages U E0 enumSelector,
        ZFSet.pair state next ∈
          M.fairPreparationTransition Q stages U E0 enumSelector prepSelector grid := by
  let grid : ZFSet.{u} := natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv
  dsimp only
  intro state member
  obtain ⟨bound, n, p, births, last, rfl, hn, _hSucc, birthFunction, _current⟩ :=
    (M.mem_fairPreparationStates _ _ _ _ _ _).1 member
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  have upperParts := (ZFSet.pair_mem_prod.1 bound).2
  have hp := (ZFSet.pair_mem_prod.1 upperParts).1
  have historyBound := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 upperParts).2).1
  have birthGround := ((M.mem_groundRelations _ _ _).1 historyBound).1
  change ZFSet.IsFunc (natSetCode (k + 1)) E0 births at birthFunction
  obtain ⟨e, he, lookup, _⟩ := birthHistory_scheduled_lookup k birthFunction
  have gridEntry : ZFSet.pair (natSetCode k)
      (ZFSet.pair (natSetCode (Nat.unpair k).1) (natSetCode (Nat.unpair k).2)) ∈ grid :=
    (natPresentation.pair_mem_graph (natPresentation.product natPresentation)
      omegaGridEquiv ⟨k⟩ (omegaGridEquiv ⟨k⟩)).2 rfl
  have chooseNext : ∃ q ∈ Q, ∃ event ∈ insert ∅ (ZFSet.prod stages U),
      ((e = ∅ ∧ q = p ∧ event = ∅) ∨
        (∃ alpha ∈ stages, ∃ y ∈ U, (∃ payload, y = ZFSet.pair q payload) ∧
          ZFSet.pair (natSetCode (Nat.unpair k).2) alpha ∈ e ∧
          ZFSet.pair (ZFSet.pair alpha p) y ∈ prepSelector ∧ event = ZFSet.pair alpha y)) := by
    rcases enumerationCases e he with idle | active
    · exact ⟨p, hp, ∅, ZFSet.mem_insert _ _, Or.inl ⟨idle, rfl, rfl⟩⟩
    · obtain ⟨alpha, level, _⟩ := active.2 _ (natSetCode_mem_omega (Nat.unpair k).2)
      have hAlpha := (ZFSet.pair_mem_prod.1 (active.1 level)).2
      obtain ⟨y, selected, _⟩ := prepared.2 _ (ZFSet.pair_mem_prod.2 ⟨hAlpha, hp⟩)
      have hy := (ZFSet.pair_mem_prod.1 (prepared.1 selected)).2
      obtain ⟨q, hq, payload, equal⟩ := outputs y hy
      exact ⟨q, hq, ZFSet.pair alpha y,
        ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.2 ⟨hAlpha, hy⟩),
        Or.inr ⟨alpha, hAlpha, y, hy, ⟨payload, equal⟩, level, selected, rfl⟩⟩
  obtain ⟨q, hq, event, hEvent, branch⟩ := chooseNext
  obtain ⟨newE, selected, _⟩ := enumerated.2 q hq
  have hNewE := (ZFSet.pair_mem_prod.1 (enumerated.1 selected)).2
  let nextBirths := insert (ZFSet.pair (natSetCode (k + 1)) newE) births
  have nextFunction := finiteBirthHistory_extend (k + 1) birthFunction hNewE
  have nextGround := M.finiteBirthHistory_extend_mem pairing unions separation infinite
    (k + 1) birthGround (M.transitive hE0 hNewE)
  have nextBound := M.finiteHistory_bound (k + 1 + 1) nextGround nextFunction.1
  let next := ZFSet.pair (natSetCode (k + 1)) (ZFSet.pair q (ZFSet.pair nextBirths event))
  have nextMember : next ∈ M.fairPreparationStates Q stages U E0 enumSelector := by
    apply (M.mem_fairPreparationStates _ _ _ _ _ _).2
    refine ⟨ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _,
      ZFSet.pair_mem_prod.2 ⟨hq, ZFSet.pair_mem_prod.2 ⟨nextBound, hEvent⟩⟩⟩, ?_⟩
    exact ⟨natSetCode (k + 1), q, nextBirths, event, rfl, natSetCode_mem_omega _,
      ZFSet.omega_succ (natSetCode_mem_omega _), nextFunction.1,
      newE, hNewE, selected, (nextFunction.2.2.2 newE).2 rfl⟩
  refine ⟨next, nextMember, (M.pair_mem_fairPreparationTransition _ _ _ _ _ _ _ _ _).2
    ⟨member, nextMember, ?_⟩⟩
  exact ⟨natSetCode k, p, births, last, natSetCode (k + 1), q, nextBirths, event,
    rfl, rfl, rfl, natSetCode (Nat.unpair k).1, natSetCode_mem_omega _,
    natSetCode (Nat.unpair k).2, natSetCode_mem_omega _, e, he, newE, hNewE,
    gridEntry, lookup, selected, rfl, branch⟩





theorem exists_groundFairPreparationOrbit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q stages U E0 enumSelector prepSelector p : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (hEnum : enumSelector ∈ M.sets) (hPrep : prepSelector ∈ M.sets)
    (enumerated : ZFSet.IsFunc Q E0 enumSelector)
    (enumerationCases : ∀ e ∈ E0, e = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages e)
    (prepared : ZFSet.IsFunc (ZFSet.prod stages Q) U prepSelector)
    (outputs : ∀ y ∈ U, ∃ q ∈ Q, ∃ payload, y = ZFSet.pair q payload)
    (member : p ∈ Q) :
    let grid := natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv
    let states := M.fairPreparationStates Q stages U E0 enumSelector
    let transition := M.fairPreparationTransition Q stages U E0 enumSelector prepSelector grid
    states ∈ M.sets ∧ transition ∈ M.sets ∧
      ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧ ∃ orbit ∈ M.sets,
        ZFSet.IsFunc ZFSet.omega states orbit ∧
        (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
          state = ZFSet.pair ∅ (ZFSet.pair p (ZFSet.pair {ZFSet.pair ∅ e} ∅))) ∧
        ∀ n ∈ ZFSet.omega, ∀ state next,
          ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
          ZFSet.pair state next ∈ transition ∧
            FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector grid state next := by
  dsimp only
  have omega := M.omega_mem separation infinite
  have gridGround := M.omega_grid_equiv_graph_mem pairing unions powers separation infinite
  have statesGround := M.fairPreparationStates_mem pairing unions powers separation
    hQ hStages hU hE0 hEnum omega
  have transitionGround := M.fairPreparationTransition_mem pairing unions powers separation
    hQ hStages hU hE0 hEnum hPrep gridGround omega
  obtain ⟨e, he, selected, initial⟩ :=
    M.exists_fairPreparation_initial pairing stages U hE0 enumerated member
  have serial := M.fairPreparationTransition_serial pairing unions separation infinite
    hE0 enumerated enumerationCases prepared outputs
  obtain ⟨orbit, ground, function, start, steps⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice
      statesGround transitionGround initial serial
  refine ⟨statesGround, transitionGround, e, he, selected, orbit, ground, function, start, ?_⟩
  intro n hn state next first second
  have edge := steps n hn state next first second
  exact ⟨edge, ((M.pair_mem_fairPreparationTransition _ _ _ _ _ _ _ _ _).1 edge).2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationRelation_strengthens
    (stages packed Q upperOrder nodes T alpha p r payload : ZFSet.{u})
    (entry : ZFSet.pair (ZFSet.pair alpha p) (ZFSet.pair r payload) ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T) :
    ZFSet.pair r p ∈ upperOrder := by
  obtain ⟨_, _, _, fields, _, _, _, _, code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T
      alpha p (ZFSet.pair r payload)).1 entry
  obtain ⟨_row, _A, r', _k, _enumerations, _q, _input, output, below, _rest⟩ := code
  obtain ⟨rfl, _⟩ := ZFSet.pair_inj.1 output
  exact below

theorem fairPreparationStep_strengthens
    (omega E0 stages U enumSelector prepSelector gridGraph packed Q upperOrder nodes T : ZFSet.{u})
    (selected : prepSelector ⊆ M.varyingPreparationRelation stages packed Q upperOrder nodes T)
    (n p births last m q nextBirths event : ZFSet.{u})
    (reflexive : ZFSet.pair p p ∈ upperOrder)
    (step : FairPreparationStepCode omega E0 stages U enumSelector prepSelector gridGraph
      (ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)))
      (ZFSet.pair m (ZFSet.pair q (ZFSet.pair nextBirths event)))) :
    ZFSet.pair q p ∈ upperOrder := by
  obtain ⟨n', p', births', last', m', q', nextBirths', event', first, second,
    _clock, _i, _hi, _j, _hj, _e, _he, _newE, _hNewE, _grid, _lookup,
    _newLookup, _append, action⟩ := step
  have oldCondition : p = p' := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 first).2).1
  have newCondition : q = q' := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 second).2).1
  rw [oldCondition, newCondition]
  rcases action with idle | ⟨alpha, _, y, _, ⟨payload, equal⟩, _, chosen, _⟩
  · rw [idle.2.1, ← oldCondition]
    exact reflexive
  · exact M.varyingPreparationRelation_strengthens stages packed Q upperOrder nodes T
      alpha p' q' payload (equal ▸ selected chosen)

end PartitionPilot.Forcing.TransitiveGround

end OAI
