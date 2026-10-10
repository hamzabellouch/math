import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBelowInitialCompression
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRawRefinementDataIdentification
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementHistoryPrefixLevels

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions pairing unions powers separation hK

theorem product {A B : ZFSet.{u}}
    (first : A ∈ M.sets ∧ GroundBelow M A K) (second : B ∈ M.sets ∧ GroundBelow M B K) :
    ZFSet.prod A B ∈ M.sets ∧ GroundBelow M (ZFSet.prod A B) K :=
  ⟨M.prod_mem pairing unions powers separation first.1 second.1,
    GroundBelow.product pairing unions powers separation first.1 second.1 hK
      conditions.1 conditions.2.2.2 first.2 second.2⟩

theorem power {A : ZFSet.{u}} (small : A ∈ M.sets ∧ GroundBelow M A K) :
    M.groundPower A ∈ M.sets ∧ GroundBelow M (M.groundPower A) K :=
  ⟨M.groundPower_mem powers small.1,
    conditions.2.2.2.power_closed pairing unions powers separation small.1 hK small.2⟩

include infinite in
theorem singleton {a : ZFSet.{u}} (ha : a ∈ M.sets) :
    ({a} : ZFSet.{u}) ∈ M.sets ∧ GroundBelow M ({a} : ZFSet.{u}) K := by
  refine ⟨?_, GroundBelow.singleton pairing unions powers separation infinite hK conditions.2.1 ha⟩
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha

include infinite in
theorem natural (n : Nat) : natSetCode n ∈ M.sets ∧ GroundBelow M (natSetCode n) K :=
  ⟨M.natSetCode_mem separation infinite n,
    GroundBelow.of_member pairing unions powers separation hK
      (conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega n))⟩

include infinite choice in
theorem binary_union {A B : ZFSet.{u}}
    (first : A ∈ M.sets ∧ GroundBelow M A K) (second : B ∈ M.sets ∧ GroundBelow M B K) :
    A ∪ B ∈ M.sets ∧ GroundBelow M (A ∪ B) K :=
  ⟨M.binary_union_mem pairing unions first.1 second.1,
    GroundBelow.binary_union pairing unions powers separation infinite choice first.1 second.1 hK
      conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 first.2 second.2⟩

include choice in
theorem sUnion {R : ZFSet.{u}} (family : R ∈ M.sets ∧ GroundBelow M R K)
    (small : ∀ A ∈ R, GroundBelow M A K) :
    (⋃₀ R) ∈ M.sets ∧ GroundBelow M (⋃₀ R) K :=
  ⟨M.union_mem unions family.1, GroundBelow.sUnion pairing unions powers separation choice family.1 hK
    conditions.1 conditions.2.2.1 conditions.2.2.2 family.2 small⟩

end PartitionPilot.Forcing.GroundInaccessibleConditions

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite choice hK

theorem finite_family_union (n : Nat) (family : Fin n → ZFSet.{u})
    (small : ∀ i, family i ∈ M.sets ∧ GroundBelow M (family i) K) :
    ∃ U, U ∈ M.sets ∧ GroundBelow M U K ∧
      ∀ x, x ∈ U ↔ ∃ i, x ∈ family i := by
  induction n with
  | zero =>
    refine ⟨∅, M.empty_mem ⟨K, hK⟩,
      (GroundBelow.empty_iff hK).2 ⟨ZFSet.omega, conditions.2.1⟩, ?_⟩
    intro x
    constructor
    · intro h
      exact False.elim (ZFSet.notMem_empty x h)
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨U, hU, smallU, members⟩ := ih (fun i => family i.succ) (fun i => small i.succ)
    have whole := conditions.binary_union pairing unions powers separation infinite choice hK
      (small 0) ⟨hU, smallU⟩
    refine ⟨family 0 ∪ U, whole.1, whole.2, ?_⟩
    intro x
    rw [ZFSet.mem_union, members]
    constructor
    · rintro (first | ⟨i, later⟩)
      · exact ⟨0, first⟩
      · exact ⟨i.succ, later⟩
    · rintro ⟨i, member⟩
      exact Fin.cases (fun h => Or.inl h)
        (fun j h => Or.inr ⟨j, h⟩) i member

end PartitionPilot.Forcing.GroundInaccessibleConditions

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable {n : Nat} {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

noncomputable def historyUnionStepDefinition (defined : GroundDefinableFunction M f) :
    GroundDefinableFunction M (fun env : Fin (n + 2) → ZFSet.{u} =>
      f (extend (refinementHistoryIndices (env 0) (env 1)) (fun j => env j.succ.succ))) := by
  let earlier := (M.definable_historyUnion pairing unions separation).reindex
    ![(0 : Fin (n + 2)), 1]
  exact defined.comp (Fin.cases earlier
    (fun j => GroundDefinableFunction.projection M j.succ.succ))

include pairing unions separation in
theorem exists_historyUnionTrace (collection : CollectionSchema M.sets)
    (defined : GroundDefinableFunction M f) (params : Fin n → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets)
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets, OrdinalRecursionTrace
      (fun alpha prior output => output = f (extend (refinementHistoryIndices alpha prior) params))
      stages history := by
  let operation := M.historyUnionStepDefinition pairing unions separation defined
  let slots : Fin (n + 3) → Fin (n + 3) :=
    Fin.cases 2 (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)))
  let formula := SetFormula.reindex slots operation.formula
  have recognize (alpha prior output : ZFSet.{u}) (ha : alpha ∈ M.sets)
      (hp : prior ∈ M.sets) (ho : output ∈ M.sets) :
      Realize M.sets formula (extend alpha (extend prior (extend output params))) ↔
        output = f (extend (refinementHistoryIndices alpha prior) params) := by
    rw [show formula = SetFormula.reindex slots operation.formula from rfl, realize_reindex]
    have eqEnv : (fun i => extend alpha (extend prior (extend output params)) (slots i)) =
        extend output (extend alpha (extend prior params)) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j) i
    rw [eqEnv]
    exact operation.correct (extend alpha (extend prior params))
      (Fin.cases ha (Fin.cases hp members)) output ho
  have closure : GroundOrdinalStepClosure M stages formula params := by
    intro alpha member prior hp _
    have ha := M.transitive hs member
    have outputGround := operation.closed (extend alpha (extend prior params))
      (Fin.cases ha (Fin.cases hp members))
    refine ⟨_, outputGround, (recognize alpha prior _ ha hp outputGround).2 rfl, ?_⟩
    intro z hz relation
    exact (recognize alpha prior z ha hp hz).1 relation
  obtain ⟨history, hh, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hs ordinal formula params members closure
  refine ⟨history, hh, trace.1, ?_⟩
  intro alpha member output entry
  have step := trace.2 alpha member output entry
  exact (recognize alpha _ output (M.transitive hs member) step.1 step.2.1).1 step.2.2

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable {I K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (phi : ZFSet.{u} → ZFSet.{u})
variable (preserves : ∀ X ∈ M.sets, X ⊆ I → GroundBelow M X K →
  phi X ⊆ I ∧ GroundBelow M (phi X) K)
include pairing unions powers separation choice hK conditions preserves

theorem historyUnionTrace_below :
    ∀ stages ∈ K, ∀ history ∈ M.sets,
      OrdinalRecursionTrace (fun alpha prior output => output = phi (refinementHistoryIndices alpha prior))
        stages history →
      (∀ alpha Y, ZFSet.pair alpha Y ∈ history → Y ⊆ I ∧ GroundBelow M Y K) ∧
      refinementHistoryIndices stages history ⊆ I ∧
      GroundBelow M (refinementHistoryIndices stages history) K := by
  intro stages
  induction stages using ZFSet.inductionOn with
  | h stages ih =>
    intro hStages history hh trace
    have hs := M.transitive hK hStages
    have ordinal := ordinalSetProperty_member conditions.1 hStages
    have fibers : ∀ alpha Y, ZFSet.pair alpha Y ∈ history → Y ⊆ I ∧ GroundBelow M Y K := by
      intro alpha Y entry
      have member := trace.1.pair_source entry
      have ha := M.transitive hs member
      have lower := ih alpha member (conditions.1.1 stages hStages alpha member)
        (graphRestriction alpha history) (M.graphRestriction_mem unions separation ha hh)
        (trace.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member))
      have earlierGround := M.refinementHistoryIndices_mem unions separation ha
        (M.graphRestriction_mem unions separation ha hh)
      have result := preserves _ earlierGround lower.2.1 lower.2.2
      exact (trace.2 alpha member Y entry).symm ▸ result
    refine ⟨fibers, ?_, ?_⟩
    · intro x hx
      obtain ⟨alpha, _, Y, entry, inside⟩ := (mem_refinementHistoryIndices stages history x).1 hx
      exact (fibers alpha Y entry).1 inside
    · exact GroundBelow.indexed_sUnion pairing unions powers separation choice hs
        (M.union_mem unions (M.union_mem unions hh)) hh hK conditions.1
        conditions.2.2.1 conditions.2.2.2 (GroundBelow.of_member pairing unions powers separation hK hStages)
        trace.1.to_isFunc (fun alpha Y entry => (fibers alpha Y entry).2)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include pairing unions powers separation infinite hK conditions

theorem refinementIndexBound_below {level nodes T1 T2 P : ZFSet.{u}}
    (hl : level ∈ M.sets) (hn : nodes ∈ M.sets)
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) (hP : P ∈ M.sets)
    (smallNodes : GroundBelow M nodes K) (smallT1 : GroundBelow M T1 K)
    (smallT2 : GroundBelow M T2 K) (smallP : GroundBelow M P K) :
    refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P) ∈ M.sets ∧
      GroundBelow M (refinementIndexBound {level} nodes
        (M.groundRelations T1 P) (M.groundRelations T2 P)) K := by
  have first : M.groundRelations T1 P ∈ M.sets ∧ GroundBelow M (M.groundRelations T1 P) K :=
    ⟨M.groundRelations_mem pairing unions powers separation hT1 hP,
      GroundBelow.relations pairing unions powers separation hT1 hP hK
        conditions.1 conditions.2.2.2 smallT1 smallP⟩
  have second : M.groundRelations T2 P ∈ M.sets ∧ GroundBelow M (M.groundRelations T2 P) K :=
    ⟨M.groundRelations_mem pairing unions powers separation hT2 hP,
      GroundBelow.relations pairing unions powers separation hT2 hP hK
        conditions.1 conditions.2.2.2 smallT2 smallP⟩
  have node : nodes ∈ M.sets ∧ GroundBelow M nodes K := ⟨hn, smallNodes⟩
  have tag := conditions.singleton pairing unions powers separation infinite hK hl
  exact conditions.product pairing unions powers separation hK tag
    (conditions.product pairing unions powers separation hK node
      (conditions.product pairing unions powers separation hK node
        (conditions.product pairing unions powers separation hK first
          (conditions.product pairing unions powers separation hK second second))))

theorem refinementIndices_below
    {level nodes r candidates relations T1 T2 T P order top : ZFSet.{u}}
    (hl : level ∈ M.sets) (hn : nodes ∈ M.sets) (hr : r ∈ M.sets)
    (hc : candidates ∈ M.sets) (hrel : relations ∈ M.sets)
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets)
    (smallNodes : GroundBelow M nodes K) (smallT1 : GroundBelow M T1 K)
    (smallT2 : GroundBelow M T2 K) (smallP : GroundBelow M P K) :
    M.refinementIndices level nodes r candidates relations T1 T2 T P order top ∈ M.sets ∧
      GroundBelow M (M.refinementIndices level nodes r candidates relations T1 T2 T P order top) K := by
  have ground := M.refinementIndices_mem pairing unions powers separation
    hl hn hr hc hrel hT1 hT2 hT hP ho ht
  have bound := M.refinementIndexBound_below pairing unions powers separation infinite hK conditions
    hl hn hT1 hT2 hP smallNodes smallT1 smallT2 smallP
  exact ⟨ground, bound.2.restrict separation ground hK (fun _ member => (ZFSet.mem_sep.1 member).1)⟩

theorem rawRefinementFormulaData_indices_below
    (collection : CollectionSchema M.sets)
    (P order top action G nodes nodeOrder basis T T2 level : ZFSet.{u})
    (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets) (ha : action ∈ M.sets)
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hl : level ∈ M.sets)
    (smallP : GroundBelow M P K) (smallNodes : GroundBelow M nodes K)
    (smallT : GroundBelow M T K) (smallT2 : GroundBelow M T2 K) :
    M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0 ∈ M.sets ∧
      GroundBelow M (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) K := by
  let params : Fin 11 → ZFSet.{u} := ![P, order, top, action, G, nodes, nodeOrder, basis, T, T2, level]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hP (Fin.cases ho (Fin.cases ht
    (Fin.cases ha (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hl (fun j => Fin.elim0 j)))))))))))
  have code := (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection).closed params members
  have ground := M.nonemptyTupleCode_field_mem 14
    (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level) code 0
  have bound := M.refinementIndexBound_below pairing unions powers separation infinite hK conditions
    hl hn hT hT2 hP smallNodes smallT smallT2 smallP
  exact ⟨ground, bound.2.restrict separation ground hK (fun _ member => (ZFSet.mem_sep.1 member).1)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
