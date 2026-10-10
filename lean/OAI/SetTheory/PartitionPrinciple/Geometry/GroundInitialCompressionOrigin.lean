import OAI.SetTheory.PartitionPrinciple.Definability.GroundBoundedCompressionHeights
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialCompletedCompressionCertificates
import OAI.SetTheory.PartitionPrinciple.Models.GroundCoherentHeightChoices
import OAI.SetTheory.PartitionPrinciple.Transfinite.CompressionPrefixCoinitiality
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologicalCompressionCoinitiality
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionBirths

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def heightCandidateStates
    (B Ps Rs C D rD original K : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ h ∈ B,
    ∃ P ∈ Ps.sUnion.sUnion, ∃ r ∈ Rs.sUnion.sUnion,
      z = ZFSet.pair n h ∧ ZFSet.pair n P ∈ Ps ∧ ZFSet.pair n r ∈ Rs ∧
      StrictLexHeightCode P C D r h rD ∧ original ⊆ h ∧
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ K)
    (ZFSet.prod ZFSet.omega B)

theorem heightCandidateStates_subset (B Ps Rs C D rD original K : ZFSet.{u}) :
    heightCandidateStates B Ps Rs C D rD original K ⊆ ZFSet.prod ZFSet.omega B :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_heightCandidateStates (B Ps Rs C D rD original K z : ZFSet.{u}) :
    z ∈ heightCandidateStates B Ps Rs C D rD original K ↔
      ∃ n ∈ ZFSet.omega, ∃ h ∈ B, ∃ P ∈ Ps.sUnion.sUnion, ∃ r ∈ Rs.sUnion.sUnion,
        z = ZFSet.pair n h ∧ ZFSet.pair n P ∈ Ps ∧ ZFSet.pair n r ∈ Rs ∧
        StrictLexHeightCode P C D r h rD ∧ original ⊆ h ∧
        ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ K := by
  rw [heightCandidateStates, ZFSet.mem_sep]
  constructor
  · exact fun member => member.2
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨n, hn, h, hh, _, _, _, _, heq, _⟩ := witness
    rw [heq]
    exact ZFSet.pair_mem_prod.2 ⟨hn, hh⟩

theorem pair_mem_heightCandidateStates {B Ps Rs C D rD original K n h P r : ZFSet.{u}}
    (domains : FunctionGraphOn ZFSet.omega Ps) (orders : FunctionGraphOn ZFSet.omega Rs)
    (domainEntry : ZFSet.pair n P ∈ Ps) (orderEntry : ZFSet.pair n r ∈ Rs) :
    ZFSet.pair n h ∈ heightCandidateStates B Ps Rs C D rD original K ↔
      h ∈ B ∧ StrictLexHeightCode P C D r h rD ∧ original ⊆ h ∧
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ K := by
  rw [mem_heightCandidateStates]
  constructor
  · rintro ⟨m, _, f, hf, Q, _, s, _, equal, first, second, code, old, columns⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have domainEq := domains.unique first domainEntry
    have orderEq := orders.unique second orderEntry
    subst Q
    subst s
    exact ⟨hf, code, old, columns⟩
  · rintro ⟨hh, code, old, columns⟩
    exact ⟨n, domains.pair_source domainEntry, h, hh,
      P, pair_second_mem_doubleUnion domainEntry, r, pair_second_mem_doubleUnion orderEntry,
      rfl, domainEntry, orderEntry, code, old, columns⟩





namespace BoundedFormula
open SetFormula

def heightCandidateEntryFormula {n}
    (z omega B Ps Rs C D rD original K boundPs boundRs : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem omega (exMem B.succ (exMem boundPs.succ.succ (exMem boundRs.succ.succ.succ
    (.conj (orderedPairFormula (lift z) 3 2)
      (.conj (pairMembershipFormula 3 1 (lift Ps))
        (.conj (pairMembershipFormula 3 0 (lift Rs))
          (.conj (strictLexHeightFormula 1 (lift C) (lift D) 0 2 (lift rD))
            (.conj (subsetFormula (lift original) 2)
              (heightColumnsBoundFormula 1 (lift C) (lift D) 2 (lift K))))))))))

theorem truth_heightCandidateEntryFormula {n}
    (z omega B Ps Rs C D rD original K boundPs boundRs : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (heightCandidateEntryFormula z omega B Ps Rs C D rD original K boundPs boundRs) env ↔
      ∃ a ∈ env omega, ∃ h ∈ env B, ∃ P ∈ env boundPs, ∃ r ∈ env boundRs,
        env z = ZFSet.pair a h ∧ ZFSet.pair a P ∈ env Ps ∧ ZFSet.pair a r ∈ env Rs ∧
        StrictLexHeightCode P (env C) (env D) r h (env rD) ∧ env original ⊆ h ∧
        ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ env K := by
  simp only [heightCandidateEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_strictLexHeightFormula, truth_subsetFormula,
    truth_heightColumnsBoundFormula]
  constructor
  · rintro ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old, columns⟩
    refine ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old, ?_⟩
    intro x c q entry
    have shape := ZFSet.pair_mem_prod.1 (code.function.1 entry)
    have coordinates := ZFSet.pair_mem_prod.1 shape.2
    exact columns x shape.1 c coordinates.1 q coordinates.2 entry
  · rintro ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old, columns⟩
    exact ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old,
      fun x _ c _ q _ entry => columns x c q entry⟩

end BoundedFormula

namespace TransitiveGround
open SetFormula

theorem heightCandidateStates_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hOmega : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {B Ps Rs C D rD original K : ZFSet.{u}}
    (hB : B ∈ M.sets) (hPs : Ps ∈ M.sets) (hRs : Rs ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hOriginal : original ∈ M.sets) (hK : K ∈ M.sets) :
    heightCandidateStates B Ps Rs C D rD original K ∈ M.sets := by
  have boundPs := M.union_mem unions (M.union_mem unions hPs)
  have boundRs := M.union_mem unions (M.union_mem unions hRs)
  let params := extend ZFSet.omega (extend B (extend Ps (extend Rs (extend C
    (extend D (extend rD (extend original (extend K
      (extend Ps.sUnion.sUnion (extend Rs.sUnion.sUnion Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightCandidateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) params
    (Fin.cases hOmega (Fin.cases hB (Fin.cases hPs (Fin.cases hRs (Fin.cases hC
      (Fin.cases hD (Fin.cases hrD (Fin.cases hOriginal (Fin.cases hK
        (Fin.cases boundPs (Fin.cases boundRs (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation hOmega hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightCandidateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) (extend z params))
      (ZFSet.prod ZFSet.omega B) = heightCandidateStates B Ps Rs C D rD original K := by
    apply ZFSet.ext
    intro z
    rw [heightCandidateStates, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightCandidateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_template_constancy (P G r μ A Labels : ZFSet.{u}) :
    RecursiveTemplateConstancy P r μ (M.initialCompressionData P G r μ A Labels) :=
  ⟨rfl, rfl, rfl⟩

theorem initialCompressionData_iterate_template_constancy
    (P G r μ A Labels Reps : ZFSet.{u}) (n : Nat) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    RecursiveTemplateConstancy P r μ
      ((M.initialCompressionData P G r μ A Labels).iterate M I Sources Reps G T n) :=
  (M.initialCompressionData_template_constancy P G r μ A Labels).iterate M _ _ Reps G _ n

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (union : GroundCompressionUnionData M state.data I Sources Reps G m one T)
include union

theorem exists_groundHeightFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Ps Rs C D rD c original : ZFSet.{u}}
    (hPs : Ps ∈ M.sets) (hRs : Rs ∈ M.sets)
    (domains : FunctionGraphOn ZFSet.omega Ps) (orders : FunctionGraphOn ZFSet.omega Rs)
    (domainEntries : ∀ n P, ZFSet.pair (natSetCode n) P ∈ Ps ↔
      P = (state.data.iterate M I Sources Reps G T n).D)
    (orderEntries : ∀ n r, ZFSet.pair (natSetCode n) r ∈ Rs ↔
      r = (state.data.iterate M I Sources Reps G T n).rD)
    (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      (∀ h, ZFSet.pair (natSetCode 0) h ∈ family ↔ h = original) ∧
      (∀ n h, ZFSet.pair (natSetCode n) h ∈ family →
        StrictLexHeightCode (state.data.iterate M I Sources Reps G T n).D C D
          (state.data.iterate M I Sources Reps G T n).rD h rD ∧ original ⊆ h ∧
          ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ h → a ∈ heightColumns P0 C D original) ∧
      ∀ n h k, ZFSet.pair (natSetCode n) h ∈ family →
        ZFSet.pair (natSetCode (n + 1)) k ∈ family → h ⊆ k := by
  let stages := state.data.iterate M I Sources Reps G T
  let B := M.groundRelations (union.fields 0) (ZFSet.prod C D)
  let K := heightColumns P0 C D original
  let W := heightCandidateStates B Ps Rs C D rD original K
  have hOmega := M.omega_mem separation infinite
  have hB : B ∈ M.sets := M.groundRelations_mem pairing unions powers separation
    (union.ground 0) (M.prod_mem pairing unions powers separation hC hD)
  have hK : K ∈ M.sets := M.heightColumns_mem pairing unions powers separation hP0 hC hD hOriginal
  have hW : W ∈ M.sets := M.heightCandidateStates_mem pairing unions powers separation
    hOmega hB hPs hRs hC hD hrD hOriginal hK
  have graphBound {P height : ZFSet.{u}} (ground : height ∈ M.sets)
      (function : ZFSet.IsFunc P (ZFSet.prod C D) height)
      (subset : P ⊆ union.fields 0) : height ∈ B := by
    apply (M.mem_groundRelations _ _ _).2
    refine ⟨ground, ?_⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, hy⟩
  have candidate (n : Nat) (height : ZFSet.{u}) :
      ZFSet.pair (natSetCode n) height ∈ W ↔ height ∈ B ∧
        StrictLexHeightCode (stages n).D C D (stages n).rD height rD ∧ original ⊆ height ∧
        ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ K :=
    pair_mem_heightCandidateStates domains orders
      ((domainEntries n _).2 rfl) ((orderEntries n _).2 rfl)
  have originalAtZero : StrictLexHeightCode (stages 0).D C D (stages 0).rD original rD := by
    simpa only [stages, RecursiveStateData.iterate_zero, initialDomain, initialOrder] using originalCode
  have start : ZFSet.pair ∅ original ∈ W := by
    apply (candidate 0 original).2
    exact ⟨graphBound hOriginal originalAtZero.function ((union.fieldUnion 0).subset 0),
      originalAtZero, fun _ hx => hx, fun _ _ _ entry => mem_heightColumns_of_entry originalCode.function entry⟩
  have extendable : ∀ n ∈ ZFSet.omega, ∀ old, ZFSet.pair n old ∈ W →
      ∃ height, ZFSet.pair (insert n n) height ∈ W ∧ old ⊆ height := by
    intro index hIndex old member
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode index).1 hIndex
    obtain ⟨oldBound, oldCode, extension, bounded⟩ := (candidate n old).1 member
    have hOld := ((M.mem_groundRelations _ _ _).1 oldBound).1
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
      rw [equal]
      exact constant.iterate M I Sources Reps G T n
    have currentCode : StrictLexHeightCode current.data.D C D current.data.rD old rD := by
      simpa only [equal] using oldCode
    obtain ⟨height, hHeight, heightCode, inclusion, originalInclusion, columnBound⟩ :=
      current.exists_column_bounded_height_step pairing unions powers separation collection infinite choice
        currentConstant hP0 hC hD hrD hc hOriginal hOld originalCode currentCode columns target above
        coordinateInjection originalSmall extension bounded
    have nextCode : StrictLexHeightCode (stages (n + 1)).D C D (stages (n + 1)).rD height rD := by
      change StrictLexHeightCode (stages n).currentCarrier C D (stages n).currentOrder height rD
      simpa only [equal] using heightCode
    refine ⟨height, ?_, inclusion⟩
    exact (candidate (n + 1) height).2
      ⟨graphBound hHeight nextCode.function ((union.fieldUnion 0).subset (n + 1)),
        nextCode, originalInclusion, columnBound⟩
  obtain ⟨family, hFamily, function, zero, selected, adjacent⟩ := M.exists_groundCoherentChoices
    pairing unions powers separation infinite choice hW hB
      (heightCandidateStates_subset _ _ _ _ _ _ _ _) start extendable
  refine ⟨family, hFamily, ⟨B, function⟩, zero, ?_, ?_⟩
  · intro n height entry
    exact ((candidate n height).1 (selected _ (natSetCode_mem_omega n) height entry)).2
  · intro n height next first second
    exact adjacent (natSetCode n) (natSetCode_mem_omega n) height next first second

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (union : GroundCompressionUnionData M state.data I Sources Reps G m one T)

theorem exists_groundHeightData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {C D rD c original : ZFSet.{u}}
    (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega) :
    Nonempty (GroundCompressionHeightData M state.data I Sources Reps G m one T union P0 C D rD original) := by
  have hOmega := M.omega_mem separation infinite
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  obtain ⟨Ps, hPs, domains, domainEntries⟩ := M.exists_groundStateFieldFamily pairing separation collection
    hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 0
  obtain ⟨Rs, hRs, orders, orderEntries⟩ := M.exists_groundStateFieldFamily pairing separation collection
    hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 1
  obtain ⟨family, hFamily, function, zero, finite, adjacent⟩ := state.exists_groundHeightFamily union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hPs hRs domains orders domainEntries orderEntries
    hP0 hC hD hrD hc hOriginal originalCode columns target above coordinateInjection originalSmall
  have zeroEq : function.natValue 0 = original := (zero _).1 (function.natValue_entry 0)
  have codes := fun n => (finite n _ (function.natValue_entry n)).1
  have mono := fun n => adjacent n _ _ (function.natValue_entry n) (function.natValue_entry (n + 1))
  have columnBounds := fun n => (finite n _ (function.natValue_entry n)).2.2
  obtain ⟨height, hHeight, exactUnion, code, exactEntries, bound⟩ := M.exists_groundCoherentHeightUnion
    unions separation hOmega hFamily function (union.fieldUnion 0) (union.fieldUnion 1)
    (fun n => (state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n).1.order)
    codes mono columnBounds
  obtain ⟨rangeGround, rangeCountable⟩ := M.countable_height_range_of_old_columns
    pairing unions powers separation infinite choice hP0 (union.ground 0) hC hD hOriginal hHeight
    originalSmall ⟨c, hc, coordinateInjection⟩ bound
  refine ⟨{
    family := family
    family_ground := hFamily
    function := function
    zero := zeroEq
    finite := codes
    adjacent := mono
    height := height
    height_ground := hHeight
    exact_union := exactUnion
    code := code
    finite_entries := exactEntries
    original_entries := ?_
    range_ground := rangeGround
    range_countable := rangeCountable
    columns := bound
  }⟩
  intro x hx y
  have hxZero : x ∈ (state.data.iterate M I Sources Reps G T 0).D := by
    simpa only [RecursiveStateData.iterate_zero, initialDomain] using hx
  simpa only [zeroEq] using exactEntries 0 x hxZero y

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialHeightedCompression
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        Nonempty (GroundHeightedCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  have accounting := state.initial_union_range_accounting algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl rfl
  obtain ⟨completion⟩ := state.completion_of_accounting algebra pairing unions powers separation
    hI hSources hReps hG hT accounting
  have initialDomain : state.data.D = P := by rw [initialData]; rfl
  have initialOrder : state.data.rD = r := by rw [initialData]; rfl
  have constant : RecursiveTemplateConstancy P r μ state.data := by
    rw [initialData]
    exact M.initialCompressionData_template_constancy P G r μ A Labels
  obtain ⟨heights⟩ := state.exists_groundHeightData completion.algebra.union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hP hC hD hrD hc hOriginal originalCode columns target above
    coordinateInjection originalSmall
  exact ⟨⟨completion, heights⟩⟩





theorem exists_groundInitialProfiledCompression
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        Nonempty (GroundProfiledCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  have accounting := state.initial_union_range_accounting algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl rfl
  obtain ⟨completion⟩ := state.completion_of_accounting algebra pairing unions powers separation
    hI hSources hReps hG hT accounting
  have initialDomain : state.data.D = P := by rw [initialData]; rfl
  have initialOrder : state.data.rD = r := by rw [initialData]; rfl
  have constant : RecursiveTemplateConstancy P r μ state.data := by
    rw [initialData]
    exact M.initialCompressionData_template_constancy P G r μ A Labels
  obtain ⟨heights⟩ := state.exists_groundHeightData completion.algebra.union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hP hC hD hrD hc hOriginal originalCode columns target above
    coordinateInjection originalSmall
  have profiles := state.initial_union_profiles completion.algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl
  exact ⟨⟨⟨completion, heights⟩, profiles⟩⟩





theorem exists_groundInitialBornCompression
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (hOld : old ∈ M.sets) (ordinal : ordinalSetProperty base)
    (oldFunction : FunctionGraphOn P old)
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (oldMeet : OldMeetCode r μ old) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        Nonempty (GroundBornCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  have accounting := state.initial_union_range_accounting algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl rfl
  obtain ⟨completion⟩ := state.completion_of_accounting algebra pairing unions powers separation
    hI hSources hReps hG hT accounting
  have initialDomain : state.data.D = P := by rw [initialData]; rfl
  have initialOrder : state.data.rD = r := by rw [initialData]; rfl
  have constant : RecursiveTemplateConstancy P r μ state.data := by
    rw [initialData]
    exact M.initialCompressionData_template_constancy P G r μ A Labels
  obtain ⟨heights⟩ := state.exists_groundHeightData completion.algebra.union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hP hC hD hrD hc hOriginal originalCode columns target above
    coordinateInjection originalSmall
  have profiles := state.initial_union_profiles completion.algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl
  have initialBirthFunction : FunctionGraphOn state.data.D old := initialDomain.symm ▸ oldFunction
  have initialOldMeet : OldMeetCode state.data.rD state.data.μD old := by
    rw [initialData]
    exact oldMeet
  obtain ⟨births⟩ := state.exists_groundBirthData completion.algebra.union
    pairing unions powers separation collection infinite hI hSources hReps hG hT
    hBase hOld ordinal initialBirthFunction oldBound initialOldMeet
  exact ⟨⟨⟨⟨completion, heights⟩, profiles⟩, births⟩⟩





theorem exists_groundInitialCompressionOrigin
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        Nonempty (GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior) := by
  dsimp only
  have hOld : old ∈ M.sets := priorBirth ▸ prior.birth_mem base baseMember
  have oldFunction : FunctionGraphOn P old := by
    rw [← priorSpace, ← priorBirth]
    exact ⟨T0, prior.birth_function base baseMember⟩
  have oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base := by
    intro x t entry
    have priorEntry : ZFSet.pair x t ∈ prior.birth base := priorBirth.symm ▸ entry
    have hx := (ZFSet.pair_mem_prod.1 ((prior.birth_function base baseMember).1 priorEntry)).1
    exact (prior.birth_bound base baseMember x hx t priorEntry).symm
  have oldMeet : OldMeetCode r μ old := by
    rw [← priorOrder, ← priorMeet, ← priorBirth]
    exact prior.old_meet base baseMember
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ⟨seed, state, initialData⟩, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  have accounting := state.initial_union_range_accounting algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl rfl
  obtain ⟨completion⟩ := state.completion_of_accounting algebra pairing unions powers separation
    hI hSources hReps hG hT accounting
  have initialDomain : state.data.D = P := by rw [initialData]; rfl
  have initialOrder : state.data.rD = r := by rw [initialData]; rfl
  have constant : RecursiveTemplateConstancy P r μ state.data := by
    rw [initialData]
    exact M.initialCompressionData_template_constancy P G r μ A Labels
  obtain ⟨heights⟩ := state.exists_groundHeightData completion.algebra.union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hP hC hD hrD hc hOriginal originalCode columns target above
    coordinateInjection originalSmall
  have profiles := state.initial_union_profiles completion.algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl
  have initialBirthFunction : FunctionGraphOn state.data.D old := initialDomain.symm ▸ oldFunction
  have initialOldMeet : OldMeetCode state.data.rD state.data.μD old := by
    rw [initialData]
    exact oldMeet
  obtain ⟨births⟩ := state.exists_groundBirthData completion.algebra.union
    pairing unions powers separation collection infinite hI hSources hReps hG hT
    hBase hOld (ordinalSetProperty_member ordinal baseMember) initialBirthFunction oldBound initialOldMeet
  have initialMeet : state.data.μD = μ := by rw [initialData]; rfl
  let history := state.prefixHistory completion.algebra.union births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
    initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth
  refine ⟨⟨⟨⟨⟨completion, heights⟩, profiles⟩, births⟩, history, priorHeight, ?_, ?_, ?_⟩⟩
  · intro s before
    exact state.prefixHistory_old completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth before
  · intro n
    exact state.prefixHistory_stamp completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth n
  · exact state.prefixHistory_limit completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth

end PartitionPilot.Forcing.TransitiveGround

end OAI
