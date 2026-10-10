import OAI.SetTheory.PartitionPrinciple.Definability.GreedyAntichainStepFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawRefinementStageWitnesses

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem antichainEligible_mem (separation : SeparationSchema M.sets)
    {Q order D alpha prior : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hD : D ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hPrior : prior ∈ M.sets) :
    antichainEligible Q order D alpha prior ∈ M.sets := by
  let formula : BoundedFormula 6 := .neg (BoundedFormula.antichainBlockedFormula 0 1 2 3 4 5)
  let params := extend Q (extend order (extend D (extend alpha (extend prior Fin.elim0))))
  have ground := M.bounded_separation_mem separation formula params
    (Fin.cases hQ (Fin.cases hOrder (Fin.cases hD
      (Fin.cases hAlpha (Fin.cases hPrior (fun i => Fin.elim0 i)))))) hD
  have equal : ZFSet.sep (fun q => BoundedFormula.Truth formula (extend q params)) D =
      antichainEligible Q order D alpha prior := by
    apply ZFSet.ext
    intro q
    simp only [ZFSet.mem_sep, antichainEligible, formula, BoundedFormula.Truth,
      BoundedFormula.truth_antichainBlockedFormula]
    rfl
  exact equal ▸ ground

theorem greedyAntichainStep_exists_unique (separation : SeparationSchema M.sets)
    {Q order D c alpha prior : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hD : D ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hPrior : prior ∈ M.sets)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets D) c) :
    ∃ y ∈ M.sets, GreedyAntichainStep Q order D (M.nonemptyGroundSubsets D) c alpha prior y ∧
      ∀ z, GreedyAntichainStep Q order D (M.nonemptyGroundSubsets D) c alpha prior z → z = y := by
  classical
  let E := antichainEligible Q order D alpha prior
  have hE := M.antichainEligible_mem separation hQ hOrder hD hAlpha hPrior
  have subset : E ⊆ D := fun _ hq => (mem_antichainEligible _ _ _ _ _ _).1 hq |>.1
  by_cases nonempty : E.Nonempty
  · have member := (M.mem_nonemptyGroundSubsets D E).2 ⟨hE, subset, nonempty⟩
    obtain ⟨y, entry, unique⟩ := code.function.2 E member
    have hy := code.chosen E y entry
    refine ⟨y, M.transitive hD (subset hy), Or.inl ⟨E, member, rfl, entry⟩, ?_⟩
    intro z step
    rcases step with ⟨S, _, rfl, selected⟩ | ⟨empty, _⟩
    · exact unique z selected
    · exact False.elim (empty nonempty)
  · refine ⟨D, hD, Or.inr ⟨nonempty, rfl⟩, ?_⟩
    intro z step
    rcases step with ⟨S, member, rfl, _⟩ | ⟨_, equal⟩
    · exact False.elim (nonempty ((M.mem_nonemptyGroundSubsets D _).1 member).2.2)
    · exact equal

theorem exists_greedyAntichainTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {Q order D c C : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hD : D ∈ M.sets) (hc : c ∈ M.sets) (hC : C ∈ M.sets)
    (ordinal : ordinalSetProperty C)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets D) c) :
    ∃ history ∈ M.sets, OrdinalRecursionTrace
      (GreedyAntichainStep Q order D (M.nonemptyGroundSubsets D) c) C history := by
  let F := M.nonemptyGroundSubsets D
  have hF : F ∈ M.sets := M.nonemptyGroundSubsets_mem powers separation hD
  let params := extend Q (extend order (extend D (extend F (extend c Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hQ (Fin.cases hOrder (Fin.cases hD
      (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i)))))
  let formula : BoundedFormula 8 := BoundedFormula.greedyAntichainStepFormula 3 4 5 6 7 0 1 2
  have recognize (alpha prior y : ZFSet.{u}) (hAlpha : alpha ∈ M.sets)
      (hPrior : prior ∈ M.sets) (hy : y ∈ M.sets) :
      Realize M.sets formula.toFormula (extend alpha (extend prior (extend y params))) ↔
        GreedyAntichainStep Q order D F c alpha prior y :=
    (BoundedFormula.realize_toFormula M formula _
      (Fin.cases hAlpha (Fin.cases hPrior (Fin.cases hy members)))).trans
      (BoundedFormula.truth_greedyAntichainStepFormula 3 4 5 6 7 0 1 2 _)
  have closure : GroundOrdinalStepClosure M C formula.toFormula params := by
    intro alpha member prior hPrior _
    have hAlpha := M.transitive hC member
    obtain ⟨y, hy, step, unique⟩ :=
      M.greedyAntichainStep_exists_unique separation hQ hOrder hD hAlpha hPrior code
    exact ⟨y, hy, (recognize alpha prior y hAlpha hPrior hy).2 step,
      fun z hz relation => unique z ((recognize alpha prior z hAlpha hPrior hz).1 relation)⟩
  obtain ⟨history, hHistory, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hC ordinal formula.toFormula params members closure
  refine ⟨history, hHistory, trace.1, ?_⟩
  intro alpha member y entry
  have step := trace.2 alpha member y entry
  exact (recognize alpha _ y (M.transitive hC member) step.1 step.2.1).1 step.2.2

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem greedyAntichainTrace_relativeMaximal {Q order D F c C f alpha : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (conditions : D ⊆ Q) (hAlpha : alpha ∈ C)
    (exhausted : ¬ (antichainEligible Q order D alpha (graphRestriction alpha f)).Nonempty) :
    RelativeMaximalAntichainCode Q order D (relationImage alpha D f) := by
  classical
  refine ⟨fun p hp => ((mem_relationImage alpha D f p).1 hp).1,
    greedyAntichainTrace_antichain choice ordinal trace conditions
      (fun beta hBeta => ordinal.1 alpha hAlpha beta hBeta), ?_⟩
  intro q hq
  by_contra missing
  apply exhausted
  refine ⟨q, (mem_antichainEligible Q order D alpha (graphRestriction alpha f) q).2
    ⟨hq, ?_⟩⟩
  rintro ⟨beta, hBeta, p, hp, entry, r, hr, rq, rp⟩
  exact missing ⟨p, (mem_relationImage alpha D f p).2
    ⟨hp, beta, hBeta, (pair_mem_graphRestriction.1 entry).1⟩, r, hr, rq, rp⟩

theorem RelativeMaximalAntichainCode.predense {Q order D A : ZFSet.{u}}
    (code : RelativeMaximalAntichainCode Q order D A)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q)
    (dense : ∀ q ∈ Q, ∃ d ∈ D, ZFSet.pair d q ∈ order) :
    ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
      ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order := by
  intro q hq
  obtain ⟨d, hd, dq⟩ := dense q hq
  obtain ⟨p, hp, r, hr, rd, rp⟩ := code.2.2 d hd
  exact ⟨p, hp, r, hr, orderCode.trans r hr d (conditions hd) q hq rd dq, rp⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundRelativeMaximalAntichain
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q order D : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets) (hD : D ∈ M.sets)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q) :
    ∃ A ∈ M.sets, RelativeMaximalAntichainCode Q order D A := by
  let F := M.nonemptyGroundSubsets D
  have hF := M.nonemptyGroundSubsets_mem powers separation hD
  obtain ⟨c, hc, chooser⟩ := M.choice_witness choice hF
    (fun E hE => ((M.mem_nonemptyGroundSubsets D E).1 hE).2.2)
  obtain ⟨C, hC, ordinal, _, impossible⟩ := M.exists_groundHartogs
    pairing unions powers separation collection hD
  obtain ⟨f, hf, trace⟩ := M.exists_greedyAntichainTrace
    pairing unions powers separation collection hQ hOrder hD hc hC ordinal chooser
  obtain ⟨alpha, hAlpha, exhausted⟩ := greedyAntichainTrace_exhausts chooser ordinal trace
    orderCode conditions (fun injection => impossible ⟨f, hf, injection⟩)
  exact ⟨relationImage alpha D f,
    M.relationImage_mem separation (M.transitive hC hAlpha) hD hf,
    greedyAntichainTrace_relativeMaximal chooser ordinal trace conditions hAlpha exhausted⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_ordinaryMembershipDecisions (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      M.ordinaryMembershipDecisions (env 1) (env 2) (env 0) (env 3)) := by
  let defined := (M.definable_separation separation
    (ordinaryMembershipDecisionFormula 1 2 0 3 4)).reindex (![1, 1, 2, 0, 3] : Fin 5 → Fin 4)
  refine defined.congr ?_
  intro env
  apply congrArg (fun params : Fin 4 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets (ordinaryMembershipDecisionFormula 1 2 0 3 4)
      (extend z params)) (env 1))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) j

theorem ordinaryMembershipDecisions_mem (separation : SeparationSchema M.sets)
    {Q order sigma tau : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hSigma : sigma ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryMembershipDecisions Q order sigma tau ∈ M.sets :=
  (M.definable_ordinaryMembershipDecisions separation).closed ![sigma, Q, order, tau]
    (Fin.cases hSigma (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))))

noncomputable def ordinaryMembershipDecisionFamily (T Q order tau : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun sigma : T => sigma.val)
    (fun sigma => M.ordinaryMembershipDecisions Q order sigma.val tau)

theorem pair_mem_ordinaryMembershipDecisionFamily (T Q order tau sigma D : ZFSet.{u}) :
    ZFSet.pair sigma D ∈ M.ordinaryMembershipDecisionFamily T Q order tau ↔
      sigma ∈ T ∧ D = M.ordinaryMembershipDecisions Q order sigma tau := by
  rw [ordinaryMembershipDecisionFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, equal⟩
    obtain ⟨hx, hd⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx ▸ x.property, hd.symm.trans (congrArg (fun y => M.ordinaryMembershipDecisions Q order y tau) hx)⟩
  · rintro ⟨member, rfl⟩
    exact ⟨⟨sigma, member⟩, rfl⟩

theorem ordinaryMembershipDecisionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryMembershipDecisionFamily T Q order tau ∈ M.sets :=
  (M.definable_ordinaryMembershipDecisions separation).graph_mem pairing separation collection
    ![Q, order, tau] (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))) hT

theorem ordinaryMembershipDecisionFamily_function
    (separation : SeparationSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    ZFSet.IsFunc T (M.groundPower Q) (M.ordinaryMembershipDecisionFamily T Q order tau) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨sigma, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨sigma.property, (M.mem_groundPower Q _).2
      ⟨M.ordinaryMembershipDecisions_mem separation hQ hOrder (M.transitive hT sigma.property) hTau,
        M.ordinaryMembershipDecisions_subset Q order sigma.val tau⟩⟩
  · intro sigma hSigma
    exact ⟨M.ordinaryMembershipDecisions Q order sigma tau,
      (M.pair_mem_ordinaryMembershipDecisionFamily T Q order tau sigma _).2 ⟨hSigma, rfl⟩,
      fun D entry => (M.pair_mem_ordinaryMembershipDecisionFamily T Q order tau sigma D).1 entry |>.2⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryMembershipDecisionFamily_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ sigma ∈ T, IsName s sigma)
    (tau : (M.nameDomain s).names) :
    ∀ sigma D, ZFSet.pair sigma D ∈
      M.ordinaryMembershipDecisionFamily T s.carrier s.conditionOrder tau.val.val →
      ∀ p ∈ s.carrier, ∃ q ∈ D, ZFSet.pair q p ∈ s.conditionOrder := by
  intro sigma D entry
  obtain ⟨member, rfl⟩ := (M.pair_mem_ordinaryMembershipDecisionFamily
    T s.carrier s.conditionOrder tau.val.val sigma D).1 entry
  let name : (M.nameDomain s).names := ⟨⟨sigma, valid sigma member⟩, M.transitive hT member⟩
  exact M.ordinaryMembershipDecisions_dense s pairing unions powers separation collection carrier order name tau

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_relativeMaximalAntichainFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q order J domains : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hJ : J ∈ M.sets) (hDomains : domains ∈ M.sets)
    (orderCode : PartialOrderCode Q order)
    (domainsCode : ZFSet.IsFunc J (M.groundPower Q) domains) :
    ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
      ∀ j D A, ZFSet.pair j D ∈ domains → ZFSet.pair j A ∈ f →
        RelativeMaximalAntichainCode Q order D A := by
  let B := M.groundPower Q
  let formula : SetFormula 5 := (BoundedFormula.relativeAntichainFamilyFormula 0 1 2 3 4).toFormula
  let params := extend Q (extend order (extend domains Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hQ (Fin.cases hOrder (Fin.cases hDomains (fun i => Fin.elim0 i)))
  have recognize (j A : ZFSet.{u}) (hj : j ∈ M.sets) (hA : A ∈ M.sets) :
      Realize M.sets formula (extend j (extend A params)) ↔
        ∃ D, ZFSet.pair j D ∈ domains ∧ RelativeMaximalAntichainCode Q order D A :=
    (BoundedFormula.realize_toFormula M _ _ (Fin.cases hj (Fin.cases hA members))).trans
      (BoundedFormula.truth_relativeAntichainFamilyFormula 0 1 2 3 4 _)
  have hB : B ∈ M.sets := M.groundPower_mem powers hQ
  let relation := M.definableRelation formula params J B
  have ground : relation ∈ M.sets := M.definableRelation_mem
    pairing unions powers separation formula params members hJ hB
  have total : ∀ j ∈ J, ∃ A ∈ B, ZFSet.pair j A ∈ relation := by
    intro j hj
    obtain ⟨D, entry, _⟩ := domainsCode.2 j hj
    have domain := (M.mem_groundPower Q D).1 (ZFSet.pair_mem_prod.1 (domainsCode.1 entry)).2
    obtain ⟨A, hA, code⟩ := M.exists_groundRelativeMaximalAntichain
      pairing unions powers separation collection choice hQ hOrder domain.1 orderCode domain.2
    have inB : A ∈ B := (M.mem_groundPower Q A).2 ⟨hA, code.2.1.1⟩
    exact ⟨A, inB, (M.pair_mem_definableRelation formula params J B j A).2
      ⟨hj, inB, (recognize j A (M.transitive hJ hj) hA).2 ⟨D, entry, code⟩⟩⟩
  obtain ⟨f, hf, function, selected⟩ := M.uniformize_relation
    pairing unions powers separation choice hJ hB ground total
  refine ⟨f, hf, function, ?_⟩
  intro j D A domainEntry chosen
  obtain ⟨hj, hA, holds⟩ := (M.pair_mem_definableRelation formula params J B j A).1 (selected chosen)
  obtain ⟨D', entry, code⟩ := (recognize j A (M.transitive hJ hj)
    ((M.mem_groundPower Q A).1 hA).1).1 holds
  obtain ⟨value, _, unique⟩ := domainsCode.2 j hj
  have equal : D' = D := (unique D' entry).trans (unique D domainEntry).symm
  exact equal ▸ code

theorem exists_smallRelativeAntichainFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q order J domains K : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hJ : J ∈ M.sets) (hDomains : domains ∈ M.sets) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) (orderCode : PartialOrderCode Q order)
    (domainsCode : ZFSet.IsFunc J (M.groundPower Q) domains)
    (smallJ : GroundBelow M J K)
    (chain : ∀ A ∈ M.sets, OrderAntichainCode Q order A → GroundBelow M A K) :
    ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
      (∀ j D A, ZFSet.pair j D ∈ domains → ZFSet.pair j A ∈ f →
        RelativeMaximalAntichainCode Q order D A) ∧
      let U := ⋃₀ relationImage J (M.groundPower Q) f
      U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q := by
  obtain ⟨f, hf, function, selected⟩ := M.exists_relativeMaximalAntichainFamily
    pairing unions powers separation collection choice hQ hOrder hJ hDomains orderCode domainsCode
  have hPower := M.groundPower_mem powers hQ
  have small : ∀ j A, ZFSet.pair j A ∈ f → GroundBelow M A K := by
    intro j A entry
    have pair := ZFSet.pair_mem_prod.1 (function.1 entry)
    obtain ⟨D, domainEntry, _⟩ := domainsCode.2 j pair.1
    exact chain A ((M.mem_groundPower Q A).1 pair.2).1
      (selected j D A domainEntry entry).2.1
  refine ⟨f, hf, function, selected,
    M.union_mem unions (M.relationImage_mem separation hJ hPower hf),
    GroundBelow.indexed_sUnion pairing unions powers separation choice hJ hPower hf hK
      conditions.1 conditions.2.2.1 conditions.2.2.2 smallJ function small, ?_⟩
  intro q member
  obtain ⟨A, inRange, inA⟩ := ZFSet.mem_sUnion.1 member
  have inPower := ((mem_relationImage J (M.groundPower Q) f A).1 inRange).1
  exact ((M.mem_groundPower Q A).1 inPower).2 inA

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)

theorem exists_ordinaryMembershipAntichainFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T K : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ sigma ∈ T, IsName s sigma)
    (tau : (M.nameDomain s).names) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) (smallT : GroundBelow M T K)
    (chain : ∀ A ∈ M.sets, OrderAntichainCode s.carrier s.conditionOrder A → GroundBelow M A K) :
    ∃ f ∈ M.sets, ZFSet.IsFunc T (M.groundPower s.carrier) f ∧
      (∀ sigma A, ZFSet.pair sigma A ∈ f →
        RelativeMaximalAntichainCode s.carrier s.conditionOrder
          (M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma tau.val.val) A ∧
        ∀ q ∈ s.carrier, ∃ p ∈ A, ∃ r ∈ s.carrier,
          ZFSet.pair r q ∈ s.conditionOrder ∧ ZFSet.pair r p ∈ s.conditionOrder) ∧
      let U := ⋃₀ relationImage T (M.groundPower s.carrier) f
      U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ s.carrier := by
  let domains := M.ordinaryMembershipDecisionFamily T s.carrier s.conditionOrder tau.val.val
  have hDomains : domains ∈ M.sets := M.ordinaryMembershipDecisionFamily_mem
    pairing separation collection hT carrier order tau.property
  have domainsCode : ZFSet.IsFunc T (M.groundPower s.carrier) domains :=
    M.ordinaryMembershipDecisionFamily_function separation hT carrier order tau.property
  obtain ⟨f, hf, function, selected, whole⟩ := M.exists_smallRelativeAntichainFamily
    pairing unions powers separation collection choice carrier order hT hDomains hK conditions
    s.conditionOrder_code domainsCode smallT chain
  refine ⟨f, hf, function, ?_, whole⟩
  intro sigma A entry
  have hSigma := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  have domainEntry : ZFSet.pair sigma
      (M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma tau.val.val) ∈ domains :=
    (M.pair_mem_ordinaryMembershipDecisionFamily T s.carrier s.conditionOrder tau.val.val sigma _).2
      ⟨hSigma, rfl⟩
  have code := selected sigma _ A domainEntry entry
  exact ⟨code, code.predense s.conditionOrder_code
    (M.ordinaryMembershipDecisions_subset s.carrier s.conditionOrder sigma tau.val.val)
    (M.ordinaryMembershipDecisionFamily_dense s pairing unions powers separation collection carrier order
      hT valid tau sigma _ domainEntry)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
