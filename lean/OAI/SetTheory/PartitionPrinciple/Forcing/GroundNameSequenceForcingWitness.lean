import OAI.SetTheory.PartitionPrinciple.Forcing.IndexedTupleNames

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u

namespace Name
variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def sequenceDecision (one : P) (τ : Name s)
    (p : P) (n a : ZFSet.{u}) : Prop :=
  ForcesMem p (check s one (ZFSet.pair n a)) τ

theorem sequenceDecision_mono (one : P) (τ : Name s) {p q : P}
    (before : q ≤ p) {n a : ZFSet.{u}} (decision : sequenceDecision s one τ p n a) :
    sequenceDecision s one τ q n a := forcesMem_mono decision before

end Name

namespace SetFormula

def nameSequenceDecisionFormula : SetFormula 7 :=
  ex (ex (.conj (orderedPairFormula 1 3 4)
    (.conj (binaryApplication uniformCheckFormula (extend 8 Fin.elim0) 1 0)
      (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
        (extend 6 (extend 7 Fin.elim0)) 2 (extend 0 (extend 5 Fin.elim0))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_nameSequenceDecisionFormula (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (τ : (M.nameDomain s).names) (p : P) (n a : ZFSet.{u})
    (hn : n ∈ M.sets) (ha : a ∈ M.sets) :
    Realize M.sets nameSequenceDecisionFormula
      (extend (s.encode p) (extend n (extend a (extend τ.val.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))) ↔
      Name.sequenceDecision s one τ.val p n a := by
  have hone := M.transitive carrier (s.encode_mem one)
  have hp := M.transitive carrier (s.encode_mem p)
  have hpair := M.orderedPair_mem pairing hn ha
  have hcheck := M.check_mem s one pairing unions powers separation collection hone _ hpair
  let checked : (M.nameDomain s).names := ⟨Name.check s one (ZFSet.pair n a), hcheck⟩
  let env := extend (s.encode p) (extend n (extend a (extend τ.val.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))
  have forcing :
      Realize M.sets
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          (extend 6 (extend 7 Fin.elim0)) 2 (extend 0 (extend 5 Fin.elim0)))
        (extend checked.val.val (extend (ZFSet.pair n a) env)) ↔
      Name.sequenceDecision s one τ.val p n a :=
    M.realize_ordinaryGroundForcing s pairing unions powers separation collection carrier order
      0 1 (.mem 0 1) (extend 6 (extend 7 Fin.elim0)) 2 (extend 0 (extend 5 Fin.elim0))
      _ rfl rfl p (extend checked (extend τ Fin.elim0)) rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))
  rw [nameSequenceDecisionFormula, realize_ex]
  constructor
  · rintro ⟨v, hv, rest⟩
    obtain ⟨w, hw, pair, check, forced⟩ := (realize_ex M.sets _ _).1 rest
    have pairEq : v = ZFSet.pair n a := (M.realize_orderedPairFormula pairing 1 3 4
      (extend w (extend v env)) hv hn ha).1 pair
    rw [realize_binaryApplication, map_extend, map_empty] at check
    have checkEq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection
      hone v w hv hw).1 check
    subst v
    subst w
    exact forcing.1 forced
  · intro decision
    refine ⟨ZFSet.pair n a, hpair, ?_⟩
    rw [realize_ex]
    refine ⟨checked.val.val, hcheck, ?_, ?_, forcing.2 decision⟩
    · exact (M.realize_orderedPairFormula pairing 1 3 4
        (extend checked.val.val (extend (ZFSet.pair n a) env)) hpair hn ha).2 rfl
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection
        hone _ _ hpair hcheck).2 rfl

end TransitiveGround

namespace Name
variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def sequenceDecisionRelation (one : P) (τ : Name s) (N U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p : P, ∃ n ∈ N, ∃ a ∈ U,
    z = ZFSet.pair (ZFSet.pair (s.encode p) n) a ∧ sequenceDecision s one τ p n a)
      (ZFSet.prod (ZFSet.prod s.carrier N) U)

theorem mem_sequenceDecisionRelation (one : P) (τ : Name s) (N U z : ZFSet.{u}) :
    z ∈ sequenceDecisionRelation s one τ N U ↔
      ∃ p : P, ∃ n ∈ N, ∃ a ∈ U,
        z = ZFSet.pair (ZFSet.pair (s.encode p) n) a ∧ sequenceDecision s one τ p n a := by
  rw [sequenceDecisionRelation, ZFSet.mem_sep]
  refine ⟨fun h => h.2, ?_⟩
  rintro ⟨p, n, hn, a, ha, rfl, decision⟩
  exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨s.encode_mem p, hn⟩, ha⟩,
    p, n, hn, a, ha, rfl, decision⟩

theorem sequenceDecisionRelation_entry (one : P) (τ : Name s) (N U : ZFSet.{u})
    (p : P) (n a : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ sequenceDecisionRelation s one τ N U ↔
      n ∈ N ∧ a ∈ U ∧ sequenceDecision s one τ p n a := by
  rw [mem_sequenceDecisionRelation]
  constructor
  · rintro ⟨q, m, hm, b, hb, equal, decision⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨condition, rfl⟩ := ZFSet.pair_inj.1 inner
    have same := s.injective condition
    subst q
    exact ⟨hm, hb, decision⟩
  · rintro ⟨hn, ha, decision⟩
    exact ⟨p, n, hn, a, ha, rfl, decision⟩

end Name

namespace SetFormula

def nameSequenceDecisionEntryFormula : SetFormula 7 :=
  ex (ex (ex (.conj (.mem 2 7) (.conj (.mem 1 4) (.conj (.mem 0 5)
    (.conj (BoundedFormula.orderedTripleFormula 3 2 1 0).toFormula
      (reindex (extend 2 (extend 1 (extend 0 (extend 6
        (extend 7 (extend 8 (extend 9 Fin.elim0))))))) nameSequenceDecisionFormula)))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_nameSequenceDecisionEntryFormula (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (τ : (M.nameDomain s).names) {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets nameSequenceDecisionEntryFormula
      (extend z (extend N (extend U (extend τ.val.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))) ↔
      z ∈ Name.sequenceDecisionRelation s one τ.val N U := by
  let env := extend z (extend N (extend U (extend τ.val.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))
  have members : ∀ j, env j ∈ M.sets := Fin.cases hz (Fin.cases hN (Fin.cases hU
    (Fin.cases τ.property (Fin.cases carrier (Fin.cases order
      (Fin.cases (M.transitive carrier (s.encode_mem one)) (fun i => Fin.elim0 i)))))))
  have shape (p n a : ZFSet.{u}) (hp : p ∈ M.sets) (hn : n ∈ M.sets) (ha : a ∈ M.sets) :
      Realize M.sets (BoundedFormula.orderedTripleFormula 3 2 1 0).toFormula
        (extend a (extend n (extend p env))) ↔ z = ZFSet.pair (ZFSet.pair p n) a :=
    (BoundedFormula.realize_toFormula M _ _ (Fin.cases ha (Fin.cases hn (Fin.cases hp members)))).trans
      (BoundedFormula.truth_orderedTripleFormula 3 2 1 0 _)
  rw [nameSequenceDecisionEntryFormula, realize_ex, Name.mem_sequenceDecisionRelation]
  constructor
  · rintro ⟨v, hv, rest⟩
    obtain ⟨n, hnM, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨a, haM, hvP, hn, ha, pair, decision⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨p, rfl⟩ := (s.mem_carrier v).1 hvP
    rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
      map_extend, map_extend, map_empty] at decision
    exact ⟨p, n, hn, a, ha, (shape _ _ _ hv hnM haM).1 pair,
      (M.realize_nameSequenceDecisionFormula s one pairing unions powers separation collection
        carrier order τ p n a hnM haM).1 decision⟩
  · rintro ⟨p, n, hn, a, ha, pair, decision⟩
    have hp := M.transitive carrier (s.encode_mem p)
    have hnM := M.transitive hN hn
    have haM := M.transitive hU ha
    refine ⟨s.encode p, hp, ?_⟩
    rw [realize_ex]
    refine ⟨n, hnM, ?_⟩
    rw [realize_ex]
    refine ⟨a, haM, s.encode_mem p, hn, ha, (shape _ _ _ hp hnM haM).2 pair, ?_⟩
    rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
      map_extend, map_extend, map_empty]
    exact (M.realize_nameSequenceDecisionFormula s one pairing unions powers separation collection
      carrier order τ p n a hnM haM).2 decision

theorem sequenceDecisionRelation_mem (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (τ : (M.nameDomain s).names) {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets) :
    Name.sequenceDecisionRelation s one τ.val N U ∈ M.sets := by
  let params := extend N (extend U (extend τ.val.val (extend s.carrier
    (extend s.conditionOrder (extend (s.encode one) Fin.elim0)))))
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation carrier hN) hU
  have selected := M.separation_mem separation nameSequenceDecisionEntryFormula params
    (Fin.cases hN (Fin.cases hU (Fin.cases τ.property (Fin.cases carrier
      (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem one))
        (fun i => Fin.elim0 i))))))) bound
  have equal : ZFSet.sep (fun z => Realize M.sets nameSequenceDecisionEntryFormula (extend z params))
      (ZFSet.prod (ZFSet.prod s.carrier N) U) = Name.sequenceDecisionRelation s one τ.val N U := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, code⟩
      exact (M.realize_nameSequenceDecisionEntryFormula s one pairing unions powers separation
        collection carrier order τ hN hU z (M.transitive bound hz)).1 code
    · intro hz
      have bounded := (ZFSet.mem_sep.1 hz).1
      exact ⟨bounded, (M.realize_nameSequenceDecisionEntryFormula s one pairing unions powers separation
        collection carrier order τ hN hU z (M.transitive bound bounded)).2 hz⟩
  exact equal ▸ selected

end TransitiveGround
end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)

noncomputable def sequenceFunctionNameEnv {N U : ZFSet.{u}}
    (hN : N ∈ M.sets) (hU : U ∈ M.sets) (τ : (M.nameDomain s).names) :
    Assignment (M.nameDomain s) 3 :=
  extend ⟨Name.check s ⊤ N, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) N hN⟩
    (extend ⟨Name.check s ⊤ U, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) U hU⟩ (extend τ Fin.elim0))

theorem sequenceFunction_eval {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s))) {p₀ : P} (hp₀ : H.mem p₀)
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p₀) :
    ZFSet.IsFunc N U (Name.eval {q | H.mem q} τ.val) := by
  let env := M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  have truth := forces_sound (M.nameDomain s) H generic _ env hp₀ forced
  have function := (BoundedFormula.truth_functionFormula 0 1 2
    (evalAssignment {q | H.mem q} env)).1
      ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨env j, rfl⟩)).1 truth)
  change ZFSet.IsFunc (Name.eval {q | H.mem q} (Name.check s ⊤ N))
    (Name.eval {q | H.mem q} (Name.check s ⊤ U)) (Name.eval {q | H.mem q} τ.val) at function
  simpa only [Name.eval_check (s := s) {q | H.mem q} ⊤ H.top_mem] using function

include pairing unions powers separation collection carrier in
theorem sequenceDecision_reading (τ : (M.nameDomain s).names) (n a : ZFSet.{u})
    (hn : n ∈ M.sets) (ha : a ∈ M.sets) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    ZFSet.pair n a ∈ Name.eval {q | H.mem q} τ.val ↔
      ∃ p, H.mem p ∧ Name.sequenceDecision s ⊤ τ.val p n a := by
  have hcheck := M.check_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) _ (M.orderedPair_mem pairing hn ha)
  have exactReading := Name.eval_mem_iff_forcesMem (M.nameDomain s) H
    (fun E member => generic E (Or.inl member)) hcheck τ.property
  simpa only [Name.eval_check (s := s) {q | H.mem q} ⊤ H.top_mem, Name.sequenceDecision] using exactReading

theorem sequenceDecision_unique_below (small : M.sets.Countable)
    {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets) (τ : (M.nameDomain s).names)
    {p₀ : P}
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p₀)
    {p : P} (before : p ≤ p₀) {n a b : ZFSet.{u}} (hn : n ∈ N) (ha : a ∈ U) (hb : b ∈ U)
    (first : Name.sequenceDecision s ⊤ τ.val p n a)
    (second : Name.sequenceDecision s ⊤ τ.val p n b) : a = b := by
  let : Countable P := M.conditions_countable s small carrier
  obtain ⟨H, hp, generic⟩ := exists_generic_formulaFamily (M.nameDomain s)
    (M.nameDomain_countable s small) p
  have function := M.sequenceFunction_eval s pairing unions powers separation collection carrier
    hN hU τ H generic (H.upward hp before) forced
  have firstEntry := (M.sequenceDecision_reading s pairing unions powers separation collection carrier
    τ n a (M.transitive hN hn) (M.transitive hU ha) H generic).2 ⟨p, hp, first⟩
  have secondEntry := (M.sequenceDecision_reading s pairing unions powers separation collection carrier
    τ n b (M.transitive hN hn) (M.transitive hU hb) H generic).2 ⟨p, hp, second⟩
  obtain ⟨v, _, unique⟩ := function.2 n hn
  exact (unique a firstEntry).trans (unique b secondEntry).symm

theorem sequenceDecision_dense_below (small : M.sets.Countable)
    {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets) (τ : (M.nameDomain s).names)
    {p₀ : P}
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p₀)
    {n : ZFSet.{u}} (hn : n ∈ N) :
    DenseBelow p₀ {q | ∃ a ∈ U, Name.sequenceDecision s ⊤ τ.val q n a} := by
  intro q before
  let : Countable P := M.conditions_countable s small carrier
  obtain ⟨H, hq, generic⟩ := exists_generic_formulaFamily (M.nameDomain s)
    (M.nameDomain_countable s small) q
  have function := M.sequenceFunction_eval s pairing unions powers separation collection carrier
    hN hU τ H generic (H.upward hq before) forced
  obtain ⟨a, entry, _⟩ := function.2 n hn
  have ha : a ∈ U := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨r, hr, decision⟩ := (M.sequenceDecision_reading s pairing unions powers separation collection
    carrier τ n a (M.transitive hN hn) (M.transitive hU ha) H generic).1 entry
  obtain ⟨t, _, tq, tr⟩ := H.directed hq hr
  exact ⟨t, tq, a, ha, Name.sequenceDecision_mono s ⊤ τ.val tr decision⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)

theorem exists_sequenceFunction_forcing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)
    {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (function : ZFSet.IsFunc N U (Name.eval {q | H.mem q} τ.val)) :
    ∃ p, H.mem p ∧ Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p := by
  let env := M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  apply (forcing_truth (M.nameDomain s) H generic _ env).1
  apply (BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨env j, rfl⟩)).2
  apply (BoundedFormula.truth_functionFormula 0 1 2 (evalAssignment {q | H.mem q} env)).2
  change ZFSet.IsFunc (Name.eval {q | H.mem q} (Name.check s ⊤ N))
    (Name.eval {q | H.mem q} (Name.check s ⊤ U)) (Name.eval {q | H.mem q} τ.val)
  simpa only [Name.eval_check (s := s) {q | H.mem q} ⊤ H.top_mem] using function

end TransitiveGround

end PartitionPilot.Forcing

end OAI
