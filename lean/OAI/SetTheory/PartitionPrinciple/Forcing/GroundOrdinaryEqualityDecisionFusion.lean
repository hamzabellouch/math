import OAI.SetTheory.PartitionPrinciple.Definability.GroundDefinableRelationProducts

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_ordinaryEqualityDecisions (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      M.ordinaryEqualityDecisions (env 1) (env 2) (env 0) (env 3)) := by
  let defined := (M.definable_separation separation
    (ordinaryEqualityDecisionFormula 1 2 0 3 4)).reindex (![1, 1, 2, 0, 3] : Fin 5 → Fin 4)
  refine defined.congr ?_
  intro env
  apply congrArg (fun params : Fin 4 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets (ordinaryEqualityDecisionFormula 1 2 0 3 4)
      (extend z params)) (env 1))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) j

theorem ordinaryEqualityDecisions_mem (separation : SeparationSchema M.sets)
    {Q order sigma tau : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hSigma : sigma ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryEqualityDecisions Q order sigma tau ∈ M.sets :=
  (M.definable_ordinaryEqualityDecisions separation).closed ![sigma, Q, order, tau]
    (Fin.cases hSigma (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))))

noncomputable def ordinaryEqualityDecisionFamily (T Q order tau : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun sigma : T => sigma.val)
    (fun sigma => M.ordinaryEqualityDecisions Q order sigma.val tau)

theorem pair_mem_ordinaryEqualityDecisionFamily (T Q order tau sigma D : ZFSet.{u}) :
    ZFSet.pair sigma D ∈ M.ordinaryEqualityDecisionFamily T Q order tau ↔
      sigma ∈ T ∧ D = M.ordinaryEqualityDecisions Q order sigma tau := by
  rw [ordinaryEqualityDecisionFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, equal⟩
    obtain ⟨hx, hd⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx ▸ x.property, hd.symm.trans (congrArg (fun y => M.ordinaryEqualityDecisions Q order y tau) hx)⟩
  · rintro ⟨member, rfl⟩
    exact ⟨⟨sigma, member⟩, rfl⟩

theorem ordinaryEqualityDecisionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryEqualityDecisionFamily T Q order tau ∈ M.sets :=
  (M.definable_ordinaryEqualityDecisions separation).graph_mem pairing separation collection
    ![Q, order, tau] (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))) hT

theorem ordinaryEqualityDecisionFamily_function
    (separation : SeparationSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    ZFSet.IsFunc T (M.groundPower Q) (M.ordinaryEqualityDecisionFamily T Q order tau) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨sigma, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨sigma.property, (M.mem_groundPower Q _).2
      ⟨M.ordinaryEqualityDecisions_mem separation hQ hOrder (M.transitive hT sigma.property) hTau,
        M.ordinaryEqualityDecisions_subset Q order sigma.val tau⟩⟩
  · intro sigma hSigma
    exact ⟨M.ordinaryEqualityDecisions Q order sigma tau,
      (M.pair_mem_ordinaryEqualityDecisionFamily T Q order tau sigma _).2 ⟨hSigma, rfl⟩,
      fun D entry => (M.pair_mem_ordinaryEqualityDecisionFamily T Q order tau sigma D).1 entry |>.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryEqualityDecisions_simultaneous_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (small : M.groundEmbeddable T ZFSet.omega)
    (valid : ∀ sigma ∈ T, IsName s sigma)
    (closed : InternallyCountablyClosed M s) (tau : (M.nameDomain s).names) (base : P) :
    DenseBelow base {q | q ≤ base ∧ ∀ sigma : (M.nameDomain s).names,
      sigma.val.val ∈ T → Name.ForcesEq q sigma.val tau.val ∨
        ∀ r, r ≤ q → ¬ Name.ForcesEq r sigma.val tau.val} := by
  let f := M.ordinaryEqualityDecisionFamily T s.carrier s.conditionOrder tau.val.val
  have hf : f ∈ M.sets := M.ordinaryEqualityDecisionFamily_mem
    pairing separation collection hT carrier order tau.property
  have function : ZFSet.IsFunc T (M.groundPower s.carrier) f :=
    M.ordinaryEqualityDecisionFamily_function separation hT carrier order tau.property
  have persistent : ∀ z E, ZFSet.pair z E ∈ f → ∀ p q : P,
      q ≤ p → s.encode p ∈ E → s.encode q ∈ E := by
    intro z E ef p q qp member
    obtain ⟨hz, rfl⟩ := (M.pair_mem_ordinaryEqualityDecisionFamily
      T s.carrier s.conditionOrder tau.val.val z E).1 ef
    let sigma : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    have first := (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection
      carrier order sigma tau p).1 member
    apply (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection
      carrier order sigma tau q).2
    rcases first with equal | negative
    · exact Or.inl (Name.forcesEq_mono equal qp)
    · exact Or.inr (fun r rq => negative r (rq.trans qp))
  have dense : ∀ z E, ZFSet.pair z E ∈ f → DenseBelow base {q | s.encode q ∈ E} := by
    intro z E ef p _
    obtain ⟨hz, rfl⟩ := (M.pair_mem_ordinaryEqualityDecisionFamily
      T s.carrier s.conditionOrder tau.val.val z E).1 ef
    let sigma : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    obtain ⟨raw, member, before⟩ := M.ordinaryEqualityDecisions_dense s pairing unions powers
      separation collection carrier order sigma tau (s.encode p) (s.encode_mem p)
    obtain ⟨q, rfl⟩ := (s.mem_carrier raw).1
      (M.ordinaryEqualityDecisions_subset s.carrier s.conditionOrder z tau.val.val member)
    exact ⟨q, (s.pair_mem_conditionOrder q p).1 before, member⟩
  have common := M.internally_countableDenseFamily_denseBelow s pairing unions powers separation
    infinite choice carrier order hT hf small function closed base persistent dense
  intro p pb
  obtain ⟨q, qp, qb, all⟩ := common p pb
  refine ⟨q, qp, qb, ?_⟩
  intro sigma member
  exact (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection
    carrier order sigma tau q).1 (all sigma.val.val _
      ((M.pair_mem_ordinaryEqualityDecisionFamily T s.carrier s.conditionOrder tau.val.val
        sigma.val.val _).2 ⟨member, rfl⟩))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
