import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNicePreparationWitnessBounds
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRefinementCollisionSymmetry
import OAI.SetTheory.PartitionPrinciple.Geometry.StructuralPreparationSourceImages

namespace OAI


namespace PartitionPilot.Forcing.SynchronizedEnumerationCode
universe u

theorem codomain_mono {omega N N' B f e names : ZFSet.{u}}
    (code : SynchronizedEnumerationCode omega N B f e names) (subset : N ⊆ N') :
    SynchronizedEnumerationCode omega N' B f e names := by
  have widen {A graph : ZFSet.{u}} (function : ZFSet.IsFunc A N graph) :
      ZFSet.IsFunc A N' graph := by
    refine ⟨?_, function.2⟩
    intro z member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hx, subset hy⟩
  exact ⟨widen code.1, code.2.1, widen code.2.2.1, code.2.2.2⟩

end PartitionPilot.Forcing.SynchronizedEnumerationCode



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem preparedCertificateCode_of_selected
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet J : ZFSet.{u}) (validJ : ∀ tau ∈ J, IsName s tau)
    (H : ConditionFilter P) (z : (M.nameDomain s).names)
    (F B f e names : ZFSet.{u}) (p : P)
    (selected : ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈
      M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (filter : MeetFilterCode b.carrier nodeOrder meet F) (nonempty : B.Nonempty)
    (profile : M.DecidesVisibilityProfile a s b K T F z.val p)
    (equalities : ∀ v ∈ B, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T K → ZFSet.pair v tau.val ∈ f →
        Name.ForcesEq p z.val tau)
    (enumerated : SynchronizedEnumerationCode ZFSet.omega
      (M.niceSupportNameCodes a s T K) B f e names) :
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p) b.carrier nodeOrder meet
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤)
      ZFSet.omega z.val.val F B f e names := by
  obtain ⟨_, _, _, _, _, nodes, basis, coinitial, function, supported⟩ :=
    M.supportedCertificateFamily_groundData a s b T K nodeOrder J validJ H
      z.val.val F B f selected
  have inside : M.niceSupportNameCodes a s T K ⊆ M.groundRelations T s.carrier := by
    intro tau member
    obtain ⟨ground, i, code⟩ := (M.mem_niceSupportNameCodes a s T K tau).1 member
    exact M.niceNameCandidates_subset a s T (K i)
      ((M.mem_niceNameCandidates a s T (K i) tau).2 ⟨ground, code⟩)
  have range : f ⊆ ZFSet.prod b.carrier (M.groundRelations T s.carrier) := by
    intro entry member
    obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨nodes (basis hv), inside htau⟩
  have valid : ∀ tau ∈ M.groundRelations T s.carrier, IsName s tau := by
    intro tau member
    exact Name.isName_of_subset validT ((M.mem_groundRelations T s.carrier tau).1 member).2
  refine ⟨filter, ⟨basis, coinitial⟩, nonempty, enumerated.codomain_mono inside, ?_, ?_⟩
  · intro v tau entry
    have bounded := ZFSet.pair_mem_prod.1 (function.1 entry)
    rw [M.visibilitySupportIncidence_eq_niceSupportRelation a s b T K]
    exact supported v bounded.1 tau bounded.2 entry
  · apply (M.preparationForcingCode_iff a s b K pairing unions powers separation collection
      carrier order T (M.groundRelations T s.carrier) graphGround
      (M.groundRelations_mem pairing unions powers separation hT carrier) valid z F f range p).2
    refine ⟨profile, ?_⟩
    intro v tau _ entry
    have bounded := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact equalities v bounded.1 tau bounded.2 entry





def TypedPreparedCertificate (nodeOrder meet omega : ZFSet.{u})
    (z : Name s) (p : P) (F B f e names : ZFSet.{u}) : Prop :=
  MeetFilterCode b.carrier nodeOrder meet F ∧
  CoinitialBelowCode nodeOrder F F B ∧ B.Nonempty ∧
  SynchronizedEnumerationCode omega (M.niceSupportNameCodes a s T K) B f e names ∧
  f ⊆ M.niceSupportRelation a s b T K ∧
  M.DecidesVisibilityProfile a s b K T F z p ∧
  ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
    ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z tau

theorem preparedCertificateCode_typed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet omega : ZFSet.{u}) (z : (M.nameDomain s).names) (p : P)
    (F B f e names : ZFSet.{u})
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier nodeOrder meet (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T K) (s.encode ⊤) omega z.val.val F B f e names) :
    M.TypedPreparedCertificate a s b T K nodeOrder meet omega z.val p F B f e names := by
  obtain ⟨filter, basis, nonempty, sync, incidence, raw⟩ := code
  have supported : f ⊆ M.niceSupportRelation a s b T K := by
    intro entry member
    obtain ⟨v, _, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    rw [← M.visibilitySupportIncidence_eq_niceSupportRelation a s b T K]
    exact incidence v tau member
  have niceRange : f ⊆ ZFSet.prod B (M.niceSupportNameCodes a s T K) := by
    intro entry member
    obtain ⟨v, hv, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    have nice := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 (supported member)).1
    exact ZFSet.pair_mem_prod.2 ⟨hv, nice.2⟩
  have namesRange : names ⊆ ZFSet.prod omega (M.niceSupportNameCodes a s T K) := by
    intro entry member
    obtain ⟨n, hn, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.2.2.1.1 member)
    obtain ⟨v, nv, _⟩ := sync.2.1.2 n hn
    have vt := sync.2.2.2.2.1 n hn v tau nv member
    exact ZFSet.pair_mem_prod.2 ⟨hn, (ZFSet.pair_mem_prod.1 (niceRange vt)).2⟩
  have narrowed : SynchronizedEnumerationCode omega
      (M.niceSupportNameCodes a s T K) B f e names :=
    ⟨⟨niceRange, sync.1.2⟩, sync.2.1, ⟨namesRange, sync.2.2.1.2⟩,
      sync.2.2.2.1, sync.2.2.2.2.1, sync.2.2.2.2.2⟩
  have range : f ⊆ ZFSet.prod b.carrier (M.groundRelations T s.carrier) := by
    intro entry member
    obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨filter.subset (basis.1 hv), htau⟩
  have valid : ∀ tau ∈ M.groundRelations T s.carrier, IsName s tau := by
    intro tau member
    exact Name.isName_of_subset validT ((M.mem_groundRelations T s.carrier tau).1 member).2
  have forcing := (M.preparationForcingCode_iff a s b K pairing unions powers separation
    collection carrier order T (M.groundRelations T s.carrier) graphGround
    (M.groundRelations_mem pairing unions powers separation hT carrier) valid z F f range p).1 raw
  refine ⟨filter, basis, nonempty, narrowed, supported, forcing.1, ?_⟩
  intro v _ tau _ entry
  exact forcing.2 v tau (ZFSet.pair_mem_prod.1 (sync.1.1 entry)).2 entry

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace PreparedCertificateFamilyCode

theorem bounds_mono {M : TransitiveGround.{u}}
    {P order q nodes nodeOrder meet N visibility top omega J C E C' E' k enumerations : ZFSet.{u}}
    (code : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J C E k enumerations)
    (certificates : C ⊆ C') (enumerationBound : E ⊆ E') :
    PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J C' E' k enumerations := by
  have widen {A B B' f : ZFSet.{u}} (function : ZFSet.IsFunc A B f) (inside : B ⊆ B') :
      ZFSet.IsFunc A B' f := by
    refine ⟨?_, function.2⟩
    intro entry member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hx, inside hy⟩
  exact ⟨widen code.1 certificates, widen code.2.1 enumerationBound, code.2.2⟩

end PreparedCertificateFamilyCode
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem preparedCertificateFamilyCode_of_selected
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet J : ZFSet.{u}) (hJ : J ∈ M.sets) (validJ : ∀ tau ∈ J, IsName s tau)
    (H : ConditionFilter P) (p : P) (k enumerations : ZFSet.{u})
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
      (M.niceSupportNameCodes a s T K)) k)
    (selected : k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (enumerated : ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
      (M.niceSupportNameCodes a s T K)) enumerations)
    (synchronized : ∀ j F B f e names,
      ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
      SynchronizedEnumerationCode ZFSet.omega (M.niceSupportNameCodes a s T K) B f e names)
    (certificates : ∀ (z : (M.nameDomain s).names) F B f,
      ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      MeetFilterCode b.carrier nodeOrder meet F ∧ B.Nonempty ∧
      M.DecidesVisibilityProfile a s b K T F z.val p ∧
      (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
        ZFSet.pair v tau.val ∈ f → Name.ForcesEq p z.val tau)) :
    PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p) b.carrier nodeOrder meet
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤) ZFSet.omega J
      (M.supportedEqualityCertificateBound b.carrier (M.niceSupportNameCodes a s T K))
      (M.synchronizedEnumerationBound b.carrier (M.niceSupportNameCodes a s T K)) k enumerations := by
  refine ⟨function, enumerated, ?_⟩
  intro j F B f e names stored enumEntry
  have hj := (ZFSet.pair_mem_prod.1 (function.1 stored)).1
  let z : (M.nameDomain s).names := ⟨⟨j, validJ j hj⟩, M.transitive hJ hj⟩
  obtain ⟨filter, nonempty, profile, equalities⟩ := certificates z F B f stored
  exact M.preparedCertificateCode_of_selected a s b T K pairing unions powers separation collection
    carrier order hT validT graphGround nodeOrder meet J validJ H z F B f e names p
    (selected stored) filter nonempty profile equalities (synchronized j F B f e names stored enumEntry)

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

private theorem anchor_of_dataBound {L : Type u} [PartialOrder L]
    (b : Presentation L) (I level T S mu X tuples A : ZFSet.{u})
    (C E D : L) (U Rf Rc u w : ZFSet.{u})
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc) u w) (b.encode D) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) : E ≤ D := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, _hfu, fw, _hfw, edge, lower, _rest⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples _ u w (b.encode D)).1 bound
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier ![level, b.encode C, b.encode E, U, Rf, Rc]
      2 rawE).1 edge).2.2
  subst rawE
  exact (b.pair_mem_conditionOrder E D).1 lower

variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignment_aligned_reference
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA newA oldA : ZFSet.{u})
    (g h : G) (D X V C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (source : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ sourceA)
    (i newU newW oldU oldW : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val))
      (stageOneAssignment i newU newW) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history)
    (newBound : ZFSet.pair (stageOneAssignment i newU newW) (b.encode (d.iso h D)) ∈
      stageOneDataBounds newA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (oldBound : ZFSet.pair (stageOneAssignment i oldU oldW) (b.encode X) ∈
      stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (overlap : ∀ x : L, x ≤ d.iso h D → x ≤ X → x ≤ d.iso h V)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (contains : M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA ⊆ oldA) :
    d.iso h E ≤ d.iso h V ∧ E ≤ V ∧
    i = refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val ∧
    i = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val ∧
    ZFSet.pair (ZFSet.pair (t.encode g) (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val))
      (stageOneAssignment i (a.act s g u).val (a.act s g w).val) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history ∧
    stageOneAssignment i (a.act s g u).val (a.act s g w).val ∈ oldA := by
  let z := stageOneAssignment
    (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have branchMember : z ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hu, hw⟩
  have graphEq := M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers
    separation collection carrier group nodes order system.inputs.condition_maps system.inputs.node_maps
    supports level T T2 hLevel hT system.valid1 system.valid2 system.inputs.terms_closed
    system.inputs.pairs_closed system.inputs.family_ground system.indices.index_ground
  have branch := ((M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) (stageOneAssignment i newU newW)).1 edge).2
  rw [graphEq h] at branch
  have moved := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u w index hu hw _).1 branch
  obtain ⟨indexH, termU, termW⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 moved
  have hBelow := anchor_of_dataBound b I level T S mu positions tuples newA
    (d.iso h C) (d.iso h E) (d.iso h D)
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val
    newU newW (indexH ▸ newBound)
  have xBelow := anchor_of_dataBound b I level T S mu positions tuples oldA
    (d.iso h C) (d.iso h E) X
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val
    oldU oldW (indexH ▸ oldBound)
  have overlapAnchor := overlap (d.iso h E) hBelow xBelow
  have anchor : E ≤ V := (d.iso h).le_iff_le.mp overlapAnchor
  obtain ⟨strict, domain, fine, coarse, _validity⟩ :=
    (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T T2 system.valid1 system.inputs.family_ground C E U Rf Rc).1 index
  have nodeAgree (x : L) (below : x ≤ V) : d.iso h x = d.iso g x := by
    have fixed := relative x below
    calc
      d.iso h x = d.iso g (d.iso (g⁻¹ * h) x) := by rw [← d.mul]; simp only [mul_inv_cancel_left]
      _ = d.iso g x := congrArg (d.iso g) fixed
  have atC : g⁻¹ * h ∈ d.principalFix C := d.principalFix_antitone (strict.le.trans anchor) relative
  have nameAgree {K : ZFSet.{u}} (tau : Name s)
      (candidate : tau.val ∈ M.niceNameCandidates a s K (d.principalFix C)) :
      a.act s h tau = a.act s g tau := by
    obtain ⟨_ground, sigma, equal, _subset, support⟩ :=
      (M.mem_niceNameCandidates a s K (d.principalFix C) tau.val).1 candidate
    have same : sigma = tau := Subtype.ext equal
    subst sigma
    have fixed : a.act s (g⁻¹ * h) tau = tau := support atC
    calc
      a.act s h tau = a.act s g (a.act s (g⁻¹ * h) tau) := by
        rw [← a.act_mul]; simp only [mul_inv_cancel_left]
      _ = a.act s g tau := congrArg (a.act s g) fixed
  have indexG : i = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
    rw [indexH, nodeAgree C (strict.le.trans anchor), nodeAgree E anchor,
      nameAgree U.val domain, nameAgree Rf.val fine, nameAgree Rc.val coarse]
  have referenceBranch := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    g C E U Rf Rc u w index hu hw (stageOneAssignment i (a.act s g u).val (a.act s g w).val)).2
      (congrArg (fun idx => stageOneAssignment idx (a.act s g u).val (a.act s g w).val) indexG)
  rw [← graphEq g] at referenceBranch
  have referenceEdge := (M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode g) (stageOneAssignment i (a.act s g u).val (a.act s g w).val)).2
      ⟨t.encode_mem g, referenceBranch⟩
  exact ⟨overlapAnchor, anchor, indexH, indexG, referenceEdge, contains
    ((M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA _).2
      ⟨z, source, referenceEdge⟩)⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

include descent in
theorem structuralAssignment_prepared_aligned_collision
    (small : M.sets.Countable)
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA newA oldA : ZFSet.{u})
    (positionSupport : ∀ (D : L), ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g h : G) (D X V C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val.val ∈ T) (hw : w.val.val ∈ T)
    (hOldU : oldU.val.val ∈ T) (hOldW : oldW.val.val ∈ T)
    (p q : P) (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (overlap : meet (d.iso h D) X = d.iso h V)
    (meetLeft : meet (d.iso h D) X ≤ d.iso h D)
    (meetRight : meet (d.iso h D) X ≤ X)
    (meetGreatest : ∀ z : L, z ≤ d.iso h D → z ≤ X → z ≤ meet (d.iso h D) X)
    (F B f e names : Fin 2 → ZFSet.{u}) :
    let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier system.inputs.condition_maps
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let movedIdx := refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val
    stageOneAssignment idx u.val.val w.val.val ∈ sourceA →
    ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment idx u.val.val w.val.val))
      (stageOneAssignment movedIdx (moved h u).val.val (moved h w).val.val) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history →
    ZFSet.pair (stageOneAssignment movedIdx (moved h u).val.val (moved h w).val.val)
      (b.encode (d.iso h D)) ∈ stageOneDataBounds newA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    ZFSet.pair (stageOneAssignment movedIdx oldU.val.val oldW.val.val) (b.encode X) ∈
      stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA ⊆ oldA →
    stageOneRawTests M fields sourceA (s.encode p) → stageOneRawTests M fields oldA (s.encode q) →
    (∀ i : Fin 2, PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i).val.val
      (F i) (B i) (f i) (e i) (names i)) →
    stageOneRawCollision M fields movedIdx (moved h u).val.val oldU.val.val
      (moved h w).val.val oldW.val.val (s.encode q) ∧
    stageOneRawCollision M fields movedIdx oldU.val.val (moved h u).val.val
      oldW.val.val (moved h w).val.val (s.encode q) := by
  let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier system.inputs.condition_maps
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let movedIdx := refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
    (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val
  dsimp only
  intro source edge newBound oldBound contains sourceTests oldTests certificates
  have aligned := M.structuralAssignment_aligned_reference a s t b d base directed level T T2 system
    pairing unions powers separation collection carrier order group nodes supports hLevel hT function stored
    I S mu positions tuples sourceA newA oldA g h D X V C E U Rf Rc u.val w.val index hu hw source
    movedIdx (moved h u).val.val (moved h w).val.val oldU.val.val oldW.val.val edge newBound oldBound
    (fun z hz hx => overlap ▸ meetGreatest z hz hx) relative contains
  have anchor : d.iso h E ≤ meet (d.iso h D) X := overlap.symm ▸ aligned.1
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order system.inputs.condition_maps level T T2 system.valid1 system.inputs.terms_closed
    system.inputs.pairs_closed system.inputs.family_ground h C E U Rf Rc).2 index
  have oldMember : stageOneAssignment movedIdx oldU.val.val oldW.val.val ∈ oldA :=
    (stageOneDataBounds_assignment_entry oldA I T S b.carrier mu positions b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples movedIdx oldU.val.val oldW.val.val (b.encode X)).1 oldBound |>.1
  have referenceRaw := oldTests.2 movedIdx movedMember
    (moved g u).val.val (system.inputs.terms_closed g u.val hu) oldU.val.val hOldU
    (moved g w).val.val (system.inputs.terms_closed g w.val hw) oldW.val.val hOldW
    aligned.2.2.2.2.2 oldMember
  have reference := (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT system.valid1 system.indices (d.iso h C) (d.iso h E)
    (moved h U) (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW movedMember q).1 referenceRaw
  have single := (M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT system.valid1 system.indices base directed system.first C E U Rf Rc u w index p).1
    (sourceTests.1 idx index u.val.val hu w.val.val hw source)
  have positionsOfBound (A : ZFSet.{u}) (Z : L) (v v' : Name s)
      (bound : ZFSet.pair (stageOneAssignment movedIdx v.val v'.val) (b.encode Z) ∈
        stageOneDataBounds A I T S b.carrier mu positions b.conditionOrder
          (refinementIndexFieldGraph I b.carrier 2) tuples) :
      d.principalFix Z ≤ a.stabilizer s v ∧ d.principalFix Z ≤ a.stabilizer s v' := by
    obtain ⟨_, _, _, _, _, rawE, _, fu, hfu, fw, hfw, _anchor, _below, tu, tw, bu, bw⟩ :=
      (stageOneDataBounds_assignment_entry A I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples movedIdx v.val v'.val (b.encode Z)).1 bound
    exact ⟨positionSupport Z fu hfu v tu bu, positionSupport Z fw hfw v' tw bw⟩
  have newPositions := positionsOfBound newA (d.iso h D) (moved h u).val (moved h w).val newBound
  have oldPositions := positionsOfBound oldA X oldU.val oldW.val oldBound
  have recognized (i : Fin 2) := M.preparedCertificateCode_typed a s b T d.principalFix pairing unions powers
    separation collection carrier order hT system.valid1 system.first.visibility_graph_ground
    b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder) ZFSet.omega
    ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i) p
    (F i) (B i) (f i) (e i) (names i) (certificates i)
  have collision := M.prepared_joint_refinementCollision_of_position_supports a s t b d
    pairing unions powers separation collection carrier order group nodes supports system.inputs.condition_maps
    hT system.valid1 system.inputs.terms_closed base directed system.first meet descent
    system.valid2 system.inputs.pairs_closed level system.indices small system.terms_hs
    C E U Rf Rc u w oldU oldW index F B f p q g h V (d.iso h D) X relative qh qg overlap anchor
    meetLeft meetRight
    (fun i => (recognized i).1.subset) (fun i => (recognized i).2.1.1)
    (fun i => (recognized i).2.1.2) (fun i => (recognized i).2.2.2.1.1)
    (fun i => (recognized i).2.2.2.2.1) (fun i => (recognized i).2.2.2.2.2.1)
    (fun i => (recognized i).2.2.2.2.2.2)
    (Fin.cases newPositions.1 (Fin.cases newPositions.2 (fun j => Fin.elim0 j)))
    (Fin.cases oldPositions.1 (Fin.cases oldPositions.2 (fun j => Fin.elim0 j))) single reference
  exact M.refinementLevelRawCollision_both_orders s pairing unions powers separation collection carrier order
    hT system.valid1 a b d level T2 system.indices (d.iso h C) (d.iso h E)
    (moved h U) (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW movedMember q collision.1

end PartitionPilot.Forcing.TransitiveGround

end OAI
