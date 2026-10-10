import OAI.SetTheory.PartitionPrinciple.Definability.GroundAllSupportCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNameSequenceValues
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPreparationForcing

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)

def ordinaryExtension (H : ConditionFilter P) : TransitiveGround.{u} :=
  ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩

theorem mem_ordinaryExtension (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ (M.ordinaryExtension s H).sets ↔
      ∃ τ ∈ (M.nameDomain s).names, Name.eval {q | H.mem q} τ = x :=
  (M.nameDomain s).mem_values {q | H.mem q} x

theorem ground_subset_ordinaryExtension [OrderTop P]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    M.sets ⊆ (M.ordinaryExtension s H).sets := by
  intro x hx
  exact (M.mem_ordinaryExtension s H x).2 ⟨Name.check s ⊤ x,
    M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx,
    Name.eval_check {q | H.mem q} ⊤ H.top_mem x⟩

end TransitiveGround

section
open SetFormula
universe u

def GroundSequenceReflection (M N : TransitiveGround.{u}) (P : ZFSet.{u}) : Prop :=
  ∀ f ∈ N.sets, ZFSet.IsFunc ZFSet.omega P f → f ∈ M.sets

namespace GroundSequenceReflection
variable {M N : TransitiveGround.{u}} {P : ZFSet.{u}}
variable (reflection : GroundSequenceReflection M N P)
include reflection

theorem enumeration
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ N.sets) (subset : X ⊆ P) (nonempty : X.Nonempty)
    (small : N.groundEmbeddable X ZFSet.omega) :
    ∃ f ∈ M.sets, f ∈ N.sets ∧ ZFSet.IsFunc ZFSet.omega X f ∧
      ZFSet.IsFunc ZFSet.omega P f ∧ relationImage ZFSet.omega P f = X := by
  obtain ⟨f, hf, function, onto⟩ :=
    N.groundCountable_enumeration pairingN unionsN powersN separationN infiniteN hX nonempty small
  have enlarged : ZFSet.IsFunc ZFSet.omega P f := by
    refine ⟨?_, function.2⟩
    intro z hz
    obtain ⟨n, hn, x, hx, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, subset hx⟩
  refine ⟨f, reflection f hf enlarged, hf, function, enlarged, ?_⟩
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨_, n, _, entry⟩ := (mem_relationImage _ _ _ x).1 hx
    exact (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  · intro hx
    obtain ⟨n, hn, entry⟩ := onto x hx
    exact (mem_relationImage _ _ _ x).2 ⟨subset hx, n, hn, entry⟩

theorem countable_subset
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (hP : P ∈ M.sets) {X : ZFSet.{u}} (hX : X ∈ N.sets) (subset : X ⊆ P)
    (small : N.groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega := by
  classical
  by_cases nonempty : X.Nonempty
  · obtain ⟨f, hf, _, _, function, range_eq⟩ :=
      reflection.enumeration pairingN unionsN powersN separationN infiniteN hX subset nonempty small
    have hOmega := M.omega_mem separation infinite
    have omegaSmall : M.groundEmbeddable ZFSet.omega ZFSet.omega :=
      ⟨identityFunctionGraph ZFSet.omega,
        M.identityFunctionGraph_mem pairing unions powers separation hOmega,
        identityFunctionGraph_injection ZFSet.omega⟩
    have rangeGround := M.relationImage_mem separation hOmega hP hf
    have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
      hOmega hP hOmega hf function omegaSmall
    rw [range_eq] at rangeGround rangeSmall
    exact ⟨rangeGround, rangeSmall⟩
  · have empty : X = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (nonempty ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact ⟨M.empty_mem ⟨P, hP⟩, M.empty_groundEmbeddable ZFSet.omega ⟨P, hP⟩⟩

end GroundSequenceReflection

end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem ordinary_ZF_of_conditionMaps {G : Type u} [Group G]
    (a : PosetAction G P) (t : Presentation G)
    (infinite : Realize M.sets infinity Fin.elim0)
    (group : t.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    ZFRealization (M.ordinaryExtension s H).sets := by
  have allGeneric : H.GenericFor
      (formulaFamily (a.symmetricDomain s (M.nameDomain s) (allSupportFamily G))) := by
    rw [a.symmetricDomain_allSupport]
    exact generic
  have checked := M.symmetric_ZF a s t (natInitialPresentation 1) (allSupportFamily G)
    (allSupportBasis G) (allSupportFamily_basis G) pairing unions powers separation collection infinite
    carrier order group (M.allSupportIndices_mem t pairing group)
    (M.allSupportBasisCode_mem t pairing group) maps H allGeneric
  rw [a.symmetricDomain_allSupport] at checked
  exact checked

include pairing unions powers separation collection carrier order in
theorem ordinary_collection_of_conditionMaps {G : Type u} [Group G]
    (a : PosetAction G P) (t : Presentation G)
    (group : t.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    CollectionSchema (M.ordinaryExtension s H).sets := by
  have allGeneric : H.GenericFor
      (formulaFamily (a.symmetricDomain s (M.nameDomain s) (allSupportFamily G))) := by
    rw [a.symmetricDomain_allSupport]
    exact generic
  have checked : CollectionSchema
      ((a.symmetricDomain s (M.nameDomain s) (allSupportFamily G)).values {p | H.mem p}) := by
    intro n
    exact M.symmetric_collection a s t (natInitialPresentation 1) (allSupportFamily G)
      (allSupportBasis G) (allSupportFamily_basis G) pairing unions powers separation collection
      carrier order group (M.allSupportIndices_mem t pairing group)
      (M.allSupportBasisCode_mem t pairing group) maps H allGeneric
  rw [a.symmetricDomain_allSupport] at checked
  exact @checked

include pairing unions powers separation collection carrier order in
theorem ordinaryExtension_ZF (infinite : Realize M.sets infinity Fin.elim0)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    ZFRealization (M.ordinaryExtension s H).sets :=
  M.ordinary_ZF_of_conditionMaps s pairing unions powers separation collection carrier order
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P) trivialGroupPresentation infinite
    (M.trivialGroupPresentation_mem pairing ⟨s.carrier, carrier⟩)
    (M.identityPosetAction_conditionMapFamily_mem s pairing unions powers separation carrier) H generic

include pairing unions powers separation collection carrier order in
theorem ordinaryExtension_collection
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    CollectionSchema (M.ordinaryExtension s H).sets :=
  M.ordinary_collection_of_conditionMaps s pairing unions powers separation collection carrier order
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P) trivialGroupPresentation
    (M.trivialGroupPresentation_mem pairing ⟨s.carrier, carrier⟩)
    (M.identityPosetAction_conditionMapFamily_mem s pairing unions powers separation carrier) H generic

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

include pairing unions powers separation collection carrier group nodes supports maps hT valid in
theorem visibleSupportProfile_mem_ordinary
    (order : s.conditionOrder ∈ M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (z : (M.nameDomain s).names) :
    M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∈
      (M.ordinaryExtension s H).sets := by
  let N := M.ordinaryExtension s H
  let graph := Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T d.principalFix)
  have hz : Name.eval {p | H.mem p} z.val ∈ N.sets := ⟨z, rfl⟩
  have hgraph : graph ∈ N.sets := ⟨⟨_, M.niceVisibilityEvaluationName_mem a s b t d.principalFix
    pairing unions powers separation collection carrier group nodes supports maps hT valid⟩, rfl⟩
  have hnodes : b.carrier ∈ N.sets := M.ground_subset_ordinaryExtension s pairing unions powers
    separation collection carrier H nodes
  have hvisibility (v : L) :
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) ∈ N.sets :=
    ⟨⟨_, M.niceVisibilityName_mem a s t b d.principalFix pairing unions powers separation collection
      carrier group supports maps hT valid v (M.transitive nodes (b.encode_mem v))⟩, rfl⟩
  let phi : SetFormula 3 := ex (.conj (BoundedFormula.pairMembershipFormula 1 0 3).toFormula (.mem 2 0))
  let params : Fin 2 → ZFSet.{u} := ![Name.eval {p | H.mem p} z.val, graph]
  have members : ∀ i, params i ∈ N.sets :=
    Fin.cases hz (Fin.cases hgraph (fun i => Fin.elim0 i))
  have meaning (v : L) : Realize N.sets phi (extend (b.encode v) params) ↔
      Name.eval {p | H.mem p} z.val ∈
        Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
    rw [show phi = ex (.conj (BoundedFormula.pairMembershipFormula 1 0 3).toFormula (.mem 2 0)) from rfl,
      realize_ex]
    constructor
    · rintro ⟨V, hV, entry, member⟩
      have coded : ZFSet.pair (b.encode v) V ∈ graph :=
        (N.realize_stageOnePairLookup 1 0 3 _
          (Fin.cases hV (Fin.cases (N.transitive hnodes (b.encode_mem v)) members))).1 entry
      have equal := (M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v V).1 coded
      exact equal.symm ▸ member
    · intro member
      refine ⟨_, hvisibility v, ?_, member⟩
      exact (N.realize_stageOnePairLookup 1 0 3 _
        (Fin.cases (hvisibility v) (Fin.cases (N.transitive hnodes (b.encode_mem v)) members))).2
        ((M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v _).2 rfl)
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  have selected := N.separation_mem zf.2.1 phi params members hnodes
  have equal : ZFSet.sep (fun x => Realize N.sets phi (extend x params)) b.carrier =
      M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (ZFSet.mem_sep.1 hx).1
      exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).2
        ((meaning v).1 (ZFSet.mem_sep.1 hx).2)
    · intro hx
      obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ hx)
      exact ZFSet.mem_sep.2 ⟨b.encode_mem v,
        (meaning v).2 ((M.encode_mem_visibleSupportProfile a s b d T H _ v).1 hx)⟩
  exact equal ▸ selected

include pairing unions powers separation collection carrier group nodes supports maps hT valid in
theorem exists_forced_visibleSupportProfile (small : M.sets.Countable)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (z : (M.nameDomain s).names)
    (ground : M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∈ M.sets)
    (p : P) (hp : H.mem p) :
    ∃ q, H.mem q ∧ q ≤ p ∧
      Forces (M.nameDomain s) visibilityProfileFormula
        (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
          carrier group nodes supports maps hT valid
          (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) ground z) q ∧
      M.DecidesVisibilityProfile a s b d.principalFix T
        (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) z.val q := by
  let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
  let env := M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
    carrier group nodes supports maps hT valid F ground z
  have truth : Realize ((M.nameDomain s).values {p | H.mem p}) visibilityProfileFormula
      (evalAssignment {p | H.mem p} env) :=
    (M.realize_visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
      carrier group nodes supports maps hT valid F ground z H).2
      (fun v => (M.encode_mem_visibleSupportProfile a s b d T H _ v).symm)
  obtain ⟨r, hr, forced⟩ := (forcing_truth (M.nameDomain s) H generic visibilityProfileFormula env).1 truth
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  have forcedQ := forces_mono (M.nameDomain s) visibilityProfileFormula env forced qr
  exact ⟨q, hq, qp, forcedQ,
    (M.forces_visibilityProfile_iff a s t b d.principalFix pairing unions powers separation collection
      carrier group nodes supports maps hT valid small F ground z q).1 forcedQ⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)

theorem ordinaryExtension_sequenceReflection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) {U : ZFSet.{u}} (hU : U ∈ M.sets)
    (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s))) :
    GroundSequenceReflection M (M.ordinaryExtension s H) U := by
  intro f hf function
  obtain ⟨τ, hτ, rfl⟩ := (M.mem_ordinaryExtension s H f).1 hf
  exact (M.sequence_value_ground_of_function s pairing unions powers separation collection infinite choice
    carrier order small hU closed ⟨τ, hτ⟩ H genericCoded genericFormula function).1

theorem ordinaryExtension_submodel_sequenceReflection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) {U : ZFSet.{u}} (hU : U ∈ M.sets)
    (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (N : TransitiveGround.{u}) (included : N.sets ⊆ (M.ordinaryExtension s H).sets) :
    GroundSequenceReflection M N U := by
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice carrier order small hU closed H genericCoded genericFormula
  intro f hf function
  exact reflection f (included hf) function

end TransitiveGround

end PartitionPilot.Forcing

end OAI
