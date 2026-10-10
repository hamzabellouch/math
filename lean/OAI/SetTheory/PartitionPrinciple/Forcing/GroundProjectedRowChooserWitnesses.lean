import OAI.SetTheory.PartitionPrinciple.Definability.GroundInternalRowSetZF
import OAI.SetTheory.PartitionPrinciple.Definability.GroundOutsideRowCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundOrdinarySubmodelReflection
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundProjectedRowUniqueFibers
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinalEnumerationFamilies

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

def symmetricExtension (H : ConditionFilter P) : TransitiveGround.{u} :=
  ⟨(a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q},
    (a.symmetricDomain s (M.nameDomain s) F).values_transitive {q | H.mem q}⟩

theorem mem_symmetricExtension (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ (M.symmetricExtension s a F H).sets ↔
      ∃ τ ∈ (M.nameDomain s).names, HereditarilySymmetric a s F τ ∧
        Name.eval {q | H.mem q} τ = x :=
  a.mem_symmetric_values s (M.nameDomain s) F {q | H.mem q} x

theorem symmetricExtension_subset_ordinaryExtension (H : ConditionFilter P) :
    (M.symmetricExtension s a F H).sets ⊆ (M.ordinaryExtension s H).sets := by
  intro x hx
  obtain ⟨τ, ground, _, equal⟩ := (M.mem_symmetricExtension s a F H x).1 hx
  exact (M.mem_ordinaryExtension s H x).2 ⟨τ, ground, equal⟩

theorem ground_subset_symmetricExtension [OrderTop P]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    M.sets ⊆ (M.symmetricExtension s a F H).sets := by
  intro x hx
  exact (M.mem_symmetricExtension s a F H x).2 ⟨Name.check s ⊤ x,
    M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx,
    HereditarilySymmetric.check a s F x, Name.eval_check {q | H.mem q} ⊤ H.top_mem x⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def supportedFamilyCodes (K : Subgroup G) (W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ tau : Name s, tau.val = z ∧ K ≤ a.stabilizer s tau) W

theorem mem_supportedFamilyCodes (K : Subgroup G) (W : ZFSet.{u}) (tau : Name s) :
    tau.val ∈ supportedFamilyCodes a s K W ↔ tau.val ∈ W ∧ K ≤ a.stabilizer s tau := by
  rw [supportedFamilyCodes, ZFSet.mem_sep]
  constructor
  · rintro ⟨member, sigma, equal, fixed⟩
    have same : sigma = tau := Subtype.ext equal
    exact ⟨member, same ▸ fixed⟩
  · rintro ⟨member, fixed⟩
    exact ⟨member, tau, rfl, fixed⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem supportedFamilyCodes_mem (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (hi : b.encode i ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z) :
    Name.supportedFamilyCodes a s (K i) W ∈ M.sets := by
  let params := extend (b.encode i) (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hi (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (fun j => Fin.elim0 j)))))
  have selected := M.separation_mem separation nameSupportFormula params members hW
  have equal : ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z params)) W =
      Name.supportedFamilyCodes a s (K i) W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, Name.supportedFamilyCodes, ZFSet.mem_sep]
    apply and_congr_right
    intro member
    let tau : Name s := ⟨z, valid z member⟩
    have meaning : Realize M.sets nameSupportFormula (extend z params) ↔
        K i ≤ a.stabilizer s tau :=
      M.realize_nameSupportFormula a s t b K pairing unions powers separation collection
        carrier group supports maps i hi tau (M.transitive hW member)
    rw [meaning]
    constructor
    · intro fixed
      exact ⟨tau, rfl, fixed⟩
    · rintro ⟨sigma, sigmaCode, fixed⟩
      have same : sigma = tau := Subtype.ext sigmaCode
      exact same ▸ fixed
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable {G : Type v} [Group G]

theorem supportedNameSequence_function_mem
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)
    {I f : ZFSet.{u}} (hI : I ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i))
    (K : Subgroup G) (support : F.mem K)
    (fixed : ∀ g ∈ K, ∀ i, a.act s g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩)
    (children : ∀ i, HereditarilySymmetric a s F ⟨function.value i, names i⟩)
    (H : ConditionFilter P) :
    let sequence := Name.indexedGraphName ⊤ function names
    sequence.val ∈ M.sets ∧ K ≤ a.stabilizer s sequence ∧
      HereditarilySymmetric a s F sequence ∧
      ZFSet.IsFunc I (ZFSet.range (fun i : I => Name.eval {p | H.mem p} ⟨function.value i, names i⟩))
        (Name.eval {p | H.mem p} sequence) ∧
      Name.eval {p | H.mem p} sequence ∈ (M.symmetricExtension s a F H).sets := by
  let sequence := Name.indexedGraphName ⊤ function names
  have ground := M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) hI hf function names
  have supported : K ≤ a.stabilizer s sequence :=
    Name.indexedTuple_supported a I (fun i => ⟨function.value i, names i⟩) K fixed
  have symmetric : HereditarilySymmetric a s F sequence :=
    Name.indexedTuple_hs a F I (fun i => ⟨function.value i, names i⟩) K support fixed children
  exact ⟨ground, supported, symmetric,
    Name.eval_indexedGraphName_function {p | H.mem p} ⊤ H.top_mem function names,
    (M.mem_symmetricExtension s a F H _).2 ⟨sequence, ground, symmetric, rfl⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]

theorem exists_groundOrdinalFixedNameSequence
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets)
    {W f : ZFSet.{u}} (hW : W ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn W f) (names : ∀ i, IsName s (function.value i))
    (fixed : ∀ g i, a.act s g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩)
    (children : ∀ i, HereditarilySymmetric a s F ⟨function.value i, names i⟩) :
    ∃ I ∈ M.sets, ordinalSetProperty I ∧
      ∃ q ∈ M.sets, ∃ qFunction : FunctionGraphOn I q,
      ∃ qNames : ∀ j, IsName s (qFunction.value j),
        (∀ g j, a.act s g ⟨qFunction.value j, qNames j⟩ = ⟨qFunction.value j, qNames j⟩) ∧
        (∀ j, HereditarilySymmetric a s F ⟨qFunction.value j, qNames j⟩) ∧
        (∀ i : W.toSet, ∃ j : I.toSet,
          (⟨qFunction.value j, qNames j⟩ : Name s) = ⟨function.value i, names i⟩) ∧
        (∀ j : I.toSet, ∃ i : W.toSet,
          (⟨qFunction.value j, qNames j⟩ : Name s) = ⟨function.value i, names i⟩) ∧
        ∀ H : ConditionFilter P,
          let sequence := Name.indexedGraphName ⊤ qFunction qNames
          sequence.val ∈ M.sets ∧ HereditarilySymmetric a s F sequence ∧
          ZFSet.IsFunc I (ZFSet.range (fun j : I => Name.eval {p | H.mem p}
            ⟨qFunction.value j, qNames j⟩)) (Name.eval {p | H.mem p} sequence) ∧
          Name.eval {p | H.mem p} sequence ∈ (M.symmetricExtension s a F H).sets := by
  obtain ⟨I, hI, enumeration, hEnumeration, ordinal, injection, onto⟩ :=
    M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice hW
  let V := functionGraphRange W f
  have hV : V ∈ M.sets := M.functionGraphRange_mem unions separation hW hf
  let q := relationCompose I W V enumeration f
  have hq : q ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hW hV hEnumeration hf
  have qFunction : FunctionGraphOn I q := ⟨V, relationCompose_function_of_subset
    injection.1 (functionGraphRange_function function) (fun _ h => h)⟩
  have each (j : I.toSet) : ∃ i : W.toSet, qFunction.value j = function.value i := by
    obtain ⟨_, _, x, hx, _, edge⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 (qFunction.value_entry j)
    exact ⟨⟨x, hx⟩, (function.value_eq_of_entry ⟨x, hx⟩ edge).symm⟩
  let source (j : I.toSet) := Classical.choose (each j)
  have value (j : I.toSet) := Classical.choose_spec (each j)
  have qNames (j : I.toSet) : IsName s (qFunction.value j) := (value j).symm ▸ names (source j)
  have actual (j : I.toSet) : (⟨qFunction.value j, qNames j⟩ : Name s) =
      ⟨function.value (source j), names (source j)⟩ := Subtype.ext (value j)
  have qFixed (g : G) (j : I.toSet) : a.act s g ⟨qFunction.value j, qNames j⟩ = ⟨qFunction.value j, qNames j⟩ := by
    rw [actual j]
    exact fixed g (source j)
  have qChildren (j : I.toSet) : HereditarilySymmetric a s F ⟨qFunction.value j, qNames j⟩ := by
    rw [actual j]
    exact children (source j)
  refine ⟨I, hI, ordinal, q, hq, qFunction, qNames, qFixed, qChildren, ?_,
    (fun j => ⟨source j, actual j⟩), ?_⟩
  · intro i
    obtain ⟨j, hj, enumerated⟩ := onto i.val i.property
    have edge : ZFSet.pair j (function.value i) ∈ q := (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨hj, (mem_functionGraphRange W f _).2 ⟨i.val, i.property, function.value_entry i⟩,
        i.val, i.property, enumerated, function.value_entry i⟩
    exact ⟨⟨j, hj⟩, Subtype.ext (qFunction.value_eq_of_entry ⟨j, hj⟩ edge)⟩
  · intro H sequence
    have package := M.supportedNameSequence_function_mem s a F pairing unions powers separation
      collection carrier hI hq qFunction qNames ⊤ F.top (fun g _ j => qFixed g j) qChildren H
    exact ⟨package.1, package.2.2.1, package.2.2.2.1, package.2.2.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {L G Upper : Type u}
variable [Group G] [PartialOrder L] [OrderBot L] [PartialOrder Upper]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (upper : Presentation Upper) (e : PosetAction G Upper)
variable (upperCarrier : upper.carrier ∈ M.sets)

include directed collection upperCarrier

theorem liftedInternalRowSet_mem :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let R := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (inclusion : SetMembers R → Upper), lower.graph upper inclusion ∈ M.sets →
      (∀ g p, inclusion (act.iso g p) = e.iso g (inclusion p)) →
      ∀ H : ConditionFilter Upper,
        Name.eval {p | H.mem p} (Name.rename upper inclusion (M.internalRowSetName s C hL)) ∈
          (M.symmetricExtension upper e (a.principalSupportFamily ⊥ directed) H).sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  dsimp only
  intro inclusion inclusionGround equivariant H
  apply (M.mem_symmetricExtension upper e (a.principalSupportFamily ⊥ directed) H _).2
  have lowerGround := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC)
    (M.natSetCode_mem separation infinite 2)
  refine ⟨_, M.rename_between_mem _ upper pairing unions powers separation collection
    lowerGround upperCarrier inclusion inclusionGround _
      (M.internalRowSetName_mem s C pairing unions powers separation collection infinite hL hC), ?_, rfl⟩
  exact (M.internalRowSetName_hs a s b C pairing unions powers separation infinite hL hC hG
    graph directed).rename e upper inclusion equivariant

theorem liftedInternalRows_chooser_witness
    (order : s.conditionOrder ∈ M.sets) (unbounded : ∀ B : L, ∃ i : L, ¬ i ≤ B) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let R := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (restriction : Upper →o SetMembers R) (inclusion : SetMembers R ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      lower.graph upper inclusion ∈ M.sets →
      (∀ g p, inclusion (act.iso g p) = e.iso g (inclusion p)) →
      ∀ (H : ConditionFilter Upper), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let N := M.symmetricExtension upper e (a.principalSupportFamily ⊥ directed) H
      let rows := Name.eval {p | H.mem p} (Name.rename upper inclusion (M.internalRowSetName s C hL))
      ∀ f ∈ N.sets,
        (∀ S ∈ N.sets, S ⊆ rows → S.Nonempty →
          ∃ x ∈ S, ZFSet.pair S x ∈ f ∧ ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x) →
        ∃ (B : L) (i : {i : L // i ≠ ⊥})
          (sn xn fn : (M.nameDomain upper).names),
          ¬ i.val ≤ B ∧
          sn.val = Name.rename upper inclusion (M.internalOutsideRowsName s C hL B) ∧
          xn.val = Name.rename upper inclusion (M.internalRowName s C hL i) ∧
          a.principalFix B ≤ e.stabilizer upper sn.val ∧
          a.principalFix B ≤ e.stabilizer upper fn.val ∧
          ∃ p : Upper, H.mem p ∧
            Forces (M.nameDomain upper) (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
              (extend sn (extend xn (extend fn Fin.elim0))) p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let R := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let lower := SetMembers.presentation R
  dsimp only
  intro restriction inclusion projection inclusionGround equivariant H ordinary f hf selection
  let F := a.principalSupportFamily (⊥ : L) directed
  let N := M.symmetricExtension upper e F H
  let K := projection.projectedFilter H
  have lowerGround : lower.carrier ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers
    separation infinite (M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation hL) hC) (M.natSetCode_mem separation infinite 2)
  have renameGround (tau : Name lower) (ground : tau.val ∈ M.sets) :
      (Name.rename upper inclusion tau).val ∈ M.sets :=
    M.rename_between_mem lower upper pairing unions powers separation collection lowerGround
      upperCarrier inclusion inclusionGround tau ground
  have evalLift (tau : Name lower) :
      Name.eval {p | H.mem p} (Name.rename upper inclusion tau) = Name.eval {p | K.mem p} tau :=
    Name.eval_rename upper inclusion {p | H.mem p} tau
  obtain ⟨fname, groundF, hsF, rfl⟩ := (M.mem_symmetricExtension upper e F H f).1 hf
  obtain ⟨B, fixedF⟩ := hsF.symmetric
  let Sname := Name.rename upper inclusion (M.internalOutsideRowsName s C hL B)
  have groundS : Sname.val ∈ M.sets := renameGround _
    (M.internalOutsideRowsName_mem s C pairing unions powers separation collection infinite hL hC order B)
  have hsS : HereditarilySymmetric e upper F Sname :=
    (M.internalOutsideRowsName_hs a s b C pairing unions powers separation infinite hL hC hG graph
      directed B).rename e upper inclusion equivariant
  have hS : Name.eval {p | H.mem p} Sname ∈ N.sets :=
    (M.mem_symmetricExtension upper e F H _).2 ⟨Sname, groundS, hsS, rfl⟩
  have subset : Name.eval {p | H.mem p} Sname ⊆
      Name.eval {p | H.mem p} (Name.rename upper inclusion (M.internalRowSetName s C hL)) := by
    change Name.eval {p | H.mem p} (Name.rename upper inclusion _) ⊆ _
    rw [evalLift, evalLift]
    exact M.eval_internalOutsideRowsName_subset s C hL B K
  have nonempty : (Name.eval {p | H.mem p} Sname).Nonempty := by
    change (Name.eval {p | H.mem p} (Name.rename upper inclusion _)).Nonempty
    rw [evalLift]
    exact M.eval_internalOutsideRowsName_nonempty s C hL B (unbounded B) K
  obtain ⟨x, hx, chosen, unique⟩ := selection _ hS subset nonempty
  have hxK : x ∈ Name.eval {p | K.mem p} (M.internalOutsideRowsName s C hL B) := by
    rw [← evalLift]
    exact hx
  obtain ⟨i, outside, rowValue⟩ := (M.mem_eval_internalOutsideRowsName s C hL B K x).1 hxK
  let rowName := Name.rename upper inclusion (M.internalRowName s C hL i)
  have groundRow : rowName.val ∈ M.sets := renameGround _
    (M.internalRowName_mem s C pairing unions powers separation collection infinite hL hC i)
  let sn : (M.nameDomain upper).names := ⟨Sname, groundS⟩
  let xn : (M.nameDomain upper).names := ⟨rowName, groundRow⟩
  let fn : (M.nameDomain upper).names := ⟨fname, groundF⟩
  let env := extend sn (extend xn (extend fn Fin.elim0))
  have rowEq : Name.eval {p | H.mem p} rowName = x :=
    (evalLift _).trans ((M.eval_internalRowName s C hL i K).trans rowValue)
  have truth : Realize ((M.nameDomain upper).values {p | H.mem p})
      (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula (evalAssignment {p | H.mem p} env) := by
    apply (realize_uniqueFiber_values (M.nameDomain upper) {p | H.mem p} 0 1 2 env).2
    change Name.eval {p | H.mem p} rowName ∈ Name.eval {p | H.mem p} Sname ∧
      ZFSet.pair (Name.eval {p | H.mem p} Sname) (Name.eval {p | H.mem p} rowName) ∈
        Name.eval {p | H.mem p} fname ∧
      ∀ z ∈ Name.eval {p | H.mem p} Sname,
        ZFSet.pair (Name.eval {p | H.mem p} Sname) z ∈ Name.eval {p | H.mem p} fname →
          z = Name.eval {p | H.mem p} rowName
    rw [rowEq]
    exact ⟨hx, chosen, unique⟩
  obtain ⟨p, hp, forced⟩ := (forcing_truth (M.nameDomain upper) H ordinary
    (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula env).1 truth
  refine ⟨B, i, sn, xn, fn, outside, rfl, rfl, ?_, fixedF, p, hp, forced⟩
  intro g fixed
  change e.act upper g (Name.rename upper inclusion _) = Name.rename upper inclusion _
  rw [act.act_rename_of_equivariant e lower upper inclusion equivariant]
  exact congrArg (Name.rename upper inclusion)
    (M.internalOutsideRowsName_action a s b C pairing unions powers separation infinite hL hC hG
      graph B g fixed)

end PartitionPilot.Forcing.TransitiveGround

end OAI
