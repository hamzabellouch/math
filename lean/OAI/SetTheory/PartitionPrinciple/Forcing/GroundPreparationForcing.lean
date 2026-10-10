import OAI.SetTheory.PartitionPrinciple.Definability.VisibilityProfileFormulas

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)

private theorem visibilityValues_isName (T : ZFSet.{u}) (K : I → Subgroup G)
    (i : b.carrier.toSet) :
    IsName s ((M.niceVisibilityGraph_function a s b T K).value i) := by
  obtain ⟨v, equal⟩ := (b.mem_carrier i.val).1 i.property
  have entry : ZFSet.pair i.val (M.niceVisibilityName a s T (K v)).val ∈
      M.niceVisibilityGraph a s b T K := by
    rw [← equal]
    exact (M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl
  rw [(M.niceVisibilityGraph_function a s b T K).value_eq_of_entry i entry]
  exact (M.niceVisibilityName a s T (K v)).property

noncomputable def niceVisibilityEvaluationName (T : ZFSet.{u}) (K : I → Subgroup G) : Name s :=
  Name.indexedGraphName ⊤ (M.niceVisibilityGraph_function a s b T K)
    (visibilityValues_isName M a s b T K)

theorem niceVisibilityEvaluationName_entry (T : ZFSet.{u}) (K : I → Subgroup G)
    (H : ConditionFilter P) (v : I) (V : ZFSet.{u}) :
    ZFSet.pair (b.encode v) V ∈ Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K) ↔
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v)) = V := by
  let i : b.carrier.toSet := ⟨b.encode v, b.encode_mem v⟩
  have equal := (M.niceVisibilityGraph_function a s b T K).value_eq_of_entry i
    ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl)
  have names : (⟨(M.niceVisibilityGraph_function a s b T K).value i,
      visibilityValues_isName M a s b T K i⟩ : Name s) = M.niceVisibilityName a s T (K v) :=
    Subtype.ext equal
  exact (Name.pair_mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem
    (M.niceVisibilityGraph_function a s b T K) (visibilityValues_isName M a s b T K) i V).trans
    (by rw [names])

theorem niceVisibilityEvaluationName_mem (t : Presentation G) (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    (M.niceVisibilityEvaluationName a s b T K).val ∈ M.sets := by
  exact M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) nodes
    (M.niceVisibilityGraph_mem a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid)
    (M.niceVisibilityGraph_function a s b T K) (visibilityValues_isName M a s b T K)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)
variable (K : I → Subgroup G)

def DecidesVisibilityProfile (T F : ZFSet.{u}) (z : Name s) (p : P) : Prop :=
  ∀ v : I,
    (b.encode v ∈ F → Name.ForcesMem p z (M.niceVisibilityName a s T (K v))) ∧
    (b.encode v ∉ F → ∀ q : P, q ≤ p → ¬ Name.ForcesMem q z (M.niceVisibilityName a s T (K v)))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

noncomputable def visibilityProfileEnv (F : ZFSet.{u}) (hF : F ∈ M.sets)
    (z : (M.nameDomain s).names) : Assignment (M.nameDomain s) 4 :=
  ![z, ⟨M.niceVisibilityEvaluationName a s b T K,
      M.niceVisibilityEvaluationName_mem a s b t K pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩,
    ⟨Name.check s ⊤ b.carrier, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) b.carrier nodes⟩,
    ⟨Name.check s ⊤ F, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) F hF⟩]

theorem realize_visibilityProfileEnv (F : ZFSet.{u}) (hF : F ∈ M.sets)
    (z : (M.nameDomain s).names) (H : ConditionFilter P) :
    Realize ((M.nameDomain s).values {p | H.mem p}) visibilityProfileFormula
      (evalAssignment {p | H.mem p}
        (M.visibilityProfileEnv a s t b K pairing unions powers separation collection carrier group nodes supports maps hT valid F hF z)) ↔
      ∀ v : I, Name.eval {p | H.mem p} z.val ∈
        Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v)) ↔ b.encode v ∈ F := by
  let env := M.visibilityProfileEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid F hF z
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have fields : evalAssignment {p | H.mem p} env =
      ![Name.eval {p | H.mem p} z.val,
        Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K), b.carrier, F] := by
    funext i
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))) i
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
  have meaning := N.realize_visibilityProfileFormula (evalAssignment {p | H.mem p} env)
    (fun i => ⟨env i, rfl⟩)
  rw [fields] at meaning
  change Realize N.sets visibilityProfileFormula (evalAssignment {p | H.mem p} env) ↔ _
  rw [fields, meaning]
  constructor
  · intro allNodes v
    have visibilityGround := M.niceVisibilityName_mem a s t b K pairing unions powers separation collection
      carrier group supports maps hT valid v (M.transitive nodes (b.encode_mem v))
    exact allNodes (b.encode v) (b.encode_mem v) _ ⟨⟨_, visibilityGround⟩, rfl⟩
      ((M.niceVisibilityEvaluationName_entry a s b T K H v _).2 rfl)
  · intro typed code hcode V hV entry
    obtain ⟨v, rfl⟩ := (b.mem_carrier code).1 hcode
    have equal := (M.niceVisibilityEvaluationName_entry a s b T K H v V).1 entry
    exact equal ▸ typed v

theorem forces_visibilityProfile_iff (small : M.sets.Countable)
    (F : ZFSet.{u}) (hF : F ∈ M.sets) (z : (M.nameDomain s).names) (p : P) :
    Forces (M.nameDomain s) visibilityProfileFormula
      (M.visibilityProfileEnv a s t b K pairing unions powers separation collection carrier group nodes supports maps hT valid F hF z) p ↔
      M.DecidesVisibilityProfile a s b K T F z.val p := by
  let env := M.visibilityProfileEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid F hF z
  let vis (v : I) : (M.nameDomain s).names := ⟨M.niceVisibilityName a s T (K v),
    M.niceVisibilityName_mem a s t b K pairing unions powers separation collection
      carrier group supports maps hT valid v (M.transitive nodes (b.encode_mem v))⟩
  have global := M.ordinaryForces_iff_all_generics s small carrier visibilityProfileFormula env p
  constructor
  · intro forced v
    have profile (H : ConditionFilter P) (hp : H.mem p)
        (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :=
      (M.realize_visibilityProfileEnv a s t b K pairing unions powers separation collection
        carrier group nodes supports maps hT valid F hF z H).1 (global.1 forced H hp generic) v
    constructor
    · intro yes
      apply (M.ordinaryForces_iff_all_generics s small carrier (.mem 0 1) ![z, vis v] p).2
      intro H hp generic
      exact (profile H hp generic).2 yes
    · intro no
      change Forces (M.nameDomain s) (.neg (.mem 0 1)) ![z, vis v] p
      apply (M.ordinaryForces_iff_all_generics s small carrier (.neg (.mem 0 1)) ![z, vis v] p).2
      intro H hp generic member
      exact no ((profile H hp generic).1 member)
  · intro decisions
    apply global.2
    intro H hp generic
    apply (M.realize_visibilityProfileEnv a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid F hF z H).2
    intro v
    by_cases member : b.encode v ∈ F
    · have atom : Forces (M.nameDomain s) (.mem 0 1 : SetFormula 2) ![z, vis v] p := by
        exact (decisions v).1 member
      have positive := forces_sound (M.nameDomain s) H generic (.mem 0 1 : SetFormula 2) ![z, vis v] hp atom
      exact ⟨fun _ => member, fun _ => positive⟩
    · have atom : Forces (M.nameDomain s) (.neg (.mem 0 1) : SetFormula 2) ![z, vis v] p := by
        exact (decisions v).2 member
      have negative := forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1) : SetFormula 2) ![z, vis v] hp atom
      exact ⟨fun yes => False.elim (negative yes), fun yes => False.elim (member yes)⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (K : I → Subgroup G)

omit [OrderTop P] in
private theorem rawForces_pair_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (phi : SetFormula 2) (p : P) (z tau : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![z.val.val, tau.val.val] ↔
      Forces (M.nameDomain s) phi ![z, tau] p := by
  have fields : (fun j : Fin 2 => (![z, tau] j).val.val) = ![z.val.val, tau.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  have translated := M.stageOneRawForces_iff s pairing unions powers separation collection
    carrier order phi p ![z, tau]
  rw [fields] at translated
  exact translated

theorem preparationForcingCode_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (T N : ZFSet.{u}) (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (namesGround : N ∈ M.sets) (valid : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod b.carrier N) (p : P) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode p) b.carrier
      (M.niceVisibilityGraph a s b T K) z.val.val F f ↔
      M.DecidesVisibilityProfile a s b K T F z.val p ∧
      ∀ v (tau : Name s), tau.val ∈ N → ZFSet.pair v tau.val ∈ f →
        Name.ForcesEq p z.val tau := by
  let vis (v : I) : (M.nameDomain s).names :=
    ⟨M.niceVisibilityName a s T (K v),
      M.pair_right (M.transitive graphGround
        ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl))⟩
  have memForces (v : I) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.mem 0 1 : SetFormula 2) ![z.val.val, (vis v).val.val] ↔
        Name.ForcesMem p z.val (vis v).val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.mem 0 1 : SetFormula 2) p z (vis v)
  have negForces (v : I) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.neg (.mem 0 1) : SetFormula 2) ![z.val.val, (vis v).val.val] ↔
        ∀ q : P, q ≤ p → ¬ Name.ForcesMem q z.val (vis v).val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.neg (.mem 0 1) : SetFormula 2) p z (vis v)
  have eqForces (tau : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.equal 0 1 : SetFormula 2) ![z.val.val, tau.val.val] ↔
        Name.ForcesEq p z.val tau.val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.equal 0 1 : SetFormula 2) p z tau
  constructor
  · rintro ⟨profile, equalities⟩
    constructor
    · intro v
      have decisions := profile (b.encode v) (vis v).val.val
        ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl) (b.encode_mem v)
      exact ⟨fun yes => (memForces v).1 (decisions.1 yes),
        fun no => (negForces v).1 (decisions.2 no)⟩
    · intro v tau htau entry
      exact (eqForces ⟨tau, M.transitive namesGround htau⟩).1 (equalities v tau.val entry)
  · rintro ⟨profile, equalities⟩
    constructor
    · intro v V entry hv
      obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 hv
      have eq := (M.pair_mem_niceVisibilityGraph a s b T K i V).1 entry
      subst V
      exact ⟨fun yes => (memForces i).2 ((profile i).1 yes),
        fun no => (negForces i).2 ((profile i).2 no)⟩
    · intro v tau entry
      have htau := (ZFSet.pair_mem_prod.1 (range entry)).2
      let name : (M.nameDomain s).names := ⟨⟨tau, valid tau htau⟩, M.transitive namesGround htau⟩
      exact (eqForces name).2 (equalities v name.val htau entry)

end PartitionPilot.Forcing.TransitiveGround

end OAI
