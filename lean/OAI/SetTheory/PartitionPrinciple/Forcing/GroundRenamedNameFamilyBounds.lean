import OAI.SetTheory.PartitionPrinciple.Definability.GroundLiftedRowTupleProvenance
import OAI.SetTheory.PartitionPrinciple.Definability.GroundNiceVisibilityGraphs
import OAI.SetTheory.PartitionPrinciple.Models.GroundRefinementQuotientNames

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure NiceNameSystem (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Prop where
  candidate_graph_ground : M.niceNameCandidateGraph a s b T d.principalFix ∈ M.sets
  candidate_graph_function : FunctionGraphOn b.carrier
    (M.niceNameCandidateGraph a s b T d.principalFix)
  candidate_entries : ∀ v z, ZFSet.pair (b.encode v) z ∈
    M.niceNameCandidateGraph a s b T d.principalFix ↔
      z = M.niceNameCandidates a s T (d.principalFix v)
  visibility_graph_ground : M.niceVisibilityGraph a s b T d.principalFix ∈ M.sets
  visibility_graph_function : FunctionGraphOn b.carrier
    (M.niceVisibilityGraph a s b T d.principalFix)
  visibility_entries : ∀ v z, ZFSet.pair (b.encode v) z ∈
    M.niceVisibilityGraph a s b T d.principalFix ↔
      z = (M.niceVisibilityName a s T (d.principalFix v)).val
  candidate_hs : ∀ v (τ : Name s), τ.val ∈ M.niceNameCandidates a s T (d.principalFix v) →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ
  visibility_ground : ∀ v, (M.niceVisibilityName a s T (d.principalFix v)).val ∈ M.sets
  visibility_support : ∀ v, d.principalFix v ≤
    a.stabilizer s (M.niceVisibilityName a s T (d.principalFix v))
  visibility_hs : ∀ v, HereditarilySymmetric a s (d.principalSupportFamily base directed)
    (M.niceVisibilityName a s T (d.principalFix v))
  visibility_action : ∀ g v, a.act s g (M.niceVisibilityName a s T (d.principalFix v)) =
    M.niceVisibilityName a s T (d.principalFix (d.iso g v))
  normalization_candidate : ∀ v (τ : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s τ.val →
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈
      M.niceNameCandidates a s T (d.principalFix v)
  normalization_visible : ∀ v (τ : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s τ.val →
    ∀ (H : ConditionFilter P), H.GenericFor (formulaFamily (M.nameDomain s)) →
    Name.eval {p | H.mem p} τ.val ⊆ Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) →
    Name.eval {p | H.mem p} τ.val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v))

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (terms : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)

include pairing unions powers separation collection carrier order maps hT valid terms in
theorem niceNormalize_mem_niceNameCandidates (K : Subgroup G)
    (τ : (M.nameDomain s).names) (fixed : K ≤ a.stabilizer s τ.val) :
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈ M.niceNameCandidates a s T K := by
  apply (M.mem_niceNameCandidates a s T K _).2
  refine ⟨M.niceNormalize_mem s pairing unions powers separation collection carrier order hT valid τ, ?_⟩
  exact Name.niceNormalize_niceNameCode a (M.nameDomain s)
    (fun g σ hσ => M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ)
    T valid terms τ K fixed

include pairing unions powers separation collection carrier order maps hT valid terms in
theorem niceNormalize_mem_eval_niceVisibilityName (K : Subgroup G)
    (τ : (M.nameDomain s).names) (fixed : K ≤ a.stabilizer s τ.val)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (subset : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) :
    Name.eval {p | H.mem p} τ.val ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T K) := by
  apply (M.mem_eval_niceVisibilityName a s T K {p | H.mem p} H.top_mem _).2
  refine ⟨Name.niceNormalize (M.nameDomain s) T valid τ,
    M.niceNormalize_mem_niceNameCandidates a s t pairing unions powers separation collection
      carrier order maps hT valid terms K τ fixed, ?_⟩
  exact Name.eval_niceNormalize_of_subset (M.nameDomain s) T valid τ
    (M.familySet_mem s ⊤ pairing unions powers separation hT
      (M.transitive carrier (s.encode_mem ⊤)) valid) H generic subset

include pairing unions powers separation collection carrier order maps hT valid terms in
theorem niceNameSystem (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (children : ∀ σ : Name s, σ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) σ) :
    NiceNameSystem M a s b d base directed T valid where
  candidate_graph_ground := M.niceNameCandidateGraph_mem a s t b d.principalFix
    pairing unions powers separation collection carrier group indices supports maps hT valid
  candidate_graph_function := M.niceNameCandidateGraph_function a s b T d.principalFix
  candidate_entries := M.pair_mem_niceNameCandidateGraph a s b T d.principalFix
  visibility_graph_ground := M.niceVisibilityGraph_mem a s t b d.principalFix
    pairing unions powers separation collection carrier group indices supports maps hT valid
  visibility_graph_function := M.niceVisibilityGraph_function a s b T d.principalFix
  visibility_entries := M.pair_mem_niceVisibilityGraph a s b T d.principalFix
  candidate_hs := fun v τ member => niceNameCode_principal_hs a s d base v directed children
    ((M.mem_niceNameCandidates a s T (d.principalFix v) τ.val).1 member).2
  visibility_ground := fun v => M.niceVisibilityName_mem a s t b d.principalFix
    pairing unions powers separation collection carrier group supports maps hT valid v
    (M.transitive indices (b.encode_mem v))
  visibility_support := fun v => M.niceVisibilityName_support a s T (d.principalFix v)
  visibility_hs := fun v => M.niceVisibilityName_principal_hs a s d base v directed T children
  visibility_action := M.act_niceVisibilityName a s t d pairing unions powers separation
    collection carrier maps terms
  normalization_candidate := fun v τ fixed =>
    M.niceNormalize_mem_niceNameCandidates a s t pairing unions powers separation collection
      carrier order maps hT valid terms (d.principalFix v) τ fixed
  normalization_visible := fun v τ fixed H generic subset =>
    M.niceNormalize_mem_eval_niceVisibilityName a s t pairing unions powers separation collection
      carrier order maps hT valid terms (d.principalFix v) τ fixed H generic subset

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

noncomputable def stageOneClassName (R w : (M.nameDomain s).names) : (M.nameDomain s).names :=
  ⟨Name.refinementClass T valid R.val w.val,
    M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid
      R.val w.val R.property w.property⟩

noncomputable def stageOneMapName (U Rf Rc : (M.nameDomain s).names) : (M.nameDomain s).names :=
  ⟨Name.refinementNaturalMap T valid U.val Rf.val Rc.val,
    M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order hT valid
      U.val Rf.val Rc.val U.property Rf.property Rc.property⟩

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

noncomputable def stageOneVisibilityName
    (system : NiceNameSystem M a s b d base directed T valid) (v : L) :
    (M.nameDomain s).names :=
  ⟨M.niceVisibilityName a s T (d.principalFix v), system.visibility_ground v⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T : ZFSet.{u}) (H : ConditionFilter P)

noncomputable def visibleSupportProfile (z : ZFSet.{u}) : ZFSet.{u} :=
  b.subset (fun v => z ∈ Name.eval {p | H.mem p}
    (M.niceVisibilityName a s T (d.principalFix v)))

theorem encode_mem_visibleSupportProfile (z : ZFSet.{u}) (v : L) :
    b.encode v ∈ M.visibleSupportProfile a s b d T H z ↔
      z ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) :=
  b.encode_mem_subset _ v

theorem visibleSupportProfile_upward (z : ZFSet.{u}) {v w : L} (lower : v ≤ w)
    (member : b.encode v ∈ M.visibleSupportProfile a s b d T H z) :
    b.encode w ∈ M.visibleSupportProfile a s b d T H z := by
  have seen := (M.encode_mem_visibleSupportProfile a s b d T H z v).1 member
  obtain ⟨τ, candidate, equal⟩ :=
    (M.mem_eval_niceVisibilityName a s T (d.principalFix v) _ H.top_mem z).1 seen
  have data := (M.name_mem_niceNameCandidates a s T (d.principalFix v) τ).1 candidate
  apply (M.encode_mem_visibleSupportProfile a s b d T H z w).2
  apply (M.mem_eval_niceVisibilityName a s T (d.principalFix w) _ H.top_mem z).2
  exact ⟨τ, (M.name_mem_niceNameCandidates a s T (d.principalFix w) τ).2
    ⟨data.1, data.2.1, le_trans (d.principalFix_antitone lower) data.2.2⟩, equal⟩

variable (valid : ∀ z ∈ T, IsName s z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (z : (M.nameDomain s).names)
variable (hs : HereditarilySymmetric a s (d.principalSupportFamily base directed) z.val)
variable (subset : Name.eval {p | H.mem p} z.val ⊆
  Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))

include system generic hs subset in
theorem visibleSupportProfile_nonempty :
    (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)).Nonempty := by
  obtain ⟨v, support⟩ := hs.symmetric
  exact ⟨b.encode v, (M.encode_mem_visibleSupportProfile a s b d T H _ v).2
    (system.normalization_visible v z support H generic subset)⟩

variable (meet : L → L → L)
variable (descent : ∀ (v w : L) (x y : (M.nameDomain s).names),
  d.principalFix v ≤ a.stabilizer s x.val →
  d.principalFix w ≤ a.stabilizer s y.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
  Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
  ∃ τ : (M.nameDomain s).names,
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ.val ∧
    d.principalFix (meet v w) ≤ a.stabilizer s τ.val ∧
    Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)

include system generic subset descent in
theorem visibleSupportProfile_meet (v w : L)
    (left : b.encode v ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val))
    (right : b.encode w ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) :
    b.encode (meet v w) ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) := by
  obtain ⟨x, hx, ex⟩ := (M.mem_eval_niceVisibilityName a s T (d.principalFix v) _ H.top_mem _).1
    ((M.encode_mem_visibleSupportProfile a s b d T H _ v).1 left)
  obtain ⟨y, hy, ey⟩ := (M.mem_eval_niceVisibilityName a s T (d.principalFix w) _ H.top_mem _).1
    ((M.encode_mem_visibleSupportProfile a s b d T H _ w).1 right)
  have dx := (M.name_mem_niceNameCandidates a s T (d.principalFix v) x).1 hx
  have dy := (M.name_mem_niceNameCandidates a s T (d.principalFix w) y).1 hy
  obtain ⟨τ, _, fixed, equal⟩ := descent v w ⟨x, dx.1⟩ ⟨y, dy.1⟩ dx.2.2 dy.2.2
    (system.candidate_hs v x hx) (system.candidate_hs w y hy) (ex.trans ey.symm)
  have target : Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} z.val := equal.trans ex
  have bounded : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := target.symm ▸ subset
  apply (M.encode_mem_visibleSupportProfile a s b d T H _ (meet v w)).2
  exact target ▸ system.normalization_visible (meet v w) τ fixed H generic bounded

include system generic hs subset descent in
theorem visibleSupportProfile_filter :
    MeetFilterCode b.carrier b.conditionOrder ((b.product b).graph b (fun vw => meet vw.1 vw.2))
      (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) := by
  refine ⟨b.subset_carrier _, M.visibleSupportProfile_nonempty a s b d base directed T H
    valid system generic z hs subset, ?_, ?_⟩
  · intro x hx y hy lower
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ hx)
    obtain ⟨w, rfl⟩ := (b.mem_carrier y).1 hy
    exact M.visibleSupportProfile_upward a s b d T H _ ((b.pair_mem_conditionOrder v w).1 lower) hx
  · intro x hx y hy out entry
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ hx)
    obtain ⟨w, rfl⟩ := (b.mem_carrier y).1 (b.subset_carrier _ hy)
    have outCarrier := (ZFSet.pair_mem_prod.1
      (((b.product b).graph_isFunc b (fun vw => meet vw.1 vw.2)).1 entry)).2
    obtain ⟨k, rfl⟩ := (b.mem_carrier out).1 outCarrier
    have equal := ((b.product b).pair_mem_graph b (fun vw => meet vw.1 vw.2) (v, w) k).1 entry
    exact equal ▸ M.visibleSupportProfile_meet a s b d base directed T H valid system generic z
      subset meet descent v w hx hy

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem pairEmpty_name_mem (hs : s.carrier ∈ M.sets) (τ : Name s) (hτ : τ.val ∈ M.sets) :
    (Name.presentationEquiv s s.pairEmpty τ).val ∈ M.sets :=
  M.rename_between_mem s s.pairEmpty pairing unions powers separation collection hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs) id
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs) τ hτ

theorem pairEmpty_name_inverse_mem (hs : s.carrier ∈ M.sets)
    (τ : Name s.pairEmpty) (hτ : τ.val ∈ M.sets) :
    ((Name.presentationEquiv s s.pairEmpty).symm τ).val ∈ M.sets :=
  M.rename_between_mem s.pairEmpty s pairing unions powers separation collection
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs) hs id
    (M.pairEmpty_inverseGraph_mem pairing unions powers separation s hs) τ hτ

theorem pairEmpty_name_ground_iff (hs : s.carrier ∈ M.sets) (τ : Name s) :
    (Name.presentationEquiv s s.pairEmpty τ).val ∈ M.sets ↔ τ.val ∈ M.sets := by
  constructor
  · intro h
    have back := M.pairEmpty_name_inverse_mem s pairing unions powers separation collection hs _ h
    simpa only [Equiv.symm_apply_apply] using back
  · exact M.pairEmpty_name_mem s pairing unions powers separation collection hs τ

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable {G : Type v} [Group G] (a : PosetAction G P) (s : Presentation P)
variable (F : NormalSubgroupFamily G)

theorem pairEmpty_nameFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (T : ZFSet.{u}) (hT : T ∈ M.sets)
    (valid : ∀ x ∈ T, IsName s x)
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ) :
    let lifted := Name.renamedFamily s.pairEmpty id T valid
    let graph := Name.renameFamilyGraph s.pairEmpty id T valid
    lifted ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
      (∀ x ∈ lifted, IsName s.pairEmpty x) ∧
      (∀ σ : Name s.pairEmpty, σ.val ∈ lifted → HereditarilySymmetric a s.pairEmpty F σ) ∧
      (∀ g (σ : Name s.pairEmpty), σ.val ∈ lifted → (a.act s.pairEmpty g σ).val ∈ lifted) ∧
      ∀ (H : Set P) (x : ZFSet.{u}),
        (∃ τ : Name s.pairEmpty, τ.val ∈ lifted ∧ Name.eval H τ = x) ↔
          ∃ σ : Name s, σ.val ∈ T ∧ Name.eval H σ = x := by
  have target := M.pairEmpty_carrier_mem pairing unions powers separation s hs
  have map := M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs
  exact ⟨M.renamedFamily_mem s s.pairEmpty pairing unions powers separation collection hs target id map T hT valid,
    M.renameFamilyGraph_mem s s.pairEmpty pairing unions powers separation collection hs target id map T hT valid,
    Name.presentationFamily_injection s.pairEmpty T valid,
    Name.renamedFamily_valid s.pairEmpty id T valid,
    Name.renamedFamily_hs a s.pairEmpty F T valid children,
    Name.renamedFamily_closed a s.pairEmpty T valid closed,
    Name.eval_renamedFamily s.pairEmpty T valid⟩

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem renamedFamily_inverse (t : Presentation P) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) :
    renamedFamily s id (renamedFamily t id T valid) (renamedFamily_valid t id T valid) = T := by
  apply ZFSet.ext
  intro z
  rw [mem_renamedFamily]
  constructor
  · rintro ⟨τ, hτ, equal⟩
    obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
    have same : τ = rename t id σ := Subtype.ext codes
    rw [same, rename_comp, Function.id_comp, rename_id] at equal
    exact equal.symm ▸ hσ
  · intro hz
    let σ : Name s := ⟨z, valid z hz⟩
    refine ⟨rename t id σ, (mem_renamedFamily t id T valid _).2 ⟨σ, hz, rfl⟩, ?_⟩
    rw [rename_comp, Function.id_comp, rename_id]

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}

theorem renamedFamily_below (s t : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (forward : s.graph t id ∈ M.sets) (backward : t.graph s id ∈ M.sets)
    {T K : ZFSet.{u}} (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (small : GroundBelow M T K) :
    GroundBelow M (Name.renamedFamily t id T valid) K := by
  have hLifted := M.renamedFamily_mem s t pairing unions powers separation collection hs ht id forward T hT valid
  have validLifted := Name.renamedFamily_valid t id T valid
  have hInverse := M.renameFamilyGraph_mem t s pairing unions powers separation collection ht hs id backward
    (Name.renamedFamily t id T valid) hLifted validLifted
  have inverse := Name.presentationFamily_injection s (Name.renamedFamily t id T valid) validLifted
  rw [Name.renamedFamily_inverse] at inverse
  exact small.of_embeddable pairing unions powers separation hLifted hT hK ⟨_, hInverse, inverse⟩

theorem pairEmpty_renamedFamily_below (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) {T K : ZFSet.{u}} (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (small : GroundBelow M T K) :
    GroundBelow M (Name.renamedFamily s.pairEmpty id T valid) K :=
  M.renamedFamily_below s s.pairEmpty pairing unions powers separation collection hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs)
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs)
    (M.pairEmpty_inverseGraph_mem pairing unions powers separation s hs) hT hK valid small

end PartitionPilot.Forcing.TransitiveGround

end

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem pairEmpty_niceNameSystem (a : PosetAction G P) (s : Presentation P)
    (t : Presentation G) (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (action : a.actionGraph s t ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (children : ∀ σ : Name s, σ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) σ) :
    let lifted := Name.renamedFamily s.pairEmpty id T valid
    let graph := Name.renameFamilyGraph s.pairEmpty id T valid
    NiceNameSystem M a s b d base directed T valid ∧
    lifted ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
      ∃ liftedValid : ∀ z ∈ lifted, IsName s.pairEmpty z,
        NiceNameSystem M a s.pairEmpty b d base directed lifted liftedValid ∧
        ∀ (H : Set P) (x : ZFSet.{u}),
          (∃ τ : Name s.pairEmpty, τ.val ∈ lifted ∧ Name.eval H τ = x) ↔
            ∃ σ : Name s, σ.val ∈ T ∧ Name.eval H σ = x := by
  obtain ⟨liftedGround, graphGround, injection, liftedValid, liftedHS, liftedClosed, values⟩ :=
    M.pairEmpty_nameFamily a s (d.principalSupportFamily base directed)
      pairing unions powers separation collection carrier T hT valid closed children
  have rawMaps := M.conditionMapFamily_mem_of_actionGraph a s t
    pairing unions powers separation collection carrier group action
  have pairedCarrier := M.pairEmpty_carrier_mem pairing unions powers separation s carrier
  have pairedOrder := M.pairEmpty_order_mem pairing unions powers separation s carrier order
  have pairedMaps := M.pairEmpty_conditionMapFamily_mem pairing unions powers separation s a t
    collection carrier group action
  refine ⟨M.niceNameSystem a s t pairing unions powers separation collection carrier order
    rawMaps hT valid closed b d base directed group indices supports children,
    liftedGround, graphGround, injection, liftedValid, ?_, values⟩
  exact M.niceNameSystem a s.pairEmpty t pairing unions powers separation collection
    pairedCarrier pairedOrder pairedMaps liftedGround liftedValid liftedClosed
    b d base directed group indices supports liftedHS

end PartitionPilot.Forcing.TransitiveGround

end OAI
