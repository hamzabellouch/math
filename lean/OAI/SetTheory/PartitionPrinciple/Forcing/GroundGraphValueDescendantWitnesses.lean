import OAI.SetTheory.PartitionPrinciple.Definability.GraphValueMembershipFormula
import OAI.SetTheory.PartitionPrinciple.Definability.RenamedEntryFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.SeparationEntryFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.FinitePrincipalNameSupports

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem rename_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets) :
    ∀ τ : Name s, τ.val ∈ M.sets → (Name.rename s f τ).val ∈ M.sets := by
  intro τ
  induction τ using Name.inductionOn with
  | step τ ih =>
    intro hτ
    have members : ∀ i, renameParameters s f i ∈ M.sets :=
      Fin.cases carrier (Fin.cases graph (fun i => Fin.elim0 i))
    have witnesses : ∀ z ∈ τ.val, ∃ y ∈ M.sets,
        Realize M.sets renamedChildFormula (extend z (extend y (renameParameters s f))) := by
      intro z hz
      obtain ⟨σ, p, rfl⟩ := Name.entries_cover τ hz
      have hσ := (M.nameDomain s).children hτ hz
      have imageM := ih σ p hz hσ
      exact ⟨(Name.rename s f σ).val, imageM,
        (M.realize_renamedChildFormula s pairing unions powers separation collection carrier f graph
          σ hσ p _ imageM).2 rfl⟩
    obtain ⟨W, hW, images⟩ := M.collection_witness collection renamedChildFormula
      (renameParameters s f) members hτ witnesses
    have children : ∀ σ p, Name.Entry σ τ p → (Name.rename s f σ).val ∈ W := by
      intro σ p entry
      obtain ⟨y, hyW, rel⟩ := images _ entry
      have eq := (M.realize_renamedChildFormula s pairing unions powers separation collection carrier f graph
        σ ((M.nameDomain s).children hτ entry) p y (M.transitive hW hyW)).1 rel
      exact eq ▸ hyW
    obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW carrier
    have bound : (Name.rename s f τ).val ⊆ B := by
      intro z hz
      obtain ⟨ν, q, rfl⟩ := Name.entries_cover (Name.rename s f τ) hz
      obtain ⟨σ, p, entry, image, _⟩ := (Name.entry_rename s f τ ν q).1 hz
      exact pairBound ν.val (image ▸ children σ p entry) (s.encode q) (s.encode_mem q)
    have selected := M.separation_mem separation renamedEntryFormula (extend τ.val (renameParameters s f))
      (Fin.cases hτ members) hB
    have eq : ZFSet.sep (fun z => Realize M.sets renamedEntryFormula
        (extend z (extend τ.val (renameParameters s f)))) B = (Name.rename s f τ).val := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_sep]
      constructor
      · rintro ⟨hzB, rel⟩
        exact (M.realize_renamedEntryFormula s pairing unions powers separation collection carrier f graph
          τ hτ z (M.transitive hB hzB)).1 rel
      · intro hz
        exact ⟨bound hz, (M.realize_renamedEntryFormula s pairing unions powers separation collection carrier f graph
          τ hτ z (M.transitive hB (bound hz))).2 hz⟩
    exact eq ▸ selected

variable {G : Type u} [Group G] [PartialOrder P]

theorem act_mem (a : PosetAction G P) (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (g : G) (τ : Name s) (hτ : τ.val ∈ M.sets) : (a.act s g τ).val ∈ M.sets :=
  M.rename_mem s pairing unions powers separation collection carrier (a.iso g)
    (M.conditionMap_graph_mem a s t maps g) τ hτ

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}}
variable (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)

include pairing unions powers separation collection carrier maps closed

theorem niceNameCandidates_act_iff (K : Subgroup G) (g : G) (τ : Name s) :
    (a.act s g τ).val ∈ M.niceNameCandidates a s T (K.map (conjugateHom g)) ↔
      τ.val ∈ M.niceNameCandidates a s T K := by
  rw [M.mem_niceNameCandidates, M.mem_niceNameCandidates,
    niceNameCode_act_iff a s closed g τ]
  constructor
  · rintro ⟨ground, code⟩
    have back := M.act_mem s a t pairing unions powers separation collection
      carrier maps g⁻¹ (a.act s g τ) ground
    exact ⟨by simpa only [a.act_inv_left] using back, code⟩
  · rintro ⟨ground, code⟩
    exact ⟨M.act_mem s a t pairing unions powers separation collection
      carrier maps g τ ground, code⟩

theorem niceNameCandidates_principal_act_iff (d : PosetAction G L)
    (g : G) (v : L) (τ : Name s) :
    (a.act s g τ).val ∈ M.niceNameCandidates a s T (d.principalFix (d.iso g v)) ↔
      τ.val ∈ M.niceNameCandidates a s T (d.principalFix v) := by
  rw [← principalFix_map_conjugate d g v]
  exact M.niceNameCandidates_act_iff a s t pairing unions powers separation collection
    carrier maps closed (d.principalFix v) g τ

noncomputable def niceNameCandidateEquiv (d : PosetAction G L) (g : G) (v : L) :
    {τ : Name s // τ.val ∈ M.niceNameCandidates a s T (d.principalFix v)} ≃
      {τ : Name s // τ.val ∈ M.niceNameCandidates a s T (d.principalFix (d.iso g v))} where
  toFun τ := ⟨a.act s g τ.val,
    (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation collection
      carrier maps closed d g v τ.val).2 τ.property⟩
  invFun ν := ⟨a.act s g⁻¹ ν.val,
    (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation collection
      carrier maps closed d g v (a.act s g⁻¹ ν.val)).1 (by
        simpa only [a.act_inv_right] using ν.property)⟩
  left_inv τ := Subtype.ext (a.act_inv_left s g τ.val)
  right_inv ν := Subtype.ext (a.act_inv_right s g ν.val)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem child_mem_doubleUnion {σ τ : Name s} {p : P} (entry : Entry σ τ p) :
    σ.val ∈ ZFSet.sUnion (ZFSet.sUnion τ.val) := by
  have single : ({σ.val} : ZFSet.{u}) ∈ ZFSet.sUnion τ.val :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair σ.val (s.encode p), entry, ZFSet.mem_pair.2 (Or.inl rfl)⟩
  exact ZFSet.mem_sUnion.2 ⟨{σ.val}, single, ZFSet.mem_singleton.2 rfl⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem separationName_mem (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 1))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (context : Fin m → ZFSet.{u})
    (members : ∀ i, context i ∈ M.sets)
    (hc : context (params A.carrier) = s.carrier) (ho : context (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => context (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => context (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, context (names i) = (nameEnv i).val.val) (τ : D.names) :
    (Name.separationName D φ nameEnv τ.val).val ∈ M.sets := by
  have hτ := ground τ.val τ.property
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hτ)) carrier
  have bound : (Name.separationName D φ nameEnv τ.val).val ⊆ B := by
    intro z hz
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.separationName D φ nameEnv τ.val) hz
    obtain ⟨r, old, _, _⟩ := (Name.entry_separationName D φ nameEnv τ.val σ p).1 hz
    exact pairBound σ.val (Name.child_mem_doubleUnion old) (s.encode p) (s.encode_mem p)
  let selected := separationEntryFormula A φ (fun j => (params j).succ.succ)
    (fun i => (names i).succ.succ) 0 1
  let fullContext := extend τ.val.val context
  have correct : ∀ z ∈ M.sets, Realize M.sets selected (extend z fullContext) ↔
      z ∈ (Name.separationName D φ nameEnv τ.val).val := by
    intro z hz
    exact M.realize_separationEntryFormula s D ground pairing carrier order A φ
      (fun j => (params j).succ.succ) (fun i => (names i).succ.succ) 0 1 (extend z fullContext)
      hc ho atomic domain nameEnv hnames τ rfl hz
  have selectedM := M.separation_mem separation selected fullContext (Fin.cases hτ members) hB
  have eq : ZFSet.sep (fun z => Realize M.sets selected (extend z fullContext)) B =
      (Name.separationName D φ nameEnv τ.val).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (correct z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selectedM

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

noncomputable def immediateChildCodes (τ : Name s) : ZFSet.{u} :=
  relationImage s.carrier (ZFSet.sUnion (ZFSet.sUnion τ.val))
    (relationConverse (ZFSet.sUnion (ZFSet.sUnion τ.val)) s.carrier τ.val)

theorem mem_immediateChildCodes (τ : Name s) (y : ZFSet.{u}) :
    y ∈ immediateChildCodes τ ↔ ∃ σ : Name s, ∃ p, Entry σ τ p ∧ y = σ.val := by
  rw [immediateChildCodes, mem_relationImage]
  constructor
  · rintro ⟨_, q, _, entry⟩
    have raw := ((pair_mem_relationConverse _ _ _ y q).1 entry).2.2
    obtain ⟨σ, p, shape⟩ := entries_cover τ raw
    refine ⟨σ, p, ?_, (ZFSet.pair_inj.1 shape).1⟩
    change ZFSet.pair σ.val (s.encode p) ∈ τ.val
    rw [← shape]
    exact raw
  · rintro ⟨σ, p, entry, rfl⟩
    have bound := child_mem_doubleUnion entry
    exact ⟨bound, s.encode p, s.encode_mem p,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨bound, s.encode_mem p, entry⟩⟩

theorem immediateChildCodes_valid (τ : Name s) :
    ∀ y ∈ immediateChildCodes τ, IsName s y := by
  intro y member
  obtain ⟨σ, _, _, rfl⟩ := (mem_immediateChildCodes τ y).1 member
  exact σ.property

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem immediateChildCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (τ : Name s) (ground : τ.val ∈ M.sets) :
    Name.immediateChildCodes τ ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions ground)
  exact M.relationImage_mem separation carrier bound
    (M.relationConverse_mem pairing unions powers separation bound carrier ground)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetricSeparationName_mem (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (φ : SetFormula (n + 1))
    (nameEnv : Assignment (a.symmetricDomain s (M.nameDomain s) F) n)
    (τ : (a.symmetricDomain s (M.nameDomain s) F).names) :
    (Name.separationName (a.symmetricDomain s (M.nameDomain s) F) φ nameEnv τ.val).val ∈ M.sets := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  let context := extend s.carrier (extend s.conditionOrder (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) (fun i => (nameEnv i).val.val))))))
  let params : Fin 6 → Fin (n + 6) := extend 0 (extend 1 (extend 2 (extend 3 (extend 4 (extend 5 Fin.elim0)))))
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => (nameEnv i).property.1))))))
  apply M.separationName_mem s D (fun _ h => h.1) pairing unions powers separation carrier order
    symmetricGroundPrimitives φ params (fun i => i.succ.succ.succ.succ.succ.succ) context members rfl rfl
  · exact M.equalityMeaning_lifted s D (fun _ h => h.1) pairing unions powers separation collection
      carrier order 0 1 _ rfl rfl
  · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps 0 2 3 4 5 _ rfl rfl rfl rfl rfl
  · exact fun _ => rfl

theorem symmetric_separation (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    SeparationSchema ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) := by
  intro n φ params members x hx
  obtain ⟨y, hy, spec⟩ := symmetric_separation_scheme a (M.nameDomain s) F
    (fun g τ hτ => M.act_mem s a t pairing unions powers separation collection carrier maps g τ hτ)
    H generic (fun ψ env τ hτ => M.symmetricSeparationName_mem a s t b F K basis
      pairing unions powers separation collection carrier order group indices supports maps ψ env ⟨τ, hτ⟩)
    φ params members hx
  exact ⟨y, hy, fun z _ => spec z⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} (s : Presentation P)

noncomputable def childFamilyCodes (W : ZFSet.{u}) : ZFSet.{u} :=
  relationImage s.carrier (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion W)))
    (relationConverse (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion W))) s.carrier
      (ZFSet.sUnion W))

theorem mem_childFamilyCodes (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z)
    (y : ZFSet.{u}) :
    y ∈ childFamilyCodes s W ↔
      ∃ tau : Name s, tau.val ∈ W ∧ ∃ sigma : Name s, ∃ p,
        Entry sigma tau p ∧ y = sigma.val := by
  rw [childFamilyCodes, mem_relationImage]
  constructor
  · rintro ⟨_, q, _, coded⟩
    have raw := ((pair_mem_relationConverse _ _ _ y q).1 coded).2.2
    obtain ⟨x, hx, entry⟩ := ZFSet.mem_sUnion.1 raw
    let tau : Name s := ⟨x, valid x hx⟩
    obtain ⟨sigma, p, shape⟩ := entries_cover tau entry
    refine ⟨tau, hx, sigma, p, ?_, (ZFSet.pair_inj.1 shape).1⟩
    change ZFSet.pair sigma.val (s.encode p) ∈ x
    rw [← shape]
    exact entry
  · rintro ⟨tau, htau, sigma, p, entry, rfl⟩
    have raw : ZFSet.pair sigma.val (s.encode p) ∈ ZFSet.sUnion W :=
      ZFSet.mem_sUnion.2 ⟨tau.val, htau, entry⟩
    have bound := pair_first_mem_doubleUnion raw
    exact ⟨bound, s.encode p, s.encode_mem p,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨bound, s.encode_mem p, raw⟩⟩

theorem childFamilyCodes_valid (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z) :
    ∀ z ∈ childFamilyCodes s W, IsName s z := by
  intro z member
  obtain ⟨tau, _, sigma, _, _, rfl⟩ := (mem_childFamilyCodes s W valid z).1 member
  exact sigma.property

theorem childFamilyCodes_hs {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W → HereditarilySymmetric a s F tau)
    (sigma : Name s) (member : sigma.val ∈ childFamilyCodes s W) :
    HereditarilySymmetric a s F sigma := by
  obtain ⟨tau, htau, child, p, entry, equal⟩ :=
    (mem_childFamilyCodes s W valid sigma.val).1 member
  have same : sigma = child := Subtype.ext equal
  exact same.symm ▸ (symmetric tau htau).member entry

theorem eval_member_childFamilyCodes (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z)
    (H : Set P) (tau : Name s) (htau : tau.val ∈ W) (x : ZFSet.{u})
    (member : x ∈ eval H tau) :
    ∃ sigma : Name s, sigma.val ∈ childFamilyCodes s W ∧ eval H sigma = x := by
  obtain ⟨sigma, p, entry, _hp, equal⟩ := (mem_eval H tau x).1 member
  exact ⟨sigma, (mem_childFamilyCodes s W valid sigma.val).2 ⟨tau, htau, sigma, p, entry, rfl⟩, equal⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem childFamilyCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (W : ZFSet.{u}) (ground : W ∈ M.sets) :
    Name.childFamilyCodes s W ∈ M.sets := by
  have entries := M.union_mem unions ground
  have bound := M.union_mem unions (M.union_mem unions entries)
  exact M.relationImage_mem separation carrier bound
    (M.relationConverse_mem pairing unions powers separation bound carrier entries)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} (s : Presentation P)

noncomputable def descendantFamilyCodes (tau : Name s) : Nat → ZFSet.{u}
  | 0 => {tau.val}
  | n + 1 => childFamilyCodes s (descendantFamilyCodes tau n)

theorem descendantFamilyCodes_valid (tau : Name s) (n : Nat) :
    ∀ z ∈ descendantFamilyCodes s tau n, IsName s z := by
  induction n with
  | zero =>
    intro z member
    have same : z = tau.val := ZFSet.mem_singleton.1 member
    exact same.symm ▸ tau.property
  | succ n ih => exact childFamilyCodes_valid s _ ih

theorem descendantFamilyCodes_hs {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (tau : Name s) (symmetric : HereditarilySymmetric a s F tau) (n : Nat) :
    ∀ sigma : Name s, sigma.val ∈ descendantFamilyCodes s tau n →
      HereditarilySymmetric a s F sigma := by
  induction n with
  | zero =>
    intro sigma member
    have same : sigma = tau := Subtype.ext (ZFSet.mem_singleton.1 member)
    exact same.symm ▸ symmetric
  | succ n ih =>
    exact childFamilyCodes_hs s a F _ (descendantFamilyCodes_valid s tau n) ih

theorem value_member_fourthDescendant (H : Set P) (tau : Name s)
    (beta A x : ZFSet.{u}) (edge : ZFSet.pair beta A ∈ eval H tau) (member : x ∈ A) :
    ∃ sigma : Name s, sigma.val ∈ descendantFamilyCodes s tau 4 ∧ eval H sigma = x := by
  have zero : tau.val ∈ descendantFamilyCodes s tau 0 := ZFSet.mem_singleton.2 rfl
  obtain ⟨pairName, first, pairValue⟩ := eval_member_childFamilyCodes s
    (descendantFamilyCodes s tau 0) (descendantFamilyCodes_valid s tau 0) H tau zero _ edge
  have pairMember : ({beta, A} : ZFSet.{u}) ∈ eval H pairName := by
    rw [pairValue]
    exact ZFSet.mem_pair.2 (Or.inr rfl)
  obtain ⟨unorderedName, second, unorderedValue⟩ := eval_member_childFamilyCodes s
    (descendantFamilyCodes s tau 1) (descendantFamilyCodes_valid s tau 1) H pairName first _ pairMember
  have valueMember : A ∈ eval H unorderedName := by
    rw [unorderedValue]
    exact ZFSet.mem_pair.2 (Or.inr rfl)
  obtain ⟨valueName, third, valueValue⟩ := eval_member_childFamilyCodes s
    (descendantFamilyCodes s tau 2) (descendantFamilyCodes_valid s tau 2) H unorderedName second _ valueMember
  have elementMember : x ∈ eval H valueName := valueValue.symm ▸ member
  exact eval_member_childFamilyCodes s (descendantFamilyCodes s tau 3)
    (descendantFamilyCodes_valid s tau 3) H valueName third x elementMember

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem descendantFamilyCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (tau : Name s) (ground : tau.val ∈ M.sets) (n : Nat) :
    Name.descendantFamilyCodes s tau n ∈ M.sets := by
  induction n with
  | zero =>
    simpa only [Name.descendantFamilyCodes, ZFSet.pair_eq_singleton] using
      M.unorderedPair_mem pairing ground ground
  | succ n ih => exact M.childFamilyCodes_mem s pairing unions powers separation carrier _ ih

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem graphValue_fourthDescendant_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets)
    (z beta : (M.nameDomain s).names) (base : P)
    (forced : Forces (M.nameDomain s)
      (ex (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula)
      (extend z (extend beta Fin.elim0)) base) :
    DenseBelow base {q | ∃ tau : (M.nameDomain s).names,
      tau.val.val ∈ Name.descendantFamilyCodes s z.val 4 ∧
      Forces (M.nameDomain s) (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
        (extend tau (extend z (extend beta Fin.elim0))) q} := by
  have descendants := M.descendantFamilyCodes_mem s pairing unions powers separation carrier
    z.val z.property 4
  intro p below
  obtain ⟨H, hp, _coded, ordinary⟩ := M.exists_coded_ordinary_generic s small carrier p
  obtain ⟨tau, q, hq, _qbase, witness⟩ := ex_witness_in_filter (M.nameDomain s) H ordinary
    (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
    (extend z (extend beta Fin.elim0)) (H.upward hp below) forced
  have truth := (realize_graphValueMember_values (M.nameDomain s) {r | H.mem r} 0 1 2
    (extend tau (extend z (extend beta Fin.elim0)))).1
      (forces_sound (M.nameDomain s) H ordinary _ _ hq witness)
  obtain ⟨A, edge, member⟩ := truth
  obtain ⟨sigma, child, same⟩ := Name.value_member_fourthDescendant s {r | H.mem r}
    z.val (Name.eval {r | H.mem r} beta.val) A (Name.eval {r | H.mem r} tau.val) edge member
  let candidate : (M.nameDomain s).names := ⟨sigma, M.transitive descendants child⟩
  have actual : Realize ((M.nameDomain s).values {r | H.mem r})
      (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
      (evalAssignment {r | H.mem r} (extend candidate (extend z (extend beta Fin.elim0)))) := by
    apply (realize_graphValueMember_values (M.nameDomain s) {r | H.mem r} 0 1 2 _).2
    exact ⟨A, edge, same.symm ▸ member⟩
  obtain ⟨r, hr, recorded⟩ := (forcing_truth (M.nameDomain s) H ordinary
    (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
    (extend candidate (extend z (extend beta Fin.elim0)))).1 actual
  obtain ⟨common, _member, toP, toR⟩ := H.directed hp hr
  exact ⟨common, toP, candidate, child, forces_mono (M.nameDomain s) _ _ recorded toR⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
