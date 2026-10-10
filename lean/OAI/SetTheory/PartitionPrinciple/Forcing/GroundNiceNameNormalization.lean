import OAI.SetTheory.PartitionPrinciple.Forcing.IndexedTupleNames
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPredenseMeet

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u v
namespace Name
variable {P : Type u} {s : Presentation P}

noncomputable def familySet (one : P) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) : Name s :=
  assemble (fun z : T => ⟨z.val, valid z.val z.property⟩) (fun _ => one)

theorem entry_familySet (one : P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (σ : Name s) (p : P) : Entry σ (familySet one T valid) p ↔ σ.val ∈ T ∧ p = one := by
  refine (entry_assemble (fun member : T => ⟨member.val, valid member.val member.property⟩)
    (fun _ => one) σ p).trans ?_
  constructor
  · rintro ⟨z, eq, hp⟩
    exact ⟨congrArg Subtype.val eq ▸ z.property, hp.symm⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨⟨σ.val, hσ⟩, Subtype.ext rfl, rfl⟩

theorem familySet_code (one : P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) :
    (familySet one T valid).val = ZFSet.prod T {s.encode one} := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range, ZFSet.mem_prod]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, s.encode one, ZFSet.mem_singleton.2 rfl, rfl⟩
  · rintro ⟨x, hx, y, hy, eq⟩
    have same := ZFSet.mem_singleton.1 hy
    subst y
    exact ⟨⟨x, hx⟩, eq.symm⟩

theorem mem_eval_familySet (H : Set P) (one : P) (hone : one ∈ H)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (x : ZFSet.{u}) :
    x ∈ eval H (familySet one T valid) ↔ ∃ τ : Name s, τ.val ∈ T ∧ eval H τ = x := by
  rw [mem_eval]
  simp only [entry_familySet]
  constructor
  · rintro ⟨τ, p, ⟨hτ, rfl⟩, _, eq⟩
    exact ⟨τ, hτ, eq⟩
  · rintro ⟨τ, hτ, eq⟩
    exact ⟨τ, one, ⟨hτ, rfl⟩, hone, eq⟩

theorem act_familySet {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T) (g : G) :
    a.act s g (familySet ⊤ T valid) = familySet ⊤ T valid := by
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (familySet ⊤ T valid)) p ↔ _
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨τ, q, entry, eq, hp⟩
    obtain ⟨hτ, rfl⟩ := (entry_familySet ⊤ T valid τ q).1 entry
    have target := closed g τ hτ
    change a.act s g τ = σ at eq
    exact ⟨eq ▸ target, hp.symm.trans (a.iso g).map_top⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨a.act s g⁻¹ σ, ⊤,
      (entry_familySet ⊤ T valid _ ⊤).2 ⟨closed g⁻¹ σ hσ, rfl⟩,
      a.act_inv_right s g σ, (a.iso g).map_top⟩

theorem familySet_hs {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (familySet ⊤ T valid) := by
  refine HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    exact act_familySet a T valid closed g
  · intro τ p entry
    exact children τ ((entry_familySet ⊤ T valid τ p).1 entry).1

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem familySet_mem {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (hone : s.encode one ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) : (Name.familySet one T valid).val ∈ M.sets := by
  rw [Name.familySet_code]
  apply M.prod_mem pairing unions powers separation hT
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u}

theorem rename_familySet_of_encode (s : Presentation Upper) (t : Presentation Lower)
    (inclusion : Lower → Upper) (codes : ∀ p, s.encode (inclusion p) = t.encode p)
    (upperOne : Upper) (lowerOne : Lower) (sameTop : s.encode upperOne = t.encode lowerOne)
    (T : ZFSet.{u}) (validUpper : ∀ z ∈ T, IsName s z)
    (validLower : ∀ z ∈ T, IsName t z) :
    rename s inclusion (familySet lowerOne T validLower) = familySet upperOne T validUpper := by
  apply Subtype.ext
  rw [rename_val_of_encode s inclusion codes, familySet_code, familySet_code, sameTop]

theorem eval_familySet_crossStage (s : Presentation Upper) (t : Presentation Lower)
    (inclusion : Lower → Upper) (codes : ∀ p, s.encode (inclusion p) = t.encode p)
    (upperOne : Upper) (lowerOne : Lower) (sameTop : s.encode upperOne = t.encode lowerOne)
    (T : ZFSet.{u}) (validUpper : ∀ z ∈ T, IsName s z)
    (validLower : ∀ z ∈ T, IsName t z) (H : Set Upper) :
    eval H (familySet upperOne T validUpper) =
      eval {p | inclusion p ∈ H} (familySet lowerOne T validLower) := by
  rw [← rename_familySet_of_encode s t inclusion codes upperOne lowerOne sameTop T validUpper validLower]
  exact eval_rename s inclusion H _

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u})
variable (valid : ∀ z ∈ J, IsName t z) (D : NameDomain s) (tau : Name s)
variable (H : ConditionFilter Upper) (generic : H.GenericFor (atomicFamily D))
variable (target : tau ∈ D.names)
variable (terms : ∀ sigma : Name t, sigma.val ∈ J → rename s inclusion sigma ∈ D.names)
variable (one : Lower) (hone : H.mem (inclusion one))
variable (decisions : ∀ sigma : Name t, sigma.val ∈ J → ∃ p : Lower,
  H.mem (inclusion p) ∧
    (ForcesMem (inclusion p) (rename s inclusion sigma) tau ∨
      ∀ q, q ≤ inclusion p → ¬ ForcesMem q (rename s inclusion sigma) tau))

include generic target terms hone decisions

theorem eval_crossStageMembershipName_of_decisions :
    eval {p | H.mem (inclusion p)} (crossStageMembershipName s t inclusion J valid tau) =
      eval {p | H.mem p} tau ∩
        eval {p | H.mem (inclusion p)} (familySet one J valid) := by
  apply ZFSet.ext
  intro x
  constructor
  · intro member
    obtain ⟨sigma, p, entry, hp, value⟩ := (mem_eval _ _ x).1 member
    obtain ⟨inJ, forced⟩ := (entry_crossStageMembershipName s t inclusion J tau valid sigma p).1 entry
    have sound := forcesMem_sound D H generic (terms sigma inJ) target hp forced
    rw [eval_rename] at sound
    change eval {p | H.mem (inclusion p)} sigma ∈ eval {p | H.mem p} tau at sound
    refine ZFSet.mem_inter.2 ⟨value ▸ sound, ?_⟩
    exact (mem_eval_familySet _ one hone J valid x).2 ⟨sigma, inJ, value⟩
  · intro member
    obtain ⟨inTau, inFamily⟩ := ZFSet.mem_inter.1 member
    obtain ⟨sigma, inJ, value⟩ := (mem_eval_familySet _ one hone J valid x).1 inFamily
    have upperMember : eval {p | H.mem p} (rename s inclusion sigma) ∈
        eval {p | H.mem p} tau := by
      rw [eval_rename]
      change eval {p | H.mem (inclusion p)} sigma ∈ eval {p | H.mem p} tau
      exact value.symm ▸ inTau
    obtain ⟨p, hp, positive | negative⟩ := decisions sigma inJ
    · exact (mem_eval _ _ x).2 ⟨sigma, p,
        (entry_crossStageMembershipName s t inclusion J tau valid sigma p).2 ⟨inJ, positive⟩,
        hp, value⟩
    · obtain ⟨q, hq, forced⟩ :=
        (eval_mem_iff_forcesMem D H generic (terms sigma inJ) target).1 upperMember
      obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
      exact False.elim (negative r rp (forcesMem_mono forced rq))

theorem eval_crossStageMembershipName_of_subset
    (subset : eval {p | H.mem p} tau ⊆
      eval {p | H.mem (inclusion p)} (familySet one J valid)) :
    eval {p | H.mem (inclusion p)} (crossStageMembershipName s t inclusion J valid tau) =
      eval {p | H.mem p} tau := by
  rw [eval_crossStageMembershipName_of_decisions s t inclusion J valid D tau H generic
    target terms one hone decisions]
  apply ZFSet.ext
  intro x
  exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
    fun member => ZFSet.mem_inter.2 ⟨member, subset member⟩⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_subset_familySet_of_code_subset (H : ConditionFilter P)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (tau : Name s)
    (shape : tau.val ⊆ ZFSet.prod T s.carrier) :
    eval {p | H.mem p} tau ⊆ eval {p | H.mem p} (familySet ⊤ T valid) := by
  intro x member
  obtain ⟨sigma, p, entry, _, value⟩ := (mem_eval {p | H.mem p} tau x).1 member
  have term : sigma.val ∈ T := (ZFSet.pair_mem_prod.1 (shape entry)).1
  exact (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).2
    ⟨sigma, term, value⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization SetFormula
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def niceNormalize (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names) : Name s :=
  separationName D (.mem 0 1) (extend τ Fin.elim0) (familySet ⊤ T valid)

theorem entry_niceNormalize (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names) (σ : Name s) (p : P) :
    Entry σ (niceNormalize D T valid τ) p ↔
      σ.val ∈ T ∧ ∃ h : σ ∈ D.names,
        Forces D (.mem 0 1) (extend ⟨σ, h⟩ (extend τ Fin.elim0)) p := by
  rw [niceNormalize, entry_separationName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid σ r).1 entry).1, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid σ ⊤).2 ⟨member, rfl⟩, le_top, forced⟩

theorem niceNormalize_subset (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names) :
    (niceNormalize D T valid τ).val ⊆ ZFSet.prod T s.carrier := by
  intro z member
  obtain ⟨σ, p, rfl⟩ := entries_cover (niceNormalize D T valid τ) member
  exact ZFSet.pair_mem_prod.2
    ⟨((entry_niceNormalize D T valid τ σ p).1 member).1, s.encode_mem p⟩

theorem eval_niceNormalize (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) :
    eval {p | H.mem p} (niceNormalize D T valid τ) =
      eval {p | H.mem p} τ.val ∩ eval {p | H.mem p} (familySet ⊤ T valid) := by
  rw [niceNormalize, eval_separationName D H generic (.mem 0 1) (extend τ Fin.elim0) family]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, ZFSet.mem_inter]
  change (_ ∧ x ∈ eval {p | H.mem p} τ.val) ↔ _
  exact and_comm

theorem eval_niceNormalize_of_subset (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (subset : eval {p | H.mem p} τ.val ⊆
      eval {p | H.mem p} (familySet ⊤ T valid)) :
    eval {p | H.mem p} (niceNormalize D T valid τ) = eval {p | H.mem p} τ.val := by
  rw [eval_niceNormalize D T valid τ family H generic]
  apply ZFSet.ext
  intro x
  exact ⟨fun h => (ZFSet.mem_inter.1 h).1,
    fun h => ZFSet.mem_inter.2 ⟨h, subset h⟩⟩

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem niceNormalize_niceNameCode (D : NameDomain s)
    (closed : ∀ g σ, σ ∈ D.names → a.act s g σ ∈ D.names)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (terms : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (τ : D.names) (K : Subgroup G) (fixed : K ≤ a.stabilizer s τ.val) :
    NiceNameCode a s T K (niceNormalize D T valid τ).val := by
  apply (niceNameCode_iff a s _).2
  refine ⟨niceNormalize_subset D T valid τ, ?_⟩
  intro g hg
  change a.act s g (niceNormalize D T valid τ) = niceNormalize D T valid τ
  unfold niceNormalize
  rw [a.act_separationName s D closed, act_familySet a T valid terms]
  have env : a.actAssignment s D closed g (extend τ Fin.elim0) = extend τ Fin.elim0 := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    apply Subtype.ext
    exact fixed hg
  rw [env]

theorem niceNormalize_hs (D : NameDomain s)
    (closed : ∀ g σ, σ ∈ D.names → a.act s g σ ∈ D.names)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (terms : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (τ : D.names) (K : Subgroup G) (fixed : K ≤ a.stabilizer s τ.val)
    (F : Compression.RecursiveMaps.NormalSubgroupFamily G) (member : F.mem K)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ) :
    HereditarilySymmetric a s F (niceNormalize D T valid τ) :=
  niceNameCode_hs a s F member children
    (niceNormalize_niceNameCode a D closed T valid terms τ K fixed)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Upper Lower : Type u}
variable [PartialOrder Upper] [PartialOrder Lower] [OrderTop Lower]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (restriction : Upper →o Lower) (inclusion : Lower ↪o Upper)
variable (projection : CompleteProjection restriction inclusion)
variable (codes : ∀ p, s.encode (inclusion p) = t.encode p)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (upperCarrier : s.carrier ∈ M.sets) (upperOrder : s.conditionOrder ∈ M.sets)
variable (lowerCarrier : t.carrier ∈ M.sets) (lowerOrder : t.conditionOrder ∈ M.sets)
variable {J f : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName t z)
variable (tau : (M.nameDomain s).names)
variable (function : ZFSet.IsFunc J (M.groundPower s.carrier) f)
variable (selected : ∀ sigma A, ZFSet.pair sigma A ∈ f →
  A ⊆ M.ordinaryMembershipDecisions s.carrier s.conditionOrder sigma tau.val.val ∧
    A ⊆ t.carrier ∧ ∀ q ∈ t.carrier, ∃ p ∈ A, ∃ r ∈ t.carrier,
      ZFSet.pair r q ∈ t.conditionOrder ∧ ZFSet.pair r p ∈ t.conditionOrder)
variable (H : ConditionFilter Upper)
variable (upperGeneric : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (lowerGeneric : (projection.projectedFilter H).GenericFor (M.codedFamily t))
include codes pairing unions powers separation collection upperCarrier upperOrder lowerCarrier lowerOrder
  hJ function selected upperGeneric lowerGeneric

theorem crossStageMembershipName_eval_of_family :
    Name.eval {p | (projection.projectedFilter H).mem p}
      (Name.crossStageMembershipName s t inclusion J valid tau.val) =
      Name.eval {p | H.mem p} tau.val ∩
        Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) := by
  have terms (sigma : Name t) (member : sigma.val ∈ J) :
      Name.rename s inclusion sigma ∈ (M.nameDomain s).names := by
    change (Name.rename s inclusion sigma).val ∈ M.sets
    rw [Name.rename_val_of_encode s inclusion codes]
    exact M.transitive hJ member
  have decisions (sigma : Name t) (member : sigma.val ∈ J) : ∃ p : Lower,
      H.mem (inclusion p) ∧
        (Name.ForcesMem (inclusion p) (Name.rename s inclusion sigma) tau.val ∨
          ∀ q, q ≤ inclusion p → ¬ Name.ForcesMem q (Name.rename s inclusion sigma) tau.val) := by
    obtain ⟨A, entry, _⟩ := function.2 sigma.val member
    have groundA := ((M.mem_groundPower s.carrier A).1
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2).1
    obtain ⟨domain, bound, predense⟩ := selected sigma.val A entry
    obtain ⟨p, hp, inA⟩ := M.generic_meets_ground_predense t separation lowerCarrier lowerOrder
      (projection.projectedFilter H) lowerGeneric groundA bound predense
    let upperSigma : (M.nameDomain s).names := ⟨Name.rename s inclusion sigma, terms sigma member⟩
    have decisionEntry : s.encode (inclusion p) ∈
        M.ordinaryMembershipDecisions s.carrier s.conditionOrder upperSigma.val.val tau.val.val := by
      change s.encode (inclusion p) ∈ M.ordinaryMembershipDecisions s.carrier s.conditionOrder
        (Name.rename s inclusion sigma).val tau.val.val
      rw [codes p, Name.rename_val_of_encode s inclusion codes]
      exact domain inA
    exact ⟨p, hp, (M.ordinaryMembershipDecisions_entry s pairing unions powers separation collection
      upperCarrier upperOrder upperSigma tau (inclusion p)).1 decisionEntry⟩
  have topMember : H.mem (inclusion ⊤) := by
    obtain ⟨p, hp⟩ := (projection.projectedFilter H).nonempty
    exact (projection.projectedFilter H).upward hp le_top
  have atomicGeneric : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E member dense => upperGeneric E (Or.inl member) dense
  exact Name.eval_crossStageMembershipName_of_decisions s t inclusion J valid (M.nameDomain s)
    tau.val H atomicGeneric tau.property terms ⊤ topMember decisions

theorem crossStageMembershipName_eval_of_family_subset
    (subset : Name.eval {p | H.mem p} tau.val ⊆
      Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid)) :
    Name.eval {p | (projection.projectedFilter H).mem p}
      (Name.crossStageMembershipName s t inclusion J valid tau.val) =
      Name.eval {p | H.mem p} tau.val := by
  rw [M.crossStageMembershipName_eval_of_family s t restriction inclusion projection codes
    pairing unions powers separation collection upperCarrier upperOrder lowerCarrier lowerOrder
    hJ valid tau function selected H upperGeneric lowerGeneric]
  apply ZFSet.ext
  intro x
  exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
    fun member => ZFSet.mem_inter.2 ⟨member, subset member⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

omit [OrderTop P] in
include pairing unions powers separation collection carrier order in
theorem ordinarySeparationName_mem {n : Nat} (φ : SetFormula (n + 1))
    (nameEnv : Assignment (M.nameDomain s) n) (τ : (M.nameDomain s).names) :
    (Name.separationName (M.nameDomain s) φ nameEnv τ.val).val ∈ M.sets := by
  let context := extend s.carrier (extend s.conditionOrder (fun i => (nameEnv i).val.val))
  let params : Fin 2 → Fin (n + 2) := extend 0 (extend 1 Fin.elim0)
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (fun i => (nameEnv i).property))
  apply M.separationName_mem s (M.nameDomain s) (fun _ h => h)
    pairing unions powers separation carrier order (ordinaryGroundPrimitives 0 1)
    φ params (fun i => i.succ.succ) context members rfl rfl
  · exact M.equalityMeaning_lifted s (M.nameDomain s) (fun _ h => h)
      pairing unions powers separation collection carrier order 0 1 _ rfl rfl
  · exact M.domainMeaning_liftedNames s pairing unions powers separation collection carrier 0 _ rfl
  · exact fun _ => rfl

include pairing unions powers separation collection carrier order in
theorem niceNormalize_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (τ : (M.nameDomain s).names) :
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈ M.sets := by
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT
    (M.transitive carrier (s.encode_mem ⊤)) valid
  exact M.ordinarySeparationName_mem s pairing unions powers separation collection carrier order
    (.mem 0 1) (extend τ Fin.elim0) ⟨Name.familySet ⊤ T valid, family⟩

theorem entry_niceNormalize {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (τ : (M.nameDomain s).names) (σ : Name s) (p : P) :
    Name.Entry σ (Name.niceNormalize (M.nameDomain s) T valid τ) p ↔
      σ.val ∈ T ∧ Name.ForcesMem p σ τ.val := by
  rw [Name.entry_niceNormalize]
  constructor
  · rintro ⟨member, _, forced⟩
    exact ⟨member, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨member, M.transitive hT member, forced⟩

include pairing unions powers separation collection carrier order in
theorem niceNormalize_spec {G : Type u} [Group G]
    (a : PosetAction G P) (t : Presentation G)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (terms : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (τ : (M.nameDomain s).names) (K : Subgroup G) (fixed : K ≤ a.stabilizer s τ.val)
    (F : NormalSubgroupFamily G) (member : F.mem K)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ) :
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈ M.sets ∧
    NiceNameCode a s T K (Name.niceNormalize (M.nameDomain s) T valid τ).val ∧
    HereditarilySymmetric a s F (Name.niceNormalize (M.nameDomain s) T valid τ) ∧
    ∀ (H : ConditionFilter P), H.GenericFor (formulaFamily (M.nameDomain s)) →
      Name.eval {p | H.mem p} (Name.niceNormalize (M.nameDomain s) T valid τ) =
        Name.eval {p | H.mem p} τ.val ∩ Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  have closed : ∀ g σ, σ ∈ (M.nameDomain s).names → a.act s g σ ∈ (M.nameDomain s).names :=
    fun g σ hσ => M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ
  have code := Name.niceNormalize_niceNameCode a (M.nameDomain s) closed T valid terms τ K fixed
  refine ⟨M.niceNormalize_mem s pairing unions powers separation collection carrier order hT valid τ,
    code, niceNameCode_hs a s F member children code, ?_⟩
  intro H generic
  exact Name.eval_niceNormalize (M.nameDomain s) T valid τ
    (M.familySet_mem s ⊤ pairing unions powers separation hT
      (M.transitive carrier (s.encode_mem ⊤)) valid) H generic

end PartitionPilot.Forcing.TransitiveGround

end OAI
