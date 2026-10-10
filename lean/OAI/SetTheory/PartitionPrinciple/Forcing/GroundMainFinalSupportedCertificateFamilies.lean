import OAI.SetTheory.PartitionPrinciple.Definability.SupportedCertificateFamilyFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalDecidedVisibility

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def supportedEqualityCertificateBound (nodes N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (M.groundPower nodes)
    (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes N))

theorem mem_supportedEqualityCertificateBound (nodes N F B f : ZFSet.{u}) :
    ZFSet.pair F (ZFSet.pair B f) ∈ M.supportedEqualityCertificateBound nodes N ↔
      (F ∈ M.sets ∧ F ⊆ nodes) ∧
      (B ∈ M.sets ∧ B ⊆ nodes ∧ M.groundEmbeddable B ZFSet.omega) ∧
      (f ∈ M.sets ∧ f ⊆ ZFSet.prod nodes N) := by
  rw [supportedEqualityCertificateBound, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod,
    M.mem_groundPower, M.mem_groundSmallSubsets, M.mem_groundRelations]

theorem supportedEqualityCertificateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.supportedEqualityCertificateBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.groundPower_mem powers hNodes)
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hN))

theorem supportedEqualityCertificate_mem {nodes N F B f : ZFSet.{u}}
    (hF : F ∈ M.sets) (profile : F ⊆ nodes) (hB : B ∈ M.sets)
    (basis : B ⊆ F) (small : M.groundEmbeddable B ZFSet.omega)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc B N f) :
    ZFSet.pair F (ZFSet.pair B f) ∈ M.supportedEqualityCertificateBound nodes N := by
  refine (M.mem_supportedEqualityCertificateBound nodes N F B f).2
    ⟨⟨hF, profile⟩, ⟨hB, fun _ member => profile (basis member), small⟩, hf, ?_⟩
  intro entry member
  obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
  exact ZFSet.pair_mem_prod.2 ⟨profile (basis hv), htau⟩

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation I) (K : I → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

noncomputable def supportedEqualitySequenceEnv (B f : ZFSet.{u})
    (hB : B ∈ M.sets) (hf : f ∈ M.sets) (z : (M.nameDomain s).names) :
    Assignment (M.nameDomain s) 6 :=
  let check (x : ZFSet.{u}) (hx : x ∈ M.sets) : (M.nameDomain s).names :=
    ⟨Name.check s ⊤ x, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx⟩
  ![check B hB,
    check (M.niceSupportNameCodes a s T K)
      (M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation collection
        carrier group nodes supports maps hT valid),
    check f hf,
    check (M.niceSupportRelation a s b T K)
      (M.niceSupportRelation_mem a s b T K t pairing unions powers separation collection
        carrier group nodes supports maps hT valid),
    ⟨M.niceSupportEvaluationName a s T K,
      M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩,
    z]

theorem realize_supportedEqualitySequenceEnv (B f : ZFSet.{u})
    (hB : B ∈ M.sets) (hf : f ∈ M.sets) (z : (M.nameDomain s).names)
    (H : ConditionFilter P) :
    Realize ((M.nameDomain s).values {p | H.mem p}) supportedEqualitySequenceFormula
      (evalAssignment {p | H.mem p}
        (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
          carrier group nodes supports maps hT valid B f hB hf z)) ↔
      ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f ∧
      ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
        ZFSet.pair v tau.val ∈ f →
        ZFSet.pair v tau.val ∈ M.niceSupportRelation a s b T K ∧
        Name.eval {p | H.mem p} tau = Name.eval {p | H.mem p} z.val := by
  let env := M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid B f hB hf z
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have fields : evalAssignment {p | H.mem p} env =
      ![B, M.niceSupportNameCodes a s T K, f, M.niceSupportRelation a s b T K,
        Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K),
        Name.eval {p | H.mem p} z.val] := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))) i
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
  have meaning := N.realize_supportedEqualitySequenceFormula
    (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)
  rw [fields] at meaning
  change Realize N.sets supportedEqualitySequenceFormula (evalAssignment {p | H.mem p} env) ↔ _
  rw [fields, meaning]
  constructor
  · rintro ⟨function, allEntries⟩
    refine ⟨function, ?_⟩
    intro v hv tau ht entry
    have result := allEntries v hv tau.val ht entry
    exact ⟨result.1, (M.niceSupportEvaluationName_entry a s T K tau ht H _).1 result.2⟩
  · rintro ⟨function, allEntries⟩
    refine ⟨function, ?_⟩
    intro v hv code hc entry
    let tau : Name s := ⟨code, M.niceSupportNameCodes_valid a s T K code hc⟩
    have result := allEntries v hv tau hc entry
    exact ⟨result.1, (M.niceSupportEvaluationName_entry a s T K tau hc H _).2 result.2⟩

theorem forces_supportedEqualitySequence_entry (small : M.sets.Countable)
    (B f : ZFSet.{u}) (hB : B ∈ M.sets) (hf : f ∈ M.sets)
    (z : (M.nameDomain s).names) (p : P)
    (forced : Forces (M.nameDomain s) supportedEqualitySequenceFormula
      (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
        carrier group nodes supports maps hT valid B f hB hf z) p)
    (v : ZFSet.{u}) (hv : v ∈ B) (tau : Name s)
    (ht : tau.val ∈ M.niceSupportNameCodes a s T K) (entry : ZFSet.pair v tau.val ∈ f) :
    Name.ForcesEq p z.val tau := by
  let named : (M.nameDomain s).names :=
    ⟨tau, ((M.mem_niceSupportNameCodes a s T K tau.val).1 ht).1⟩
  change Forces (M.nameDomain s) (.equal 0 1 : SetFormula 2) ![z, named] p
  apply (M.ordinaryForces_iff_all_generics s small carrier (.equal 0 1) ![z, named] p).2
  intro H hp generic
  have truth := forces_sound (M.nameDomain s) H generic supportedEqualitySequenceFormula
    (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid B f hB hf z) hp forced
  have result := (M.realize_supportedEqualitySequenceEnv a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid B f hB hf z H).1 truth
  exact (result.2 v hv tau ht entry).2.symm

theorem exists_forced_supportedEqualitySequence (small : M.sets.Countable)
    (B f : ZFSet.{u}) (hB : B ∈ M.sets) (hf : f ∈ M.sets)
    (z : (M.nameDomain s).names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (function : ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f)
    (meaning : ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
      ZFSet.pair v tau.val ∈ f →
      ZFSet.pair v tau.val ∈ M.niceSupportRelation a s b T K ∧
      Name.eval {p | H.mem p} tau = Name.eval {p | H.mem p} z.val)
    (p : P) (hp : H.mem p) :
    ∃ q, H.mem q ∧ q ≤ p ∧
      Forces (M.nameDomain s) supportedEqualitySequenceFormula
        (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
          carrier group nodes supports maps hT valid B f hB hf z) q ∧
      ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
        ZFSet.pair v tau.val ∈ f →
        ZFSet.pair v tau.val ∈ M.niceSupportRelation a s b T K ∧ Name.ForcesEq q z.val tau := by
  let env := M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid B f hB hf z
  have truth := (M.realize_supportedEqualitySequenceEnv a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid B f hB hf z H).2 ⟨function, meaning⟩
  obtain ⟨r, hr, forced⟩ := (forcing_truth (M.nameDomain s) H generic
    supportedEqualitySequenceFormula env).1 truth
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  have forcedQ := forces_mono (M.nameDomain s) supportedEqualitySequenceFormula env forced qr
  refine ⟨q, hq, qp, forcedQ, ?_⟩
  intro v hv tau ht entry
  exact ⟨(meaning v hv tau ht entry).1,
    M.forces_supportedEqualitySequence_entry a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid small B f hB hf z q forcedQ v hv tau ht entry⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)

noncomputable def supportedCertificateFamilyRelation
    (nodeOrder J : ZFSet.{u}) (validJ : ∀ z ∈ J, IsName s z)
    (H : ConditionFilter P) : ZFSet.{u} :=
  supportedCertificateRelation J (M.groundPower b.carrier)
    (M.groundSmallSubsets b.carrier ZFSet.omega)
    (M.groundRelations b.carrier (M.niceSupportNameCodes a s T K)) b.carrier
    (M.niceSupportNameCodes a s T K) nodeOrder (M.niceSupportRelation a s b T K)
    (Name.eval {p | H.mem p} (Name.inputEvaluationName s J validJ))
    (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
    (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K))

theorem supportedCertificateFamilyRelation_mem_ordinary (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    {nodeOrder J : ZFSet.{u}} (hNodeOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H ∈
      (M.ordinaryExtension s H).sets := by
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation
    collection carrier H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection
    carrier order infinite H generic
  have hN := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have hInput := M.inputEvaluationName_mem s pairing unions powers separation collection carrier hJ validJ
  have hNice := M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have hVisibility := M.niceVisibilityEvaluationName_mem a s b t K pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  exact (M.ordinaryExtension s H).supportedCertificateRelation_mem
    zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1 zf.2.1
    (includes hJ) (includes (M.groundPower_mem powers nodes))
    (includes (M.groundSmallSubsets_mem powers separation nodes (M.omega_mem separation infinite)))
    (includes (M.groundRelations_mem pairing unions powers separation nodes hN))
    (includes nodes) (includes hN) (includes hNodeOrder)
    (includes (M.niceSupportRelation_mem a s b T K t pairing unions powers separation
      collection carrier group nodes supports maps hT valid))
    ⟨⟨_, hInput⟩, rfl⟩ ⟨⟨_, hNice⟩, rfl⟩ ⟨⟨_, hVisibility⟩, rfl⟩

end TransitiveGround

namespace TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)

theorem supportedCertificateFamily_groundData (nodeOrder J : ZFSet.{u})
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P)
    (j F B f : ZFSet.{u})
    (member : ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈
      M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H) :
    j ∈ J ∧ F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
      M.groundEmbeddable B ZFSet.omega ∧ F ⊆ b.carrier ∧ B ⊆ F ∧
      (∀ v ∈ F, ∃ w ∈ B, ZFSet.pair w v ∈ nodeOrder) ∧
      ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f ∧
      ∀ v ∈ B, ∀ tau ∈ M.niceSupportNameCodes a s T K,
        ZFSet.pair v tau ∈ f → ZFSet.pair v tau ∈ M.niceSupportRelation a s b T K := by
  obtain ⟨hj, hF, hB, hf, value, _, certificate⟩ :=
    (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 member
  have small := (M.mem_groundSmallSubsets b.carrier ZFSet.omega B).1 hB
  exact ⟨hj, ((M.mem_groundPower b.carrier F).1 hF).1, small.1,
    ((M.mem_groundRelations b.carrier (M.niceSupportNameCodes a s T K) f).1 hf).1,
    small.2.2, certificate.1, certificate.2.1, certificate.2.2.1,
    certificate.2.2.2.1, fun v hv tau ht edge => (certificate.2.2.2.2.2 v hv tau ht edge).1⟩

end TransitiveGround

namespace GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_supportedEqualityBasis
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (z : (M.nameDomain s).names)
      (_hs : HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z.val)
      (_subset : Name.eval {p | H.mem p} z.val ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
      ∃ ground : F ∈ M.sets,
        MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
        ∃ (B : ZFSet.{u}) (hB : B ∈ M.sets),
          M.groundEmbeddable B ZFSet.omega ∧ B ⊆ F ∧
          (∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ geometry.order) ∧
          ∃ (f : ZFSet.{u}) (hf : f ∈ M.sets),
            ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f ∧
            ∃ q, H.mem q ∧ q ≤ p ∧
              Forces (M.nameDomain s) visibilityProfileFormula
                (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
                  carrier geometry.actors_ground geometry.carrier_ground
                  (geometry.decoded_supportBasis_ground pairing unions powers separation)
                  maps hT valid F ground z) q ∧
              M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
              Forces (M.nameDomain s) supportedEqualitySequenceFormula
                (M.supportedEqualitySequenceEnv a s t b d.principalFix
                  pairing unions powers separation collection carrier geometry.actors_ground
                  geometry.carrier_ground
                  (geometry.decoded_supportBasis_ground pairing unions powers separation)
                  maps hT valid B f hB hf z) q ∧
              ∀ (v : SetMembers geometry.carrier), b.encode v ∈ B →
                ∀ τ : Name s, ZFSet.pair (b.encode v) τ.val ∈ f →
                  τ.val ∈ M.sets ∧ τ.val ⊆ ZFSet.prod T s.carrier ∧
                  HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ ∧
                  d.principalFix v ≤ a.stabilizer s τ ∧ Name.ForcesEq q z.val τ := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent z hs subset p hp
  let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  obtain ⟨ground, filter, B, hB, smallB, contained, coinitial, q₀, hq₀, q₀p, profile, _⟩ :=
    fulfilled.exists_decided_visibilityProfile s collection infinite choice carrier order small
      closed smallD irreflexive a maps T hT valid terms children H genericCoded genericFormula
      descent z hs subset p hp
  have inNodes : B ⊆ b.carrier := fun _ member => filter.subset (contained member)
  have visible : ∀ v : SetMembers geometry.carrier, b.encode v ∈ B →
      Name.eval {p | H.mem p} z.val ∈
        Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
    intro v hv
    exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).1 (contained hv)
  obtain ⟨f, hf, function, selected⟩ := M.exists_ground_supportedEqualityChoice a s t b T
    d.principalFix pairing unions powers separation collection infinite choice carrier order
    geometry.actors_ground geometry.carrier_ground supports maps hT valid small closed H
    genericCoded genericFormula hB smallB inNodes z visible
  have meaning : ∀ raw ∈ B, ∀ τ : Name s,
      τ.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair raw τ.val ∈ f →
      ZFSet.pair raw τ.val ∈ M.niceSupportRelation a s b T d.principalFix ∧
      Name.eval {p | H.mem p} τ = Name.eval {p | H.mem p} z.val := by
    intro raw _ τ ht entry
    have facts := (pair_mem_supportedEqualityRelation B _ _ _ _ raw τ.val).1 (selected entry)
    exact ⟨facts.2.2.1,
      (M.niceSupportEvaluationName_entry a s T d.principalFix τ ht H _).1 facts.2.2.2⟩
  obtain ⟨q, hq, qq₀, forced, entries⟩ := M.exists_forced_supportedEqualitySequence a s t b
    d.principalFix pairing unions powers separation collection carrier geometry.actors_ground
    geometry.carrier_ground supports maps hT valid small B f hB hf z H genericFormula
    function meaning q₀ hq₀
  have profileQ := forces_mono (M.nameDomain s) visibilityProfileFormula _ profile qq₀
  have decisions := (M.forces_visibilityProfile_iff a s t b d.principalFix pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps
    hT valid small F ground z q).1 profileQ
  refine ⟨ground, filter, B, hB, smallB, contained, coinitial, f, hf, function,
    q, hq, le_trans qq₀ q₀p, profileQ, decisions, forced, ?_⟩
  intro v hv τ entry
  have member := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  have certificate := entries (b.encode v) hv τ member entry
  have code := (M.pair_mem_niceSupportRelation a s b T d.principalFix v τ.val).1 certificate.1
  have nice := (niceNameCode_iff a s τ).1 code.2
  exact ⟨code.1, nice.1, niceNameCode_principal_hs a s d ⊥ v directed children code.2,
    nice.2, certificate.2⟩

theorem exists_supportedCertificateFamily
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)),
      ∃ k ∈ M.sets,
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent
    J hJ validJ smallJ hs subsets
  let codes := M.niceSupportNameCodes a s T d.principalFix
  let bound := M.supportedEqualityCertificateBound b.carrier codes
  let relation := M.supportedCertificateFamilyRelation a s b T d.principalFix
    geometry.order J validJ H
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have codesGround := M.niceSupportNameCodes_mem a s b T d.principalFix t pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
  have boundGround := M.supportedEqualityCertificateBound_mem pairing unions powers separation
    geometry.carrier_ground codesGround (M.omega_mem separation infinite)
  have relationGround := M.supportedCertificateFamilyRelation_mem_ordinary a s b T d.principalFix
    t pairing unions powers separation collection infinite carrier order geometry.actors_ground
    geometry.carrier_ground supports maps hT valid geometry.order_ground hJ validJ H genericFormula
  have total : ∀ raw ∈ J, ∃ certificate ∈ bound, ZFSet.pair raw certificate ∈ relation := by
    intro raw member
    let z : (M.nameDomain s).names := ⟨⟨raw, validJ raw member⟩, M.transitive hJ member⟩
    let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
    obtain ⟨hF, filter, B, hB, smallB, contained, coinitial, f, hf, function,
        q, hq, _, _, _, forced, _⟩ :=
      fulfilled.exists_supportedEqualityBasis s collection infinite choice carrier order small
        closed smallD irreflexive a maps T hT valid terms children H genericCoded genericFormula
        descent z (hs z.val member) (subsets z.val member) ⊤ H.top_mem
    have certificateBound := M.supportedEqualityCertificate_mem hF filter.subset hB contained
      smallB hf function
    refine ⟨ZFSet.pair F (ZFSet.pair B f), certificateBound, ?_⟩
    change ZFSet.pair raw (ZFSet.pair F (ZFSet.pair B f)) ∈ supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _
    apply (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
    have boundFields := (M.mem_supportedEqualityCertificateBound b.carrier codes F B f).1 certificateBound
    refine ⟨member, (M.mem_groundPower _ _).2 boundFields.1,
      (M.mem_groundSmallSubsets _ _ _).2 boundFields.2.1,
      (M.mem_groundRelations _ _ _).2 boundFields.2.2,
      Name.eval {p | H.mem p} z.val,
      (Name.inputEvaluationName_entry s J validJ z.val H _).2 ⟨member, rfl⟩,
      filter.subset, contained, coinitial, function, ?_, ?_⟩
    · intro rawNode V entry inNodes
      obtain ⟨v, rfl⟩ := (b.mem_carrier rawNode).1 inNodes
      have equal := (M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v V).1 entry
      rw [← equal]
      exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).symm
    · have truth := forces_sound (M.nameDomain s) H genericFormula supportedEqualitySequenceFormula
        (M.supportedEqualitySequenceEnv a s t b d.principalFix pairing unions powers separation
          collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
          B f hB hf z) hq forced
      have meaning := (M.realize_supportedEqualitySequenceEnv a s t b d.principalFix pairing unions
        powers separation collection carrier geometry.actors_ground geometry.carrier_ground supports
        maps hT valid B f hB hf z H).1 truth
      intro v hv rawName inCodes entry
      let tau : Name s := ⟨rawName, M.niceSupportNameCodes_valid a s T d.principalFix rawName inCodes⟩
      have result := meaning.2 v hv tau inCodes entry
      exact ⟨result.1, (M.niceSupportEvaluationName_entry a s T d.principalFix tau inCodes H _).2 result.2⟩
  let extension := M.ordinaryExtension s H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  obtain ⟨k, hk, function, selected⟩ := extension.uniformize_relation zf.1.2.2.2.1 zf.1.2.2.2.2.1
    zf.1.2.2.2.2.2.1 zf.2.1 choiceN (includes hJ) (includes boundGround) relationGround total
  have ground := M.ordinaryExtension_countableDomainFunction_mem s pairing unions powers separation
    collection infinite choice carrier order small hJ boundGround smallJ closed H genericCoded
    genericFormula hk function
  exact ⟨k, ground, function, selected⟩

end GroundMainPrefix.FinalSupportFulfillment

end PartitionPilot.Forcing

end OAI
