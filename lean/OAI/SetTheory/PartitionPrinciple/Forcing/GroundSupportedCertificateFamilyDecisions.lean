import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalSupportedCertificateFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (omega : ZFSet.omega ∈ M.sets)

noncomputable def supportedCertificateFamilyEnv (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) : Assignment (M.nameDomain s) 12 :=
  let check (x : ZFSet.{u}) (hx : x ∈ M.sets) : (M.nameDomain s).names :=
    ⟨Name.check s ⊤ x, M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx⟩
  let N := M.niceSupportNameCodes a s T K
  let hN := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  ![check k hk, check J hJ, check (M.groundPower b.carrier) (M.groundPower_mem powers nodes),
    check (M.groundSmallSubsets b.carrier ZFSet.omega)
      (M.groundSmallSubsets_mem powers separation nodes omega),
    check (M.groundRelations b.carrier N)
      (M.groundRelations_mem pairing unions powers separation nodes hN),
    check b.carrier nodes, check N hN, check nodeOrder hOrder,
    check (M.niceSupportRelation a s b T K)
      (M.niceSupportRelation_mem a s b T K t pairing unions powers separation collection
        carrier group nodes supports maps hT valid),
    ⟨Name.inputEvaluationName s J validJ,
      M.inputEvaluationName_mem s pairing unions powers separation collection carrier hJ validJ⟩,
    ⟨M.niceSupportEvaluationName a s T K,
      M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩,
    ⟨M.niceVisibilityEvaluationName a s b T K,
      M.niceVisibilityEvaluationName_mem a s b t K pairing unions powers separation collection
        carrier group nodes supports maps hT valid⟩]

theorem realize_supportedCertificateFamilyEnv (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P) :
    Realize ((M.nameDomain s).values {p | H.mem p}) supportedCertificateFamilyFormula
      (evalAssignment {p | H.mem p}
        (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
          carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ)) ↔
      k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H := by
  let env := M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
    carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ
  let extension : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have fields : evalAssignment {p | H.mem p} env =
      ![k, J, M.groundPower b.carrier, M.groundSmallSubsets b.carrier ZFSet.omega,
        M.groundRelations b.carrier (M.niceSupportNameCodes a s T K), b.carrier,
        M.niceSupportNameCodes a s T K, nodeOrder, M.niceSupportRelation a s b T K,
        Name.eval {p | H.mem p} (Name.inputEvaluationName s J validJ),
        Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K),
        Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K)] := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))))))))))) i
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · rfl
    · rfl
    · rfl
  have meaning := extension.realize_supportedCertificateFamilyFormula
    (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)
  rw [fields] at meaning
  change Realize extension.sets supportedCertificateFamilyFormula
    (evalAssignment {p | H.mem p} env) ↔ _
  rw [fields]
  exact meaning

theorem exists_forced_supportedCertificateFamily (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (selected : k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (p : P) (hp : H.mem p) :
    ∃ q, H.mem q ∧ q ≤ p ∧
      Forces (M.nameDomain s) supportedCertificateFamilyFormula
        (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
          carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) q := by
  let env := M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
    carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ
  have truth := (M.realize_supportedCertificateFamilyEnv a s t b T K pairing unions powers separation
    collection carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ H).2 selected
  obtain ⟨r, hr, forced⟩ := (forcing_truth (M.nameDomain s) H generic
    supportedCertificateFamilyFormula env).1 truth
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  exact ⟨q, hq, qp, forces_mono (M.nameDomain s) supportedCertificateFamilyFormula env forced qr⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)
private theorem actual_certificate (nodeOrder J k : ZFSet.{u})
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P) (z : Name s)
    (F B f : ZFSet.{u})
    (selected : k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (entry : ZFSet.pair z.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k) :
    SupportedEqualityCertificate b.carrier (M.niceSupportNameCodes a s T K) nodeOrder
      (M.niceSupportRelation a s b T K)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
      (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K))
      (Name.eval {p | H.mem p} z) F B f := by
  obtain ⟨_, _, _, _, value, evaluated, certificate⟩ :=
    (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 (selected entry)
  have equal := (Name.inputEvaluationName_entry s J validJ z H value).1 evaluated
  exact equal.2.symm ▸ certificate

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (omega : ZFSet.omega ∈ M.sets)

theorem forces_supportedCertificateFamily_profile (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (small : M.sets.Countable)
    (z : (M.nameDomain s).names) (F B f : ZFSet.{u})
    (q : P) (forced : Forces (M.nameDomain s) supportedCertificateFamilyFormula
      (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
        carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) q)
    (entry : ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k)
    (hF : F ∈ M.sets) : M.DecidesVisibilityProfile a s b K T F z.val q := by
  apply (M.forces_visibilityProfile_iff a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid small F hF z q).1
  apply (M.ordinaryForces_iff_all_generics s small carrier visibilityProfileFormula
    (M.visibilityProfileEnv a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid F hF z) q).2
  intro H hq generic
  have truth := forces_sound (M.nameDomain s) H generic supportedCertificateFamilyFormula
    (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
      carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) hq forced
  have selected := (M.realize_supportedCertificateFamilyEnv a s t b T K pairing unions powers
    separation collection carrier group nodes supports maps hT valid omega nodeOrder J k
    hOrder hJ hk validJ H).1 truth
  have certificate := actual_certificate M a s b T K nodeOrder J k validJ H z.val F B f selected entry
  apply (M.realize_visibilityProfileEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid F hF z H).2
  intro v
  exact certificate.2.2.2.2.1 (b.encode v)
    (Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v)))
    ((M.niceVisibilityEvaluationName_entry a s b T K H v _).2 rfl) (b.encode_mem v)

theorem forces_supportedCertificateFamily_equality (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (small : M.sets.Countable)
    (z : (M.nameDomain s).names) (F B f : ZFSet.{u})
    (q : P) (forced : Forces (M.nameDomain s) supportedCertificateFamilyFormula
      (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
        carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) q)
    (entry : ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k)
    (v : ZFSet.{u}) (hv : v ∈ B) (tau : Name s)
    (ht : tau.val ∈ M.niceSupportNameCodes a s T K)
    (selectedEntry : ZFSet.pair v tau.val ∈ f) : Name.ForcesEq q z.val tau := by
  let named : (M.nameDomain s).names :=
    ⟨tau, ((M.mem_niceSupportNameCodes a s T K tau.val).1 ht).1⟩
  change Forces (M.nameDomain s) (.equal 0 1 : SetFormula 2) ![z, named] q
  apply (M.ordinaryForces_iff_all_generics s small carrier (.equal 0 1) ![z, named] q).2
  intro H hq generic
  have truth := forces_sound (M.nameDomain s) H generic supportedCertificateFamilyFormula
    (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
      carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) hq forced
  have selected := (M.realize_supportedCertificateFamilyEnv a s t b T K pairing unions powers
    separation collection carrier group nodes supports maps hT valid omega nodeOrder J k
    hOrder hJ hk validJ H).1 truth
  have certificate := actual_certificate M a s b T K nodeOrder J k validJ H z.val F B f selected entry
  have result := certificate.2.2.2.2.2 v hv tau.val ht selectedEntry
  exact ((M.niceSupportEvaluationName_entry a s T K tau ht H _).1 result.2).symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
