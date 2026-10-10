import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceSupportEvaluation
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundOrdinarySubmodelReflection

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def supportedEqualityRelation (B N R E value : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun entry => ∃ v ∈ B, ∃ tau ∈ N, entry = ZFSet.pair v tau ∧
    ZFSet.pair v tau ∈ R ∧ ZFSet.pair tau value ∈ E) (ZFSet.prod B N)

theorem pair_mem_supportedEqualityRelation (B N R E value v tau : ZFSet.{u}) :
    ZFSet.pair v tau ∈ supportedEqualityRelation B N R E value ↔
      v ∈ B ∧ tau ∈ N ∧ ZFSet.pair v tau ∈ R ∧ ZFSet.pair tau value ∈ E := by
  rw [supportedEqualityRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, w, hw, sigma, hsigma, equal, support, evaluated⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hw, hsigma, support, evaluated⟩
  · rintro ⟨hv, htau, support, evaluated⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, htau⟩, v, hv, tau, htau, rfl, support, evaluated⟩

namespace BoundedFormula
def supportedEqualityEntryFormula {n} (entry B N R E value : Fin n) : BoundedFormula n :=
  exMem B (exMem N.succ (.conj (orderedPairFormula entry.succ.succ 1 0)
    (.conj (pairMembershipFormula 1 0 R.succ.succ)
      (pairMembershipFormula 0 value.succ.succ E.succ.succ))))

theorem truth_supportedEqualityEntryFormula {n} (entry B N R E value : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (supportedEqualityEntryFormula entry B N R E value) env ↔
      ∃ v ∈ env B, ∃ tau ∈ env N, env entry = ZFSet.pair v tau ∧
        ZFSet.pair v tau ∈ env R ∧ ZFSet.pair tau (env value) ∈ env E := by
  simp only [supportedEqualityEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem supportedEqualityRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {B N R E value : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (hR : R ∈ M.sets) (hE : E ∈ M.sets) (hvalue : value ∈ M.sets) :
    supportedEqualityRelation B N R E value ∈ M.sets := by
  let params := extend B (extend N (extend R (extend E (extend value Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.supportedEqualityEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hB (Fin.cases hN (Fin.cases hR (Fin.cases hE (Fin.cases hvalue (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hB hN)
  have equal : ZFSet.sep (fun entry => BoundedFormula.Truth
      (BoundedFormula.supportedEqualityEntryFormula 0 1 2 3 4 5) (extend entry params))
      (ZFSet.prod B N) = supportedEqualityRelation B N R E value := by
    apply ZFSet.ext
    intro entry
    rw [ZFSet.mem_sep, supportedEqualityRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_supportedEqualityEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G) (H : ConditionFilter P)

theorem supportedEqualityRelation_entry (B value : ZFSet.{u}) (v : L) (tau : Name s) :
    ZFSet.pair (b.encode v) tau.val ∈ supportedEqualityRelation B
      (M.niceSupportNameCodes a s T K) (M.niceSupportRelation a s b T K)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K)) value ↔
      b.encode v ∈ B ∧ tau.val ∈ M.sets ∧ NiceNameCode a s T (K v) tau.val ∧
        Name.eval {p | H.mem p} tau = value := by
  rw [pair_mem_supportedEqualityRelation]
  constructor
  · rintro ⟨hv, htau, support, evaluated⟩
    have code := (M.pair_mem_niceSupportRelation a s b T K v tau.val).1 support
    exact ⟨hv, code.1, code.2, (M.niceSupportEvaluationName_entry a s T K tau htau H value).1 evaluated⟩
  · rintro ⟨hv, ground, code, evaluated⟩
    have member := (M.mem_niceSupportNameCodes a s T K tau.val).2 ⟨ground, v, code⟩
    exact ⟨hv, member, (M.pair_mem_niceSupportRelation a s b T K v tau.val).2 ⟨ground, code⟩,
      (M.niceSupportEvaluationName_entry a s T K tau member H value).2 evaluated⟩

theorem supportedEqualityRelation_total {B value : ZFSet.{u}}
    (subset : B ⊆ b.carrier)
    (visible : ∀ v : L, b.encode v ∈ B → value ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v))) :
    ∀ v ∈ B, ∃ tau ∈ M.niceSupportNameCodes a s T K,
      ZFSet.pair v tau ∈ supportedEqualityRelation B
        (M.niceSupportNameCodes a s T K) (M.niceSupportRelation a s b T K)
        (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K)) value := by
  intro raw member
  obtain ⟨v, rfl⟩ := (b.mem_carrier raw).1 (subset member)
  obtain ⟨tau, candidate, evaluated⟩ :=
    (M.mem_eval_niceVisibilityName a s T (K v) _ H.top_mem value).1 (visible v member)
  have code := (M.mem_niceNameCandidates a s T (K v) tau.val).1 candidate
  exact ⟨tau.val, (M.mem_niceSupportNameCodes a s T K tau.val).2 ⟨code.1, v, code.2⟩,
    (M.supportedEqualityRelation_entry a s b T K H B value v tau).2
      ⟨member, code.1, code.2, evaluated⟩⟩

theorem supportedEqualityRelation_mem_ordinary (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {B : ZFSet.{u}} (hB : B ∈ M.sets) (z : (M.nameDomain s).names) :
    supportedEqualityRelation B (M.niceSupportNameCodes a s T K) (M.niceSupportRelation a s b T K)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
      (Name.eval {p | H.mem p} z.val) ∈ (M.ordinaryExtension s H).sets := by
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  have nameGround := M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  exact (M.ordinaryExtension s H).supportedEqualityRelation_mem zf.1.2.2.2.1 zf.1.2.2.2.2.1
    zf.1.2.2.2.2.2.1 zf.2.1 (includes hB)
    (includes (M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation collection
      carrier group nodes supports maps hT valid))
    (includes (M.niceSupportRelation_mem a s b T K t pairing unions powers separation collection
      carrier group nodes supports maps hT valid))
    ⟨⟨_, nameGround⟩, rfl⟩ ⟨z, rfl⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def SupportedEqualityCertificate
    (nodes N order R niceEval visibilityEval value F B f : ZFSet.{u}) : Prop :=
  F ⊆ nodes ∧ B ⊆ F ∧
    (∀ v ∈ F, ∃ w ∈ B, ZFSet.pair w v ∈ order) ∧
    ZFSet.IsFunc B N f ∧
    (∀ v V, ZFSet.pair v V ∈ visibilityEval → v ∈ nodes →
      (value ∈ V ↔ v ∈ F)) ∧
    ∀ v ∈ B, ∀ tau ∈ N, ZFSet.pair v tau ∈ f →
      ZFSet.pair v tau ∈ R ∧ ZFSet.pair tau value ∈ niceEval

noncomputable def supportedCertificateRelation
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun entry => ∃ j ∈ J, ∃ F ∈ PF, ∃ B ∈ PB, ∃ f ∈ WF,
    entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∧
    ∃ value, ZFSet.pair j value ∈ inputEval ∧
      SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f)
    (ZFSet.prod J (ZFSet.prod PF (ZFSet.prod PB WF)))

theorem pair_mem_supportedCertificateRelation
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval j F B f : ZFSet.{u}) :
    ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈
        supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ↔
      j ∈ J ∧ F ∈ PF ∧ B ∈ PB ∧ f ∈ WF ∧
        ∃ value, ZFSet.pair j value ∈ inputEval ∧
          SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f := by
  rw [supportedCertificateRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j', hj, F', hF, B', hB, f', hf, equal, value, evaluated, certificate⟩
    have outer := ZFSet.pair_inj.1 equal
    have middle := ZFSet.pair_inj.1 outer.2
    have inner := ZFSet.pair_inj.1 middle.2
    cases outer.1
    cases middle.1
    cases inner.1
    cases inner.2
    exact ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
  · rintro ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hj, ZFSet.pair_mem_prod.2
      ⟨hF, ZFSet.pair_mem_prod.2 ⟨hB, hf⟩⟩⟩,
      j, hj, F, hF, B, hB, f, hf, rfl, value, evaluated, certificate⟩

theorem supportedCertificateRelation_subset
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval : ZFSet.{u}) :
    supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ⊆
      ZFSet.prod J (ZFSet.prod PF (ZFSet.prod PB WF)) := by
  intro entry member
  exact (ZFSet.mem_sep.1 member).1

end PartitionPilot.Forcing

end

end OAI
