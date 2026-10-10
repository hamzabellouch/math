import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFamilyValueUnions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

noncomputable def niceSupportNameCodes : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun i => M.niceNameCandidates a s T (K i)))

theorem mem_niceSupportNameCodes (z : ZFSet.{u}) :
    z ∈ M.niceSupportNameCodes a s T K ↔
      z ∈ M.sets ∧ ∃ i, NiceNameCode a s T (K i) z := by
  rw [niceSupportNameCodes, familyCodeGraph_valueUnion_mem_iff]
  constructor
  · rintro ⟨i, hi⟩
    have code := (M.mem_niceNameCandidates a s T (K i) z).1 hi
    exact ⟨code.1, i, code.2⟩
  · rintro ⟨ground, i, code⟩
    exact ⟨i, (M.mem_niceNameCandidates a s T (K i) z).2 ⟨ground, code⟩⟩

theorem niceSupportNameCodes_valid :
    ∀ z ∈ M.niceSupportNameCodes a s T K, IsName s z := by
  intro z member
  obtain ⟨_, i, code⟩ := (M.mem_niceSupportNameCodes a s T K z).1 member
  exact niceNameCode_isName a s code

theorem niceSupportNameCodes_hs (F : NormalSubgroupFamily G)
    (basis : ∀ i, F.mem (K i))
    (children : ∀ tau : Name s, tau.val ∈ T → HereditarilySymmetric a s F tau)
    (tau : Name s) (member : tau.val ∈ M.niceSupportNameCodes a s T K) :
    HereditarilySymmetric a s F tau := by
  obtain ⟨_, i, code⟩ := (M.mem_niceSupportNameCodes a s T K tau.val).1 member
  exact niceNameCode_hs a s F (basis i) children code

noncomputable def niceSupportRelation : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i tau, z = ZFSet.pair (b.encode i) tau ∧
    tau ∈ M.niceNameCandidates a s T (K i))
    (ZFSet.prod b.carrier (M.niceSupportNameCodes a s T K))

theorem pair_mem_niceSupportRelation (i : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode i) tau ∈ M.niceSupportRelation a s b T K ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K i) tau := by
  rw [niceSupportRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, sigma, eq, candidate⟩
    obtain ⟨keys, rfl⟩ := ZFSet.pair_inj.1 eq
    have same := b.injective keys
    subst j
    exact (M.mem_niceNameCandidates a s T (K i) tau).1 candidate
  · intro code
    exact ⟨ZFSet.pair_mem_prod.2 ⟨b.encode_mem i,
      (M.mem_niceSupportNameCodes a s T K tau).2 ⟨code.1, i, code.2⟩⟩,
      i, tau, rfl, (M.mem_niceNameCandidates a s T (K i) tau).2 code⟩

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
include b t pairing unions powers separation collection carrier group nodes supports maps hT valid

theorem niceSupportNameCodes_mem : M.niceSupportNameCodes a s T K ∈ M.sets := by
  have whole := M.niceNameCandidateGraph_mem a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have domain : ZFSet.range b.encode = b.carrier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    exact (b.mem_carrier z).symm
  exact M.union_mem unions (M.familyCodeGraph_valueRange_mem unions separation b.encode
    (fun i => M.niceNameCandidates a s T (K i)) (domain.symm ▸ nodes) whole)

theorem niceSupportRelation_mem : M.niceSupportRelation a s b T K ∈ M.sets := by
  let graph := M.niceNameCandidateGraph a s b T K
  have hgraph := M.niceNameCandidateGraph_mem a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have hNames := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  let phi : SetFormula 2 := ex (ex (ex (.conj (orderedPairFormula 3 2 1)
    (.conj (pairMembershipFormula 2 0 4) (.mem 1 0)))))
  have meaning (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets phi (extend z (extend graph Fin.elim0)) ↔
        ∃ i tau, z = ZFSet.pair (b.encode i) tau ∧
          tau ∈ M.niceNameCandidates a s T (K i) := by
    simp only [phi, realize_ex]
    constructor
    · rintro ⟨v, hv, tau, htau, values, hvalues, shape, entry, member⟩
      have pair := (M.realize_orderedPairFormula pairing 3 2 1 _ hz hv htau).1 shape
      have edge : ZFSet.pair v values ∈ graph :=
        (M.realize_pairMembershipFormula pairing 2 0 4 _ hv hvalues hgraph).1 entry
      obtain ⟨i, eq⟩ := (M.mem_niceNameCandidateGraph a s b T K _).1 edge
      have parts := ZFSet.pair_inj.1 eq
      exact ⟨i, tau, pair.trans (congrArg (fun w => ZFSet.pair w tau) parts.1),
        parts.2 ▸ member⟩
    · rintro ⟨i, tau, shape, member⟩
      have hi := M.transitive nodes (b.encode_mem i)
      have hvalues := M.niceNameCandidates_mem a s t b K pairing unions powers separation
        collection carrier group supports maps hT valid i hi
      have htau := M.transitive hvalues member
      refine ⟨b.encode i, hi, tau, htau, M.niceNameCandidates a s T (K i), hvalues, ?_, ?_, member⟩
      · exact (M.realize_orderedPairFormula pairing 3 2 1 _ hz hi htau).2 shape
      · exact (M.realize_pairMembershipFormula pairing 2 0 4 _ hi hvalues hgraph).2
          ((M.pair_mem_niceNameCandidateGraph a s b T K i _).2 rfl)
  have selected := M.separation_mem separation phi (extend graph Fin.elim0)
    (Fin.cases hgraph (fun j => Fin.elim0 j)) (M.prod_mem pairing unions powers separation nodes hNames)
  have equal : ZFSet.sep (fun z => Realize M.sets phi (extend z (extend graph Fin.elim0)))
      (ZFSet.prod b.carrier (M.niceSupportNameCodes a s T K)) = M.niceSupportRelation a s b T K := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, niceSupportRelation, ZFSet.mem_sep]
    exact and_congr_right (fun member => meaning z
      (M.transitive (M.prod_mem pairing unions powers separation nodes hNames) member))
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder I] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (d : PosetAction G I)
variable (base : I) (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k)

theorem niceSupportNameCodes_principal_iff (T : ZFSet.{u})
    (children : ∀ tau : Name s, tau.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau)
    (tau : Name s) :
    tau.val ∈ M.niceSupportNameCodes a s T d.principalFix ↔
      tau.val ∈ M.sets ∧ tau.val ⊆ ZFSet.prod T s.carrier ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed) tau := by
  constructor
  · intro member
    obtain ⟨ground, i, code⟩ := (M.mem_niceSupportNameCodes a s T d.principalFix tau.val).1 member
    exact ⟨ground, (niceNameCode_iff a s tau).1 code |>.1,
      M.niceSupportNameCodes_hs a s T d.principalFix (d.principalSupportFamily base directed)
        (fun i => ⟨i, le_refl _⟩) children tau member⟩
  · rintro ⟨ground, subset, symmetric⟩
    obtain ⟨i, fixed⟩ := (d.principalSupportFamily_basis base directed _).1 symmetric.symmetric
    exact (M.mem_niceSupportNameCodes a s T d.principalFix tau.val).2
      ⟨ground, i, (niceNameCode_iff a s tau).2 ⟨subset, fixed⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
