import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPrincipalSupportZF
import OAI.SetTheory.PartitionPrinciple.Forcing.NameFamilySetTransport

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem niceNameCandidates_valid (T : ZFSet.{u}) (K : Subgroup G) :
    ∀ z ∈ M.niceNameCandidates a s T K, IsName s z := by
  intro z hz
  exact niceNameCode_isName a s ((M.mem_niceNameCandidates a s T K z).1 hz).2

variable [OrderTop P]

noncomputable def niceVisibilityName (T : ZFSet.{u}) (K : Subgroup G) : Name s :=
  Name.familySet ⊤ (M.niceNameCandidates a s T K) (M.niceNameCandidates_valid a s T K)

theorem niceVisibilityName_code (T : ZFSet.{u}) (K : Subgroup G) :
    (M.niceVisibilityName a s T K).val =
      ZFSet.prod (M.niceNameCandidates a s T K) {s.encode ⊤} :=
  Name.familySet_code ⊤ _ _

theorem entry_niceVisibilityName (T : ZFSet.{u}) (K : Subgroup G)
    (τ : Name s) (p : P) :
    Name.Entry τ (M.niceVisibilityName a s T K) p ↔
      τ.val ∈ M.niceNameCandidates a s T K ∧ p = ⊤ :=
  Name.entry_familySet ⊤ _ _ τ p

theorem mem_eval_niceVisibilityName (T : ZFSet.{u}) (K : Subgroup G)
    (H : Set P) (top : ⊤ ∈ H) (x : ZFSet.{u}) :
    x ∈ Name.eval H (M.niceVisibilityName a s T K) ↔
      ∃ τ : Name s, τ.val ∈ M.niceNameCandidates a s T K ∧ Name.eval H τ = x :=
  Name.mem_eval_familySet H ⊤ top _ _ x

theorem niceVisibilityName_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (i : I) (hi : b.encode i ∈ M.sets) :
    (M.niceVisibilityName a s T (K i)).val ∈ M.sets :=
  M.familySet_mem s ⊤ pairing unions powers separation
    (M.niceNameCandidates_mem a s t b K pairing unions powers separation collection
      carrier group supports maps hT valid i hi)
    (M.transitive carrier (s.encode_mem ⊤)) _

theorem niceVisibilityName_support (T : ZFSet.{u}) (K : Subgroup G) :
    K ≤ a.stabilizer s (M.niceVisibilityName a s T K) := by
  apply Name.familySet_support a _ _ K
  intro τ hτ
  exact ((M.name_mem_niceNameCandidates a s T K τ).1 hτ).2.2

theorem niceVisibilityName_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (K : Subgroup G) (member : F.mem K)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (M.niceVisibilityName a s T K) := by
  refine HereditarilySymmetric.mk (F.upward member (M.niceVisibilityName_support a s T K)) ?_
  intro τ p entry
  have candidate := ((M.mem_niceNameCandidates a s T K τ.val).1
    ((M.entry_niceVisibilityName a s T K τ p).1 entry).1).2
  exact niceNameCode_hs a s F member children candidate

theorem niceVisibilityName_principal_hs {L : Type u} [PartialOrder L]
    (d : PosetAction G L) (base v : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z) (T : ZFSet.{u})
    (children : ∀ τ : Name s, τ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ) :
    HereditarilySymmetric a s (d.principalSupportFamily base directed)
      (M.niceVisibilityName a s T (d.principalFix v)) :=
  M.niceVisibilityName_hs a s (d.principalSupportFamily base directed)
    T (d.principalFix v) ⟨v, le_refl _⟩ children

theorem act_niceVisibilityName {L : Type u} [PartialOrder L]
    (t : Presentation G) (d : PosetAction G L)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}}
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (g : G) (v : L) :
    a.act s g (M.niceVisibilityName a s T (d.principalFix v)) =
      M.niceVisibilityName a s T (d.principalFix (d.iso g v)) := by
  apply Name.act_familySet_transport a
  exact M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation collection
    carrier maps closed d g v

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mix_mem_mixtureCandidates (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) (p : P) :
    (a.mix s K p τ).val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s τ) K := by
  apply (M.name_mem_niceNameCandidates a s _ K _).2
  exact ⟨M.mix_mem a s t pairing unions powers separation collection carrier order group maps K hK p τ ground,
    M.mix_subset_mixtureTermCodes a s τ ground K p, fun _ hg => a.mix_fixed s K p τ hg⟩

theorem mixture_candidate_data (F : NormalSubgroupFamily G) (K : Subgroup G)
    (member : F.mem K) (τ : Name s) (hs : HereditarilySymmetric a s F τ)
    (σ : Name s) (candidate : σ.val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s τ) K) :
    σ.val ∈ M.sets ∧ K ≤ a.stabilizer s σ ∧ HereditarilySymmetric a s F σ ∧
      Name.nameRank σ ≤ Name.nameRank τ := by
  have data := (M.name_mem_niceNameCandidates a s _ K σ).1 candidate
  refine ⟨data.1, data.2.2,
    niceNameCode_hs a s F member (M.mixtureTermCodes_hs a s F τ hs)
      ((niceNameCode_iff a s σ).2 data.2), ?_⟩
  change ZFSet.rank (Name.eval Set.univ σ) ≤ Name.nameRank τ
  rw [ZFSet.rank_le_iff]
  intro value memValue
  obtain ⟨ν, p, entry, _, rfl⟩ := (Name.mem_eval Set.univ σ value).1 memValue
  exact (Name.rank_eval_le Set.univ ν).trans_lt
    (M.mixtureTermCodes_rank a s τ ν (Name.entry_term_of_subset data.2.1 entry))

variable [OrderTop P]

theorem mixture_visibility_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) (i : I) (hi : b.encode i ∈ M.sets) :
    (M.niceVisibilityName a s (M.mixtureTermCodes a s τ) (K i)).val ∈ M.sets :=
  M.niceVisibilityName_mem a s t b K pairing unions powers separation collection carrier group supports maps
    (M.mixtureTermCodes_mem a s t pairing unions powers separation collection carrier group maps τ ground)
    (M.mixtureTermCodes_valid a s τ) i hi

theorem mixture_visibility_hs (F : NormalSubgroupFamily G) (K : Subgroup G)
    (member : F.mem K) (τ : Name s) (hs : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (M.niceVisibilityName a s (M.mixtureTermCodes a s τ) K) :=
  M.niceVisibilityName_hs a s F _ K member (M.mixtureTermCodes_hs a s F τ hs)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P I : Type u} [Group G]
variable [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation I) (K : I → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)

include pairing unions powers separation collection carrier order group indices supports maps in
theorem forcesMem_mixtureVisibility_of_dense
    (i : I) (x : Name s) (ground : x.val ∈ M.sets) (p₀ : P)
    (dense : DenseBelow p₀ {p | Name.ForcesEq p x (a.mix s (K i) p x)}) :
    Name.ForcesMem p₀ x (M.niceVisibilityName a s (M.mixtureTermCodes a s x) (K i)) := by
  have subgroup := M.supportBasis_fiber_mem t b K pairing separation group indices supports i
  intro q below
  obtain ⟨p, pq, equal⟩ := dense q below
  refine ⟨p, pq, a.mix s (K i) p x, ⊤, ?_, le_top, equal⟩
  apply (M.entry_niceVisibilityName a s (M.mixtureTermCodes a s x) (K i) _ ⊤).2
  exact ⟨M.mix_mem_mixtureCandidates a s t pairing unions powers separation collection
    carrier order group maps (K i) subgroup x ground p, rfl⟩

include pairing unions powers separation collection carrier order group indices supports maps in
theorem exists_mixtureCandidate_of_dense
    (F : NormalSubgroupFamily G) (i : I) (member : F.mem (K i))
    (x : Name s) (ground : x.val ∈ M.sets) (symmetric : HereditarilySymmetric a s F x)
    (p₀ : P) (dense : DenseBelow p₀ {p | Name.ForcesEq p x (a.mix s (K i) p x)})
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (active : H.mem p₀) :
    ∃ z : Name s,
      z.val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s x) (K i) ∧
      z.val ∈ M.sets ∧ HereditarilySymmetric a s F z ∧
      K i ≤ a.stabilizer s z ∧ Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  have visibility := M.mixture_visibility_mem a s t b K pairing unions powers separation
    collection carrier group supports maps x ground i (M.transitive indices (b.encode_mem i))
  have forced := M.forcesMem_mixtureVisibility_of_dense a s t b K pairing unions powers
    separation collection carrier order group indices supports maps i x ground p₀ dense
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE => generic E (Or.inl hE)
  have value := Name.forcesMem_sound (M.nameDomain s) H atomic ground visibility active forced
  obtain ⟨z, candidate, equal⟩ :=
    (M.mem_eval_niceVisibilityName a s (M.mixtureTermCodes a s x) (K i)
      {q | H.mem q} H.top_mem (Name.eval {q | H.mem q} x)).1 value
  obtain ⟨groundZ, support, hs, rank⟩ :=
    M.mixture_candidate_data a s F (K i) member x symmetric z candidate
  exact ⟨z, candidate, groundZ, hs, support, rank, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
