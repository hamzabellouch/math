import OAI.SetTheory.PartitionPrinciple.Geometry.GroundHartogs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundUnionInterpretation

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_infinity_of_witness (U : Set ZFSet.{u})
    (transitive : ∀ x ∈ U, ∀ z ∈ x, z ∈ U)
    (I : ZFSet.{u}) (hI : I ∈ U) (empty : (∅ : ZFSet.{u}) ∈ I)
    (successor : ∀ x ∈ I, insert x x ∈ I) : Realize U infinity Fin.elim0 := by
  simp only [infinity, emptySetFormula, successorFormula, realize_ex, realize_imp, realize_disj, Realize]
  refine ⟨I, hI, ⟨∅, transitive I hI ∅ empty, empty, fun z _ => ZFSet.notMem_empty z⟩, ?_⟩
  intro x _ hx
  refine ⟨insert x x, transitive I hI _ (successor x hx), successor x hx, ?_⟩
  intro z _
  exact ⟨ZFSet.mem_insert_iff.1, ZFSet.mem_insert_iff.2⟩

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u})

theorem infinity_witness (infinite : Realize M.sets infinity Fin.elim0) :
    ∃ I ∈ M.sets, (∅ : ZFSet.{u}) ∈ I ∧ ∀ x ∈ I, insert x x ∈ I := by
  simp only [infinity, emptySetFormula, successorFormula, realize_ex, realize_imp, realize_disj, Realize] at infinite
  obtain ⟨I, hI, ⟨e, he, eI, empty⟩, successors⟩ := infinite
  have eqEmpty : e = ∅ := by
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => False.elim (empty z (M.transitive he hz) hz),
      fun hz => False.elim (ZFSet.notMem_empty z hz)⟩
  refine ⟨I, hI, eqEmpty ▸ eI, ?_⟩
  intro x hx
  have hxM := M.transitive hI hx
  obtain ⟨y, hy, yI, spec⟩ := successors x hxM hx
  have eq : y = insert x x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      exact (spec z (M.transitive hy hz)).1 hz
    · intro hz
      have hzM : z ∈ M.sets := by
        rcases hz with rfl | hz
        · exact hxM
        · exact M.transitive hxM hz
      exact (spec z hzM).2 hz
  exact eq ▸ yI

theorem symmetric_infinity {P G : Type u} [Group G] [PartialOrder P] [OrderTop P]
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) infinity Fin.elim0 := by
  obtain ⟨I, hI, empty, successor⟩ := M.infinity_witness infinite
  let D := a.symmetricDomain s (M.nameDomain s) F
  exact realize_infinity_of_witness (D.values {p | H.mem p})
    (fun _ hx _ hz => D.values_transitive _ hx hz) I
    (M.ground_subset_symmetric_values s a F pairing unions powers separation collection carrier H hI)
    empty successor

end PartitionPilot.Forcing.TransitiveGround

end



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetric_ZF (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    ZFRealization ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  have nonempty := a.symmetricDomain_nonempty s (M.nameDomain s) F
    (M.nameDomain_nonempty s ⟨s.carrier, carrier⟩)
  refine ⟨⟨realize_extensionality D _, realize_foundation D _, realize_emptySet D nonempty _,
    M.symmetric_pairing s a F pairing carrier H,
    M.symmetric_union s a F pairing unions powers separation carrier order H,
    M.symmetric_powerSet a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic,
    M.symmetric_infinity s a F pairing unions powers separation collection infinite carrier H⟩, ?_, ?_⟩
  · exact M.symmetric_separation a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic
  · exact M.symmetric_replacement a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic

theorem exists_ZF_interpretation (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      M.sets ⊆ (a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization ((a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) := by
  obtain ⟨H, hp, ground, ordinary, symmetric⟩ := M.exists_joint_generic s a F small carrier p
  exact ⟨H, hp, ground, ordinary, symmetric,
    M.ground_subset_symmetric_values s a F pairing unions powers separation collection carrier H,
    M.symmetric_ZF a s t b F K basis pairing unions powers separation collection infinite carrier order
      group indices supports maps H symmetric⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def restrictBelow (p : P) (τ : Name s) : Name s := selectName (fun _ q => q ≤ p) τ

theorem entry_restrictBelow (p : P) (τ σ : Name s) (q : P) :
    Entry σ (restrictBelow p τ) q ↔ ∃ r, Entry σ τ r ∧ q ≤ r ∧ q ≤ p :=
  entry_selectName _ τ σ q

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

def restrictionEntryFormula : SetFormula 5 :=
  ex (exConditions 4 (exConditions 5 (.conj (orderedPairFormula 3 2 1)
    (.conj (pairMembershipFormula 2 0 4)
      (.conj (pairMembershipFormula 1 0 7) (pairMembershipFormula 1 5 7))))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_restrictionEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets restrictionEntryFormula (extend z (extend τ.val (extend (s.encode p)
      (extend s.carrier (extend s.conditionOrder Fin.elim0))))) ↔
      z ∈ (Name.restrictBelow p τ).val := by
  let base := extend z (extend τ.val (extend (s.encode p) (extend s.carrier (extend s.conditionOrder Fin.elim0))))
  have hp := M.transitive carrier (s.encode_mem p)
  rw [restrictionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨q, rest⟩ := (M.realize_exConditions s 4 _ (extend x base) carrier rfl).1 rest
    obtain ⟨r, shape, old, qr, qp⟩ := (M.realize_exConditions s 5 _
      (extend (s.encode q) (extend x base)) carrier rfl).1 rest
    let e := extend (s.encode r) (extend (s.encode q) (extend x base))
    have hq := M.transitive carrier (s.encode_mem q)
    have hr := M.transitive carrier (s.encode_mem r)
    have raw := (M.realize_pairMembershipFormula pairing 2 0 4 e hx hr hτ).1 old
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ x r raw⟩
    have eq := (M.realize_orderedPairFormula pairing 3 2 1 e hz hx hq).1 shape
    change z = ZFSet.pair x (s.encode q) at eq
    rw [eq]
    exact (Name.entry_restrictBelow p τ σ q).2 ⟨r, raw,
      (M.realize_conditionLE s pairing carrier order 1 0 7 e q r rfl rfl rfl).1 qr,
      (M.realize_conditionLE s pairing carrier order 1 5 7 e q p rfl rfl rfl).1 qp⟩
  · intro member
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (Name.restrictBelow p τ) member
    have entry : Name.Entry σ (Name.restrictBelow p τ) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (Name.restrictBelow p τ).val
      rwa [← eq]
    obtain ⟨r, old, qr, qp⟩ := (Name.entry_restrictBelow p τ σ q).1 entry
    have hσ := (M.nameDomain s).children hτ old
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 4 _ (extend σ.val base) carrier rfl).2
    refine ⟨q, ?_⟩
    apply (M.realize_exConditions s 5 _ (extend (s.encode q) (extend σ.val base)) carrier rfl).2
    let e := extend (s.encode r) (extend (s.encode q) (extend σ.val base))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 2 1 e hz hσ (M.transitive carrier (s.encode_mem q))).2 eq
    · exact (M.realize_pairMembershipFormula pairing 2 0 4 e hσ (M.transitive carrier (s.encode_mem r)) hτ).2 old
    · exact (M.realize_conditionLE s pairing carrier order 1 0 7 e q r rfl rfl rfl).2 qr
    · exact (M.realize_conditionLE s pairing carrier order 1 5 7 e q p rfl rfl rfl).2 qp

theorem restrictBelow_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.restrictBelow p τ).val ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hτ)) carrier
  have bound : (Name.restrictBelow p τ).val ⊆ B := by
    intro z hz
    obtain ⟨σ, q, rfl⟩ := Name.entries_cover (Name.restrictBelow p τ) hz
    obtain ⟨r, old, _, _⟩ := (Name.entry_restrictBelow p τ σ q).1 hz
    exact pairBound σ.val (Name.child_mem_doubleUnion old) (s.encode q) (s.encode_mem q)
  let context := extend τ.val (extend (s.encode p) (extend s.carrier (extend s.conditionOrder Fin.elim0)))
  have selected := M.separation_mem separation restrictionEntryFormula context
    (Fin.cases hτ (Fin.cases (M.transitive carrier (s.encode_mem p))
      (Fin.cases carrier (Fin.cases order (fun i => Fin.elim0 i))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets restrictionEntryFormula (extend z context)) B =
      (Name.restrictBelow p τ).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_restrictionEntryFormula s pairing carrier order p τ hτ z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_restrictionEntryFormula s pairing carrier order p τ hτ z
        (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def subgroupOrbitCodes (K : Subgroup G) (τ : Name s) : ZFSet.{u} :=
  ZFSet.range (fun g : K => (a.act s g.val τ).val)

theorem mem_subgroupOrbitCodes (K : Subgroup G) (τ : Name s) (y : ZFSet.{u}) :
    y ∈ a.subgroupOrbitCodes s K τ ↔ ∃ g ∈ K, y = (a.act s g τ).val := by
  rw [subgroupOrbitCodes, ZFSet.mem_range]
  constructor
  · rintro ⟨g, eq⟩
    exact ⟨g.val, g.property, eq.symm⟩
  · rintro ⟨g, hg, eq⟩
    exact ⟨⟨g, hg⟩, eq.symm⟩

theorem entry_act_restrictBelow (g : G) (p : P) (τ σ : Name s) (q : P) :
    Name.Entry σ (a.act s g (Name.restrictBelow p τ)) q ↔
      ∃ ν r, Name.Entry ν τ r ∧ a.act s g ν = σ ∧ q ≤ a.iso g p ∧ q ≤ a.iso g r := by
  change Name.Entry σ (Name.rename s (a.iso g) (Name.restrictBelow p τ)) q ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, c, entry, eq, cq⟩
    obtain ⟨r, old, cr, cp⟩ := (Name.entry_restrictBelow p τ ν c).1 entry
    refine ⟨ν, r, old, eq, ?_, ?_⟩
    · rw [← cq]
      exact (a.iso g).monotone cp
    · rw [← cq]
      exact (a.iso g).monotone cr
  · rintro ⟨ν, r, old, eq, qp, qr⟩
    refine ⟨ν, (a.iso g).symm q, (Name.entry_restrictBelow p τ ν _).2 ⟨r, old, ?_, ?_⟩,
      eq, (a.iso g).apply_symm_apply q⟩
    · exact (a.iso g).le_iff_le.1 (by simpa only [OrderIso.apply_symm_apply] using qr)
    · exact (a.iso g).le_iff_le.1 (by simpa only [OrderIso.apply_symm_apply] using qp)

theorem mix_code_union (K : Subgroup G) (p : P) (τ : Name s) :
    (a.mix s K p τ).val = ⋃₀ (a.subgroupOrbitCodes s K (Name.restrictBelow p τ)) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · intro hz
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (a.mix s K p τ) hz
    have entry : Name.Entry σ (a.mix s K p τ) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (a.mix s K p τ).val
      rwa [← eq]
    obtain ⟨g, hg, ν, r, old, moved, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
    refine ⟨(a.act s g (Name.restrictBelow p τ)).val,
      (a.mem_subgroupOrbitCodes s K _ _).2 ⟨g, hg, rfl⟩, ?_⟩
    rw [eq]
    exact (a.entry_act_restrictBelow s g p τ σ q).2 ⟨ν, r, old, moved, qp, qr⟩
  · rintro ⟨w, hw, hz⟩
    obtain ⟨g, hg, rfl⟩ := (a.mem_subgroupOrbitCodes s K _ w).1 hw
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (a.act s g (Name.restrictBelow p τ)) hz
    have entry : Name.Entry σ (a.act s g (Name.restrictBelow p τ)) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (a.act s g (Name.restrictBelow p τ)).val
      rwa [← eq]
    obtain ⟨ν, r, old, moved, qp, qr⟩ := (a.entry_act_restrictBelow s g p τ σ q).1 entry
    rw [eq]
    exact (a.entry_mix s K p τ σ q).2 ⟨g, hg, ν, r, old, moved, qp, qr⟩

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.SetFormula

def subgroupOrbitFormula : SetFormula 6 :=
  exConditions 4 (.conj (.mem 0 3)
    (atomicApplication codedNameActionFormula (extend 4 (extend 6 Fin.elim0)) 0 2 1))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_subgroupOrbitFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (τ : Name s) (hτ : τ.val ∈ M.sets) (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets subgroupOrbitFormula (extend y (extend τ.val (extend (t.subset (fun g => g ∈ K))
      (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      y ∈ a.subgroupOrbitCodes s K τ := by
  rw [subgroupOrbitFormula, M.realize_exConditions t 4 _ _ group rfl, a.mem_subgroupOrbitCodes]
  apply exists_congr
  intro g
  change (t.encode g ∈ t.subset (fun g => g ∈ K) ∧ Realize M.sets _ _) ↔ _
  rw [t.encode_mem_subset]
  apply and_congr_right
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  change Realize M.sets codedNameActionFormula (extend (t.encode g) (extend τ.val (extend y
    (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔ _
  rw [M.realize_codedNameActionFormula a s t pairing unions powers separation collection carrier group maps g τ.val y hτ hy]
  constructor
  · rintro ⟨σ, eq, output⟩
    have names : σ.val = τ := Subtype.ext eq
    rwa [names] at output
  · intro eq
    exact ⟨⟨τ, hτ⟩, rfl, eq⟩

theorem subgroupOrbitCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : a.subgroupOrbitCodes s K τ ∈ M.sets := by
  let W := ({τ.val, τ.val} : ZFSet.{u})
  have hW : W ∈ M.sets := M.unorderedPair_mem pairing hτ hτ
  let B := a.orbitCodes s (M.nameDomain s) W
  have hB := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  have bound : a.subgroupOrbitCodes s K τ ⊆ B := by
    intro y hy
    obtain ⟨g, _, eq⟩ := (a.mem_subgroupOrbitCodes s K τ y).1 hy
    exact (a.mem_orbitCodes s (M.nameDomain s) W y).2
      ⟨g, τ, hτ, ZFSet.mem_pair.2 (Or.inl rfl), eq⟩
  let context := extend τ.val (extend (t.subset (fun g => g ∈ K))
    (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))
  have selected := M.separation_mem separation subgroupOrbitFormula context
    (Fin.cases hτ (Fin.cases hK (Fin.cases carrier (Fin.cases group (Fin.cases maps (fun i => Fin.elim0 i)))))) hB
  have eq : ZFSet.sep (fun y => Realize M.sets subgroupOrbitFormula (extend y context)) B =
      a.subgroupOrbitCodes s K τ := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hy, rel⟩
      exact (M.realize_subgroupOrbitFormula a s t pairing unions powers separation collection carrier group maps K τ hτ y
        (M.transitive hB hy)).1 rel
    · intro hy
      exact ⟨bound hy, (M.realize_subgroupOrbitFormula a s t pairing unions powers separation collection carrier group maps K τ hτ y
        (M.transitive hB (bound hy))).2 hy⟩
  exact eq ▸ selected

theorem mix_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (a.mix s K p τ).val ∈ M.sets := by
  rw [a.mix_code_union]
  exact M.union_mem unions (M.subgroupOrbitCodes_mem a s t pairing unions powers separation collection carrier group maps K hK
    (Name.restrictBelow p τ) (M.restrictBelow_mem s pairing unions powers separation carrier order p τ hτ))

end PartitionPilot.Forcing.TransitiveGround

end OAI
