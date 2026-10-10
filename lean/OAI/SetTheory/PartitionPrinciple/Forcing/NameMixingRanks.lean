import OAI.SetTheory.PartitionPrinciple.Forcing.OrbitPairGraphNames

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

noncomputable def nameRank (τ : Name s) : Ordinal.{u} := ZFSet.rank (eval Set.univ τ)

theorem eval_univ (τ : Name s) :
    eval Set.univ τ = ZFSet.range (fun a : Entries τ => eval Set.univ a.val.1) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, ZFSet.mem_range]
  constructor
  · rintro ⟨σ, p, h, _, eq⟩
    exact ⟨⟨(σ, p), h⟩, eq⟩
  · rintro ⟨a, eq⟩
    exact ⟨a.val.1, a.val.2, a.property, Set.mem_univ _, eq⟩

theorem nameRank_eq (τ : Name s) :
    nameRank τ = ⨆ a : Entries τ, Order.succ (nameRank a.val.1) := by
  change ZFSet.rank (eval Set.univ τ) = _
  rw [eval_univ, ZFSet.rank_range]
  rfl

theorem entry_nameRank_lt {σ τ : Name s} {p : P} (h : Entry σ τ p) :
    nameRank σ < nameRank τ :=
  ZFSet.rank_lt_of_mem ((mem_eval Set.univ τ _).2 ⟨σ, p, h, Set.mem_univ _, rfl⟩)

theorem nameRank_rename (t : Presentation Q) (f : P → Q) (τ : Name s) :
    nameRank (rename t f τ) = nameRank τ := by
  unfold nameRank
  rw [eval_rename]
  rfl

theorem rank_eval_le (H : Set P) (τ : Name s) : ZFSet.rank (eval H τ) ≤ nameRank τ := by
  induction τ using inductionOn with
  | step τ ih =>
    rw [ZFSet.rank_le_iff]
    intro x hx
    obtain ⟨σ, p, entry, _, rfl⟩ := (mem_eval H τ x).1 hx
    exact (ih σ p entry).trans_lt (entry_nameRank_lt entry)

theorem nameRank_check (one : P) (x : ZFSet.{u}) : nameRank (check s one x) = ZFSet.rank x := by
  unfold nameRank
  rw [eval_check Set.univ one (Set.mem_univ one)]

end PartitionPilot.Forcing.Name


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def selectName (R : Name s → P → Prop) (τ : Name s) : Name s :=
  assemble (fun z : {z : Entries τ × P // z.2 ≤ z.1.val.2 ∧ R z.1.val.1 z.2} => z.val.1.val.1)
    (fun z => z.val.2)

theorem entry_selectName (R : Name s → P → Prop) (τ σ : Name s) (p : P) :
    Entry σ (selectName R τ) p ↔ ∃ r, Entry σ τ r ∧ p ≤ r ∧ R σ p := by
  rw [selectName, entry_assemble]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z.val.1.val.2, z.val.1.property, z.property⟩
  · rintro ⟨r, entry, pr, hR⟩
    exact ⟨⟨(⟨(σ, r), entry⟩, p), pr, hR⟩, rfl, rfl⟩

theorem nameRank_selectName_le (R : Name s → P → Prop) (τ : Name s) :
    nameRank (selectName R τ) ≤ nameRank τ := by
  change ZFSet.rank (eval Set.univ (selectName R τ)) ≤ nameRank τ
  rw [ZFSet.rank_le_iff]
  intro x hx
  obtain ⟨σ, p, entry, _, rfl⟩ := (mem_eval Set.univ (selectName R τ) x).1 hx
  obtain ⟨r, old, _, _⟩ := (entry_selectName R τ σ p).1 entry
  exact (rank_eval_le Set.univ σ).trans_lt (entry_nameRank_lt old)

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_selectName (g : G) (R R' : Name s → P → Prop)
    (transport : ∀ σ p, R' (a.act s g σ) (a.iso g p) ↔ R σ p) (τ : Name s) :
    a.act s g (Name.selectName R τ) = Name.selectName R' (a.act s g τ) := by
  apply Name.ext
  intro σ p
  obtain ⟨σ, rfl⟩ := (a.nameEquiv s g).surjective σ
  obtain ⟨p, rfl⟩ := (a.iso g).surjective p
  change Name.Entry (a.act s g σ) (a.act s g (Name.selectName R τ)) (a.iso g p) ↔
    Name.Entry (a.act s g σ) (Name.selectName R' (a.act s g τ)) (a.iso g p)
  rw [a.entry_act, Name.entry_selectName, Name.entry_selectName]
  constructor
  · rintro ⟨r, entry, pr, hR⟩
    exact ⟨a.iso g r, (a.entry_act s g σ τ r).2 entry,
      (a.iso g).monotone pr, (transport σ p).2 hR⟩
  · rintro ⟨r, entry, pr, hR⟩
    obtain ⟨r, rfl⟩ := (a.iso g).surjective r
    exact ⟨r, (a.entry_act s g σ τ r).1 entry, (a.iso g).le_iff_le.1 pr, (transport σ p).1 hR⟩

end PartitionPilot.Forcing.PosetAction

end


namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def separationPredicate (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (σ : Name s) (p : P) : Prop :=
  ∃ h : σ ∈ D.names, Forces D φ (extend ⟨σ, h⟩ env) p

noncomputable def separationName (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (τ : Name s) : Name s := selectName (separationPredicate D φ env) τ

theorem entry_separationName (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (τ σ : Name s) (p : P) :
    Entry σ (separationName D φ env τ) p ↔
      ∃ r, Entry σ τ r ∧ p ≤ r ∧ ∃ h : σ ∈ D.names, Forces D φ (extend ⟨σ, h⟩ env) p := by
  rw [separationName, entry_selectName]
  rfl

theorem eval_separationName (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) {τ : Name s} (hτ : τ ∈ D.names) :
    eval {p | H.mem p} (separationName D φ env τ) =
      ZFSet.sep (fun x => Realize (D.values {p | H.mem p}) φ
        (extend x (evalAssignment {p | H.mem p} env))) (eval {p | H.mem p} τ) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, ZFSet.mem_sep]
  constructor
  · rintro ⟨σ, p, entry, hp, value⟩
    obtain ⟨r, old, pr, hσ, forced⟩ := (entry_separationName D φ env τ σ p).1 entry
    have truth := forces_sound D H generic φ (extend ⟨σ, hσ⟩ env) hp forced
    rw [evalAssignment_extend, value] at truth
    exact ⟨(mem_eval _ τ x).2 ⟨σ, r, old, H.upward hp pr, value⟩, truth⟩
  · rintro ⟨member, truth⟩
    obtain ⟨σ, r, entry, hr, value⟩ := (mem_eval _ τ x).1 member
    have hσ := D.children hτ entry
    have instanceTruth : Realize (D.values {p | H.mem p}) φ
        (evalAssignment {p | H.mem p} (extend ⟨σ, hσ⟩ env)) := by
      rw [evalAssignment_extend, value]
      exact truth
    obtain ⟨q, hq, forced⟩ := (forcing_truth D H generic φ (extend ⟨σ, hσ⟩ env)).1 instanceTruth
    obtain ⟨p, hp, pr, pq⟩ := H.directed hr hq
    exact ⟨σ, p, (entry_separationName D φ env τ σ p).2
      ⟨r, entry, pr, hσ, forces_mono D φ (extend ⟨σ, hσ⟩ env) forced pq⟩, hp, value⟩

theorem nameRank_separationName_le (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (τ : Name s) : nameRank (separationName D φ env τ) ≤ nameRank τ :=
  nameRank_selectName_le (separationPredicate D φ env) τ

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] [Small.{u} G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

def MixIndices (K : Subgroup G) (p : P) (τ : Name s) :=
  {z : K × Name.Entries τ × P //
    z.2.2 ≤ a.iso z.1.val p ∧ z.2.2 ≤ a.iso z.1.val z.2.1.val.2}

instance mixIndices_small (K : Subgroup G) (p : P) (τ : Name s) :
    Small.{u} (a.MixIndices s K p τ) := by
  unfold MixIndices
  infer_instance

noncomputable def mix (K : Subgroup G) (p : P) (τ : Name s) : Name s :=
  Name.assemble (fun z : a.MixIndices s K p τ => a.act s z.val.1.val z.val.2.1.val.1)
    (fun z => z.val.2.2)

theorem entry_mix (K : Subgroup G) (p : P) (τ σ : Name s) (q : P) :
    Name.Entry σ (a.mix s K p τ) q ↔
      ∃ g ∈ K, ∃ ν r, Name.Entry ν τ r ∧ a.act s g ν = σ ∧
        q ≤ a.iso g p ∧ q ≤ a.iso g r := by
  rw [mix, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨z.val.1.val, z.val.1.property, z.val.2.1.val.1, z.val.2.1.val.2,
      z.val.2.1.property, eq, z.property⟩
  · rintro ⟨g, hg, ν, r, entry, eq, lower⟩
    exact ⟨⟨(⟨g, hg⟩, ⟨(ν, r), entry⟩, q), lower⟩, eq, rfl⟩

theorem mix_entry_translated (K : Subgroup G) (p : P) (τ : Name s)
    {σ : Name s} {q : P} (entry : Name.Entry σ (a.mix s K p τ) q)
    {h : G} (hh : h ∈ K) :
    Name.Entry (a.act s h σ) (a.mix s K p τ) (a.iso h q) := by
  obtain ⟨g, hg, ν, r, old, eq, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
  apply (a.entry_mix s K p τ _ _).2
  refine ⟨h * g, K.mul_mem hh hg, ν, r, old, ?_, ?_, ?_⟩
  · rw [a.act_mul, eq]
  · rw [a.mul]
    exact (a.iso h).monotone qp
  · rw [a.mul]
    exact (a.iso h).monotone qr

theorem mix_fixed (K : Subgroup G) (p : P) (τ : Name s) {g : G} (hg : g ∈ K) :
    a.act s g (a.mix s K p τ) = a.mix s K p τ := by
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename s (a.iso g) (a.mix s K p τ)) q ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, r, entry, eq, hr⟩
    change a.act s g ν = σ at eq
    have h := a.mix_entry_translated s K p τ entry hg
    simpa only [eq, hr] using h
  · intro entry
    have moved := a.mix_entry_translated s K p τ entry (K.inv_mem hg)
    refine ⟨a.act s g⁻¹ σ, a.iso g⁻¹ q, moved, a.act_inv_right s g σ, ?_⟩
    rw [← a.mul, mul_inv_cancel, a.one]

theorem mix_hs (F : NormalSubgroupFamily G) (K : Subgroup G) (hK : F.mem K)
    (p : P) {τ : Name s} (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (a.mix s K p τ) := by
  refine HereditarilySymmetric.mk (F.upward hK ?_) ?_
  · intro g hg
    exact a.mix_fixed s K p τ hg
  · intro σ q entry
    obtain ⟨g, _, ν, r, old, rfl, _, _⟩ := (a.entry_mix s K p τ σ q).1 entry
    exact (hτ.member old).translated g

theorem mem_eval_mix (K : Subgroup G) (p : P) (τ : Name s)
    (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ Name.eval {q | H.mem q} (a.mix s K p τ) ↔
      ∃ g ∈ K, H.mem (a.iso g p) ∧ x ∈ Name.eval {q | H.mem q} (a.act s g τ) := by
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, q, entry, hq, eq⟩
    obtain ⟨g, hg, ν, r, old, rfl, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
    refine ⟨g, hg, H.upward hq qp, ?_⟩
    apply (Name.mem_eval {q | H.mem q} (a.act s g τ) x).2
    exact ⟨a.act s g ν, a.iso g r, (a.entry_act s g ν τ r).2 old,
      H.upward hq qr, eq⟩
  · rintro ⟨g, hg, hp, hx⟩
    obtain ⟨σ, q, entry, hq, eq⟩ := (Name.mem_eval {q | H.mem q} (a.act s g τ) x).1 hx
    change Name.Entry σ (Name.rename s (a.iso g) τ) q at entry
    obtain ⟨ν, r, old, rfl, rfl⟩ := (Name.entry_rename s (a.iso g) τ σ q).1 entry
    obtain ⟨c, hc, cp, cr⟩ := H.directed hp hq
    exact ⟨a.act s g ν, c,
      (a.entry_mix s K p τ _ c).2 ⟨g, hg, ν, r, old, rfl, cp, cr⟩, hc, eq⟩

theorem eval_mix_of_active_equal (K : Subgroup G) (p : P) (τ : Name s)
    (H : ConditionFilter P) (hp : H.mem p)
    (agree : ∀ g ∈ K, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g τ) = Name.eval {q | H.mem q} τ) :
    Name.eval {q | H.mem q} (a.mix s K p τ) = Name.eval {q | H.mem q} τ := by
  apply ZFSet.ext
  intro x
  rw [a.mem_eval_mix s]
  constructor
  · rintro ⟨g, hg, active, hx⟩
    rwa [agree g hg active] at hx
  · intro hx
    refine ⟨1, K.one_mem, ?_, ?_⟩
    · simpa only [a.one] using hp
    · simpa only [a.act_one] using hx

end PartitionPilot.Forcing.PosetAction


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def UnionIndices (τ : Name s) :=
  {z : (Σ e : Entries τ, Entries e.val.1) × P //
    z.2 ≤ z.1.1.val.2 ∧ z.2 ≤ z.1.2.val.2}

instance unionIndices_small (τ : Name s) : Small.{u} (UnionIndices τ) := by
  unfold UnionIndices
  infer_instance

noncomputable def unionName (τ : Name s) : Name s :=
  assemble (fun z : UnionIndices τ => z.val.1.2.val.1) (fun z => z.val.2)

theorem entry_unionName (τ σ : Name s) (p : P) : Entry σ (unionName τ) p ↔
    ∃ ν r q, Entry ν τ r ∧ Entry σ ν q ∧ p ≤ r ∧ p ≤ q := by
  rw [unionName, entry_assemble]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z.val.1.1.val.1, z.val.1.1.val.2, z.val.1.2.val.2,
      z.val.1.1.property, z.val.1.2.property, z.property⟩
  · rintro ⟨ν, r, q, topEntry, child, pr, pq⟩
    exact ⟨⟨(⟨⟨(ν, r), topEntry⟩, ⟨(σ, q), child⟩⟩, p), pr, pq⟩, rfl, rfl⟩

theorem eval_unionName (H : ConditionFilter P) (τ : Name s) :
    eval {p | H.mem p} (unionName τ) = ZFSet.sUnion (eval {p | H.mem p} τ) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨σ, p, entry, hp, value⟩
    obtain ⟨ν, r, q, topEntry, child, pr, pq⟩ := (entry_unionName τ σ p).1 entry
    exact ⟨eval {p | H.mem p} ν,
      (mem_eval _ τ _).2 ⟨ν, r, topEntry, H.upward hp pr, rfl⟩,
      (mem_eval _ ν x).2 ⟨σ, q, child, H.upward hp pq, value⟩⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨ν, r, topEntry, hr, rfl⟩ := (mem_eval _ τ y).1 hy
    obtain ⟨σ, q, child, hq, value⟩ := (mem_eval _ ν x).1 hx
    obtain ⟨p, hp, pr, pq⟩ := H.directed hr hq
    exact ⟨σ, p, (entry_unionName τ σ p).2 ⟨ν, r, q, topEntry, child, pr, pq⟩, hp, value⟩

theorem nameRank_unionName_le (τ : Name s) : nameRank (unionName τ) ≤ nameRank τ := by
  change ZFSet.rank (eval Set.univ (unionName τ)) ≤ nameRank τ
  rw [ZFSet.rank_le_iff]
  intro x hx
  obtain ⟨σ, p, entry, _, rfl⟩ := (mem_eval Set.univ (unionName τ) x).1 hx
  obtain ⟨ν, r, q, topEntry, child, _, _⟩ := (entry_unionName τ σ p).1 entry
  exact (rank_eval_le Set.univ σ).trans_lt
    ((entry_nameRank_lt child).trans (entry_nameRank_lt topEntry))

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_unionName (g : G) (τ : Name s) :
    a.act s g (Name.unionName τ) = Name.unionName (a.act s g τ) := by
  apply Name.ext
  intro σ p
  obtain ⟨σ, rfl⟩ := (a.nameEquiv s g).surjective σ
  obtain ⟨p, rfl⟩ := (a.iso g).surjective p
  change Name.Entry (a.act s g σ) (a.act s g (Name.unionName τ)) (a.iso g p) ↔
    Name.Entry (a.act s g σ) (Name.unionName (a.act s g τ)) (a.iso g p)
  rw [a.entry_act, Name.entry_unionName, Name.entry_unionName]
  constructor
  · rintro ⟨ν, r, q, topEntry, child, pr, pq⟩
    exact ⟨a.act s g ν, a.iso g r, a.iso g q,
      (a.entry_act s g ν τ r).2 topEntry, (a.entry_act s g σ ν q).2 child,
      (a.iso g).monotone pr, (a.iso g).monotone pq⟩
  · rintro ⟨ν, r, q, topEntry, child, pr, pq⟩
    obtain ⟨ν, rfl⟩ := (a.nameEquiv s g).surjective ν
    obtain ⟨r, rfl⟩ := (a.iso g).surjective r
    obtain ⟨q, rfl⟩ := (a.iso g).surjective q
    exact ⟨ν, r, q, (a.entry_act s g ν τ r).1 topEntry,
      (a.entry_act s g σ ν q).1 child, (a.iso g).le_iff_le.1 pr, (a.iso g).le_iff_le.1 pq⟩

theorem unionName_hs (F : NormalSubgroupFamily G) {τ : Name s}
    (hτ : HereditarilySymmetric a s F τ) : HereditarilySymmetric a s F (Name.unionName τ) := by
  refine HereditarilySymmetric.mk (F.upward hτ.symmetric ?_) ?_
  · intro g fixed
    change a.act s g (Name.unionName τ) = Name.unionName τ
    rw [a.act_unionName]
    exact congrArg Name.unionName fixed
  · intro σ p entry
    obtain ⟨ν, r, q, topEntry, child, _, _⟩ := (Name.entry_unionName τ σ p).1 entry
    exact (hτ.member topEntry).member child

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def envelope (τ : Name s) : Name s := selectName (fun _ _ => True) τ

theorem entry_envelope (τ σ : Name s) (p : P) :
    Entry σ (envelope τ) p ↔ ∃ r, Entry σ τ r ∧ p ≤ r := by
  simp only [envelope, entry_selectName, and_true]

theorem selectName_subset_envelope (R : Name s → P → Prop) (τ : Name s) :
    (selectName R τ).val ⊆ (envelope τ).val := by
  intro z hz
  obtain ⟨σ, p, rfl⟩ := entries_cover (selectName R τ) hz
  obtain ⟨r, old, pr, _⟩ := (entry_selectName R τ σ p).1 hz
  exact (entry_envelope τ σ p).2 ⟨r, old, pr⟩

omit [Preorder P] in
theorem eval_mono (H : Set P) {σ τ : Name s} (sub : σ.val ⊆ τ.val) :
    eval H σ ⊆ eval H τ := by
  intro x hx
  obtain ⟨ν, p, entry, hp, eq⟩ := (mem_eval H σ x).1 hx
  exact (mem_eval H τ x).2 ⟨ν, p, sub entry, hp, eq⟩

theorem eval_envelope (H : ConditionFilter P) (τ : Name s) :
    eval {p | H.mem p} (envelope τ) = eval {p | H.mem p} τ := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨r, old, pr⟩ := (entry_envelope τ σ p).1 entry
    exact ⟨σ, r, old, H.upward hp pr, eq⟩
  · rintro ⟨σ, p, entry, hp, eq⟩
    exact ⟨σ, p, (entry_envelope τ σ p).2 ⟨p, entry, le_rfl⟩, hp, eq⟩

theorem separationName_true (D : NameDomain s) {τ : Name s} (hτ : τ ∈ D.names) :
    separationName D (.equal 0 0) Fin.elim0 τ = envelope τ := by
  apply ext
  intro σ p
  rw [entry_separationName, entry_envelope]
  constructor
  · rintro ⟨r, old, pr, _⟩
    exact ⟨r, old, pr⟩
  · rintro ⟨r, old, pr⟩
    exact ⟨r, old, pr, D.children hτ old, forcesEq_refl σ p⟩

omit [Preorder P] in
theorem rename_mono (f : P → P) {σ τ : Name s} (sub : σ.val ⊆ τ.val) :
    (rename s f σ).val ⊆ (rename s f τ).val := by
  intro z hz
  obtain ⟨ν, p, rfl⟩ := entries_cover (rename s f σ) hz
  obtain ⟨χ, q, entry, eq, hp⟩ := (entry_rename s f σ ν p).1 hz
  exact (entry_rename s f τ ν p).2 ⟨χ, q, sub entry, eq, hp⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_envelope (g : G) (τ : Name s) :
    a.act s g (Name.envelope τ) = Name.envelope (a.act s g τ) :=
  a.act_selectName s g (fun _ _ => True) (fun _ _ => True) (fun _ _ => Iff.rfl) τ

theorem envelope_hs (F : NormalSubgroupFamily G) {τ : Name s}
    (hτ : HereditarilySymmetric a s F τ) : HereditarilySymmetric a s F (Name.envelope τ) := by
  refine HereditarilySymmetric.mk (F.upward hτ.symmetric ?_) ?_
  · intro g hg
    change a.act s g (Name.envelope τ) = Name.envelope τ
    rw [a.act_envelope, show a.act s g τ = τ from hg]
  · intro σ p entry
    obtain ⟨r, old, _⟩ := (Name.entry_envelope τ σ p).1 entry
    exact hτ.member old

theorem act_subset_iff_fixed (g : G) {σ τ : Name s} (fixed : a.act s g τ = τ) :
    (a.act s g σ).val ⊆ τ.val ↔ σ.val ⊆ τ.val := by
  constructor
  · intro sub
    have h := Name.rename_mono (a.iso g⁻¹) sub
    change (a.act s g⁻¹ (a.act s g σ)).val ⊆ (a.act s g⁻¹ τ).val at h
    rw [a.act_inv_left, ← fixed, a.act_inv_left] at h
    exact h
  · intro sub
    have h := Name.rename_mono (a.iso g) sub
    change (a.act s g σ).val ⊆ (a.act s g τ).val at h
    rwa [fixed] at h

end PartitionPilot.Forcing.PosetAction

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem nameRank_act (g : G) (τ : Name s) :
    Name.nameRank (a.act s g τ) = Name.nameRank τ :=
  Name.nameRank_rename s (a.iso g) τ

theorem nameRank_mix_le [Small.{u} G] (K : Subgroup G) (p : P) (τ : Name s) :
    Name.nameRank (a.mix s K p τ) ≤ Name.nameRank τ := by
  change ZFSet.rank (Name.eval Set.univ (a.mix s K p τ)) ≤ Name.nameRank τ
  rw [ZFSet.rank_le_iff]
  intro value hv
  obtain ⟨σ, q, entry, _, rfl⟩ := (Name.mem_eval Set.univ (a.mix s K p τ) value).1 hv
  obtain ⟨g, _, ν, r, old, rfl, _, _⟩ := (a.entry_mix s K p τ σ q).1 entry
  apply (Name.rank_eval_le Set.univ (a.act s g ν)).trans_lt
  rw [a.nameRank_act]
  exact Name.entry_nameRank_lt old

end PartitionPilot.Forcing.PosetAction

end OAI
