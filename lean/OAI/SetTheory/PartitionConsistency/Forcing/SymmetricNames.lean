import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingTruth

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v w

/-- A set symmetric system with a named presentation of the conditions.
Every piece of data is algebraic: no forcing axiom or satisfaction assertion
is included in this structure. The equivalence also ensures that the poset is
a set in the same universe as the literal name codes. -/
structure SymmetricSystem (P : Type w) [Preorder P] (Γ : Type v) [Group Γ] where
  action : ConditionAction.{u} Γ
  codeEquiv : P ≃ action.conditions
  order : ∀ g p q,
    codeEquiv.symm (action.perm g (codeEquiv p)) ≤
      codeEquiv.symm (action.perm g (codeEquiv q)) ↔ p ≤ q
  filter : Set (Subgroup Γ)
  normal : SupportFilter.IsNormalFilter filter

namespace SymmetricSystem
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem small_conditions (S : SymmetricSystem.{u} P Γ) : Small.{u} P := small_of_injective S.codeEquiv.injective

/-- The actual set code, not a semantic truth value. -/
def code (p : P) : ZFSet.{u} := (S.codeEquiv p).val

theorem code_mem (p : P) : S.code p ∈ S.action.conditions := (S.codeEquiv p).property

theorem code_injective : Function.Injective S.code := fun _ _ h =>
  S.codeEquiv.injective (Subtype.ext h)

/-- Automorphisms of the poset obtained from its coded action. -/
noncomputable def move (g : Γ) : P ≃o P where
  toEquiv := (S.codeEquiv.trans (S.action.perm g)).trans S.codeEquiv.symm
  map_rel_iff' := fun {p q} => S.order g p q

@[simp] theorem actCode_code (g : Γ) (p : P) :
    S.action.actCode g (S.code p) = S.code (S.move g p) := by
  rw [S.action.actCode_of_mem g (S.code_mem p)]
  change (S.action.perm g (S.codeEquiv p)).val =
    (S.codeEquiv (S.codeEquiv.symm (S.action.perm g (S.codeEquiv p)))).val
  rw [Equiv.apply_symm_apply]

/-- All hereditarily symmetric names, without any fixed bound on ranks. -/
def Name := {σ : S.action.Name // ConditionAction.Name.HS S.filter σ}

namespace Name
variable {S}

def raw (σ : S.Name) : ZFSet.{u} := σ.1.val

@[ext] theorem ext {σ τ : S.Name} (h : σ.raw = τ.raw) : σ = τ :=
  Subtype.ext (ConditionAction.Name.ext h)

theorem isName (σ : S.Name) : IsName S.action.conditions σ.raw := σ.1.property

theorem hs (σ : S.Name) : ConditionAction.Name.HS S.filter σ.1 := σ.property

/-- An active entry is automatically HS by hereditary symmetry. -/
def child (σ : S.Name) {ρ c : ZFSet.{u}} (he : ZFSet.pair ρ c ∈ σ.raw) : S.Name :=
  ⟨σ.1.child he, σ.property.child he⟩

@[simp] theorem child_val (σ : S.Name) {ρ c : ZFSet.{u}} (he : ZFSet.pair ρ c ∈ σ.raw) :
    (σ.child he).raw = ρ := rfl

noncomputable instance : MulAction Γ S.Name where
  smul g σ := ⟨g • σ.1, σ.property.smul S.normal g⟩
  one_smul σ := Subtype.ext (one_smul Γ σ.1)
  mul_smul g h σ := Subtype.ext (mul_smul g h σ.1)

@[simp] theorem smul_val (g : Γ) (σ : S.Name) :
    (g • σ).raw = mapConditions (S.action.actCode g) σ.raw := rfl

noncomputable def empty : S.Name :=
  ⟨ConditionAction.Name.empty, ConditionAction.Name.empty_HS S.normal.1⟩

@[simp] theorem empty_val : (empty : S.Name).raw = ∅ := rfl

instance : Nonempty S.Name := ⟨empty⟩

end Name

/-- The previously constructed recursive atomic relations, restricted to the
actual HS class of this set symmetric system. -/
noncomputable def atomic : ForcingQuotient.AtomicData P S.Name where
  EqF p a b := AtomicForcing.EqAt S.code p a.raw b.raw
  MemF p a b := AtomicForcing.MemAt S.code p a.raw b.raw
  eq_mono := AtomicForcing.eq_mono
  mem_mono := AtomicForcing.mem_mono
  eq_refl p a := AtomicForcing.eq_refl p a.raw
  eq_symm := AtomicForcing.eq_symm
  eq_trans := AtomicForcing.eq_trans
  mem_congr ha hb := (AtomicForcing.mem_congr_left ha).trans (AtomicForcing.mem_congr_right hb)

theorem atomic_regular : S.atomic.Regular :=
  ⟨fun _ _ _ => AtomicForcing.eq_of_dense, fun _ _ _ => AtomicForcing.mem_of_dense⟩

/-- Named formula forcing in this symmetric system. Quantifiers range over all
HS names; the existential clause remains density of local witnesses. -/
abbrev Forces {n} (v : Fin n → S.Name) (p : P) (φ : Formula n) : Prop :=
  S.atomic.ForceFormula v p φ

/-- Full formula symmetry for the concrete HS class. -/
theorem forces_symmetry (g : Γ) {n} (φ : Formula n) (v : Fin n → S.Name) (p : P) :
    S.Forces v p φ ↔ S.Forces (fun i => g • v i) (S.move g p) φ := by
  apply S.atomic.force_symmetry (S.move g) (MulAction.toPerm g)
  · intro p a b
    exact (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
      (S.move g) (S.actCode_code g) a.raw b.raw).2 p
  · intro p a b
    exact (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
      (S.move g) (S.actCode_code g) a.raw b.raw).1 p

/-- Ordinary syntactic consistency follows if *all* axioms of a theory are
forced. This result does not assert the forcing of PP, ACwo, or failure of
Choice. In particular it is not the selected main theorem. -/
theorem consistent_of_forces {T : Theory} (p : P)
    (hT : ∀ φ ∈ T, S.Forces Fin.elim0 p φ) : Consistent T :=
  S.atomic.consistent_of_regular_forcing S.atomic_regular p hT

end SymmetricSystem
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Active members of an HS name are in the same quantifier domain. -/
theorem mem_iff {p : P} {ν σ : S.Name} : S.atomic.MemF p ν σ ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ (τ : S.Name) (c : P),
      ZFSet.pair τ.raw (S.code c) ∈ σ.raw ∧ r ≤ c ∧ S.atomic.EqF r ν τ := by
  constructor
  · intro h q hqp
    obtain ⟨r, hrq, τ, c, he, hrc, heq⟩ := AtomicForcing.mem_iff.mp h q hqp
    exact ⟨r, hrq, σ.child he, c, he, hrc, heq⟩
  · intro h
    apply AtomicForcing.mem_iff.mpr
    intro q hqp
    obtain ⟨r, hrq, τ, c, he, hrc, heq⟩ := h q hqp
    exact ⟨r, hrq, τ.raw, c, he, hrc, heq⟩

theorem mem_of_edge {p c : P} {σ τ : S.Name}
    (he : ZFSet.pair τ.raw (S.code c) ∈ σ.raw) (hpc : p ≤ c) :
    S.atomic.MemF p τ σ := AtomicForcing.mem_of_edge_eq hpc he (S.atomic.eq_refl p τ)

/-- Extensionality is proved from the recursive definition of equality, not
assumed as another law of a forcing algebra. -/
theorem eq_of_same_members {p : P} {σ τ : S.Name}
    (h : ∀ ν : S.Name, ∀ q, q ≤ p → (S.atomic.MemF q ν σ ↔ S.atomic.MemF q ν τ)) :
    S.atomic.EqF p σ τ := by
  apply AtomicForcing.eq_iff.mpr
  constructor
  · intro ν c he q hqp hqc
    exact (h (σ.child he) q hqp).mp (S.mem_of_edge he hqc)
  · intro ν c he q hqp hqc
    exact (h (τ.child he) q hqp).mpr (S.mem_of_edge he hqc)

theorem not_mem_empty (p : P) (σ : S.Name) : ¬ S.atomic.MemF p σ Name.empty := by
  intro h
  obtain ⟨r, _, τ, c, he, _, _⟩ := (S.mem_iff.mp h) p le_rfl
  exact ZFSet.notMem_empty _ he

/-- A local minimal-member witness obtained by genuine well-founded induction
on literal names. No generic filter or external well-foundedness of a model
is used in this lemma. -/
theorem minimal_member (σ ν : S.Name) (p : P) (hmem : S.atomic.MemF p ν σ) :
    ∃ q, q ≤ p ∧ ∃ τ : S.Name, S.atomic.MemF q τ σ ∧
      ∀ ρ : S.Name, ∀ r, r ≤ q → S.atomic.MemF r ρ τ → ¬ S.atomic.MemF r ρ σ := by
  classical
  induction ν using (InvImage.wf (fun ν : S.Name => ν.raw) child_wf).induction generalizing p with
  | h ν ih =>
    by_cases hn : ∃ q, q ≤ p ∧ ∃ ρ : S.Name, S.atomic.MemF q ρ ν ∧ S.atomic.MemF q ρ σ
    · obtain ⟨q, hqp, ρ, hρν, hρσ⟩ := hn
      obtain ⟨r, hrq, χ, c, he, _, heq⟩ := (S.mem_iff.mp hρν) q le_rfl
      have hχσ : S.atomic.MemF r χ σ :=
        (S.atomic.mem_congr heq (S.atomic.eq_refl r σ)).mp (S.atomic.mem_mono hrq hρσ)
      obtain ⟨s, hsr, τ, hτ, hmin⟩ := ih χ ⟨S.code c, he⟩ r hχσ
      exact ⟨s, hsr.trans (hrq.trans hqp), τ, hτ, hmin⟩
    · exact ⟨p, le_rfl, ν, hmem, fun ρ r hr hρν hρσ => hn ⟨r, hr, ρ, hρν, hρσ⟩⟩

/-- The schema's Extensionality instance. -/
theorem forces_extensionality (p : P) : S.Forces Fin.elim0 p SetLanguage.extensionality := by
  simp only [Forces, SetLanguage.extensionality, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal]
  intro σ τ q hqp h
  apply S.eq_of_same_members
  intro ν r hrq
  exact ⟨fun hν => (h ν).1 r hrq hν, fun hν => (h ν).2 r hrq hν⟩

/-- The schema's Empty Set instance. -/
theorem forces_emptySet (p : P) : S.Forces Fin.elim0 p SetLanguage.emptySet := by
  simp only [Forces, SetLanguage.emptySet, SetLanguage.empty,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_neg S.atomic_regular, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro q hqp
  refine ⟨q, le_rfl, Name.empty, ?_⟩
  intro σ r hrq
  exact S.not_mem_empty r σ

/-- The schema's Foundation instance, uniformly at every condition. -/
theorem forces_foundation (p : P) : S.Forces Fin.elim0 p SetLanguage.foundation := by
  simp only [Forces, SetLanguage.foundation, SetLanguage.nonempty,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro σ q hqp hnonempty r hrq
  obtain ⟨s, hsr, ν, hν⟩ := hnonempty r hrq
  obtain ⟨t, hts, τ, hτ, hmin⟩ := S.minimal_member σ ν s hν
  refine ⟨t, hts.trans hsr, τ, hτ, ?_⟩
  intro ρ a hat hρτ b hba hρσ
  exact hmin ρ b (hba.trans hat) (S.atomic.mem_mono hba hρτ) hρσ

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames
universe u v w t

/-- Transport of the immediate membership graph preserves inclusions. -/
theorem mapConditions_mono (f : ZFSet.{u} → ZFSet.{u}) {σ τ : ZFSet.{u}} (h : σ ⊆ τ) :
    mapConditions f σ ⊆ mapConditions f τ := by
  intro z hz
  obtain ⟨ν, p, he, hz⟩ := mem_mapConditions_iff.mp hz
  exact mem_mapConditions_iff.mpr ⟨ν, p, h he, hz⟩

namespace SymmetricSystem
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- A small family of HS names with any predicate on its entry conditions. -/
noncomputable def collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) : ZFSet.{u} := by
  letI := S.small_conditions
  exact ZFSet.range (fun z : {z : ι × P // R z.1 z.2} =>
    ZFSet.pair (f z.val.1).raw (S.code z.val.2))

theorem mem_collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) (z : ZFSet.{u}) :
    z ∈ S.collectRaw f R ↔ ∃ i p, R i p ∧ ZFSet.pair (f i).raw (S.code p) = z := by
  let := S.small_conditions
  rw [collectRaw, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨i,p⟩,hR⟩,hz⟩
    exact ⟨i,p,hR,hz⟩
  · rintro ⟨i,p,hR,hz⟩
    exact ⟨⟨(i,p),hR⟩,hz⟩

theorem edge_collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) (ν c : ZFSet.{u}) :
    ZFSet.pair ν c ∈ S.collectRaw f R ↔
      ∃ i p, R i p ∧ (f i).raw = ν ∧ S.code p = c := by
  simp only [mem_collectRaw, ZFSet.pair_inj]

theorem isName_collectRaw {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) : IsName S.action.conditions (S.collectRaw f R) := by
  apply IsName.intro
  intro z hz
  obtain ⟨i,p,_,rfl⟩ := (S.mem_collectRaw f R z).mp hz
  exact ⟨(f i).raw, S.code p, rfl, S.code_mem p, (f i).isName⟩

noncomputable def collectName {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) : S.action.Name := ⟨S.collectRaw f R, S.isName_collectRaw f R⟩

/-- Permuting the entry family fixes its literal set of pairs. This lemma
contains no coherence or forcing premise. -/
theorem collect_HS {ι : Type t} [Small.{u} ι] (f : ι → S.Name) (R : ι → P → Prop)
    (H : Subgroup Γ) (hH : H ∈ S.filter)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) :
    ConditionAction.Name.HS S.filter (S.collectName f R) := by
  have hsub (g : Γ) (hg : g ∈ H) :
      (g • S.collectName f R).val ⊆ (S.collectName f R).val := by
    intro z hz
    obtain ⟨ν,c,he,rfl⟩ := mem_mapConditions_iff.mp hz
    obtain ⟨i,p,hR,rfl,rfl⟩ := (S.edge_collectRaw f R ν c).mp he
    obtain ⟨j,hj,hRj⟩ := permutes g hg i p hR
    apply (S.mem_collectRaw f R _).mpr
    refine ⟨j, S.move g p, hRj, ?_⟩
    rw [hj, Name.smul_val, S.actCode_code]
  apply ConditionAction.Name.hs_iff.mpr
  constructor
  · apply S.normal.2.1 H _ hH
    intro g hg
    apply ConditionAction.Name.ext
    apply le_antisymm (hsub g hg)
    have hi := mapConditions_mono (S.action.actCode g) (hsub g⁻¹ (H.inv_mem hg))
    change (g • (g⁻¹ • S.collectName f R)).val ⊆ (g • S.collectName f R).val at hi
    simpa only [smul_inv_smul] using hi
  · rintro τ ⟨c,hc⟩
    obtain ⟨i,p,_,hi,_⟩ := (S.edge_collectRaw f R τ.val c).mp hc
    have heq : (f i).val = τ := ConditionAction.Name.ext hi
    exact heq ▸ (f i).hs

/-- The collected name is packaged with the proved hereditary symmetry. -/
noncomputable def collect {ι : Type t} [Small.{u} ι] (f : ι → S.Name) (R : ι → P → Prop)
    (H : Subgroup Γ) (hH : H ∈ S.filter)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) : S.Name :=
  ⟨S.collectName f R, S.collect_HS f R H hH permutes⟩

/-- Finite tuples have a common subgroup in the given normal filter. -/
noncomputable def tupleStabilizer : {n : ℕ} → (Fin n → S.Name) → Subgroup Γ
  | 0, _ => ⊤
  | n+1, v => tupleStabilizer (fun i => v i.castSucc) ⊓ MulAction.stabilizer Γ (v (Fin.last n)).val

theorem tupleStabilizer_mem {n} (v : Fin n → S.Name) : S.tupleStabilizer v ∈ S.filter := by
  induction n with
  | zero => exact S.normal.1
  | succ n ih => exact S.normal.2.2.1 _ _ (ih _) (v (Fin.last n)).hs.symmetric

theorem mem_tupleStabilizer {n} (v : Fin n → S.Name) (g : Γ) :
    g ∈ S.tupleStabilizer v ↔ ∀ i, g • v i = v i := by
  induction n with
  | zero => simp [tupleStabilizer]
  | succ n ih =>
    simp only [tupleStabilizer, Subgroup.mem_inf, ih, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h,hl⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Subtype.ext hl
      · exact h j
    · intro h
      exact ⟨fun i => h i.castSucc, congrArg Subtype.val (h (Fin.last n))⟩

/-- Atomic symmetry, explicitly in the HS-name domain used by all quantifiers. -/
theorem mem_symmetry (g : Γ) (p : P) (σ τ : S.Name) :
    S.atomic.MemF p σ τ ↔ S.atomic.MemF (S.move g p) (g • σ) (g • τ) :=
  (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
    (S.move g) (S.actCode_code g) σ.raw τ.raw).1 p

theorem eq_symmetry (g : Γ) (p : P) (σ τ : S.Name) :
    S.atomic.EqF p σ τ ↔ S.atomic.EqF (S.move g p) (g • σ) (g • τ) :=
  (AtomicForcing.atomic_symmetry (S.action.actCode_injective g)
    (S.move g) (S.actCode_code g) σ.raw τ.raw).2 p

end SymmetricSystem
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

theorem forceFormula_close (hA : A.Regular) {n} (φ : Formula n) (p : P) :
    A.ForceFormula Fin.elim0 p φ.close ↔ ∀ v : Fin n → N, A.ForceFormula v p φ := by
  induction n with
  | zero =>
    exact ⟨fun h v => Subsingleton.elim (Fin.elim0 : Fin 0 → N) v ▸ h,
      fun h => h Fin.elim0⟩
  | succ n ih =>
    rw [Formula.close, ih]
    simp only [A.forceFormula_all hA]
    constructor
    · intro h v
      have hv : Fin.snoc (fun i => v i.castSucc) (v (Fin.last n)) = v := by
        funext i
        refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp
      exact hv ▸ h _ _
    · exact fun h v x => h (Fin.snoc v x)

end PartitionConsistency.ForcingQuotient.AtomicData

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_snoc_congr {n} (φ : Formula (n+1)) (v : Fin n → S.Name)
    {p : P} {σ τ : S.Name} (h : S.atomic.EqF p σ τ) :
    S.Forces (Fin.snoc v σ) p φ ↔ S.Forces (Fin.snoc v τ) p φ := by
  apply S.atomic.forceFormula_tuple_congr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h
  · simpa using S.atomic.eq_refl p (v j)

/-- Literal entry families are carried to literal entry families by the group. -/
theorem entry_permute (g : Γ) (σ : S.Name) (i : Edges σ.raw) :
    ∃ j : Edges (g • σ).raw, (g • σ).child j.property = g • σ.child i.property := by
  have he : ZFSet.pair (mapConditions (S.action.actCode g) i.val.1)
      (S.action.actCode g i.val.2) ∈ (g • σ).raw :=
    edge_mapConditions_iff.mpr ⟨i.val.1, i.val.2, i.property, rfl, rfl⟩
  refine ⟨⟨(mapConditions (S.action.actCode g) i.val.1, S.action.actCode g i.val.2),he⟩, ?_⟩
  apply Name.ext
  rfl

noncomputable def separationTest {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (i : Edges σ.raw) (p : P) : Prop :=
  S.atomic.MemF p (σ.child i.property) σ ∧ S.Forces (Fin.snoc v (σ.child i.property)) p φ

theorem separationTest_permute {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) :
    ∀ g ∈ MulAction.stabilizer Γ σ.val ⊓ S.tupleStabilizer v,
      ∀ i p, S.separationTest σ v φ i p → ∃ j,
      σ.child j.property = g • σ.child i.property ∧ S.separationTest σ v φ j (S.move g p) := by
  intro g hg i p hi
  have hσ : g • σ = σ := Subtype.ext hg.1
  have hv := (S.mem_tupleStabilizer v g).mp hg.2
  have he := S.entry_permute g σ i
  rw [hσ] at he
  obtain ⟨j,hj⟩ := he
  refine ⟨j,hj,?_,?_⟩
  · change S.atomic.MemF (S.move g p) (σ.child j.property) σ
    rw [hj]
    simpa only [hσ] using (S.mem_symmetry g p (σ.child i.property) σ).mp hi.1
  · change S.Forces (Fin.snoc v (σ.child j.property)) (S.move g p) φ
    rw [hj]
    have hvec : (fun k => g • Fin.snoc v (σ.child i.property) k) =
        Fin.snoc v (g • σ.child i.property) := by
      funext k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv]
    simpa only [hvec] using (S.forces_symmetry g φ (Fin.snoc v (σ.child i.property)) p).mp hi.2

/-- The Separation name for an arbitrary formula with an arbitrary finite
parameter tuple. Its entries are taken only from the original name's domain. -/
noncomputable def separate {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) : S.Name :=
  S.collect (fun i : Edges σ.raw => σ.child i.property) (S.separationTest σ v φ)
    (MulAction.stabilizer Γ σ.val ⊓ S.tupleStabilizer v)
    (S.normal.2.2.1 _ _ σ.hs.symmetric (S.tupleStabilizer_mem v))
    (S.separationTest_permute σ v φ)

theorem edge_separate {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+1))
    (ν : S.Name) (c : P) : ZFSet.pair ν.raw (S.code c) ∈ (S.separate σ v φ).raw ↔
      ∃ i : Edges σ.raw, σ.child i.property = ν ∧ S.separationTest σ v φ i c := by
  change ZFSet.pair ν.raw (S.code c) ∈
    S.collectRaw (fun i : Edges σ.raw => σ.child i.property) (S.separationTest σ v φ) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,p,hR,hν,hp⟩
    obtain rfl := S.code_injective hp
    exact ⟨i,Name.ext hν,hR⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,c,hR,congrArg Name.raw hi,rfl⟩

/-- Verification of the Separation name; quantified names are unrestricted
HS names, not a rank-bounded subclass. -/
theorem mem_separate {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+1))
    (ν : S.Name) (p : P) : S.atomic.MemF p ν (S.separate σ v φ) ↔
      S.atomic.MemF p ν σ ∧ S.Forces (Fin.snoc v ν) p φ := by
  constructor
  · intro h
    have hd : ∀ q, q ≤ p → ∃ r, r ≤ q ∧
        S.atomic.MemF r ν σ ∧ S.Forces (Fin.snoc v ν) r φ := by
      intro q hqp
      obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
      obtain ⟨i,hi,hm,hφ⟩ := (S.edge_separate σ v φ τ c).mp he
      change S.atomic.MemF c (σ.child i.property) σ at hm
      change S.Forces (Fin.snoc v (σ.child i.property)) c φ at hφ
      rw [hi] at hm hφ
      refine ⟨r,hrq,?_,?_⟩
      · exact (S.atomic.mem_congr heq (S.atomic.eq_refl r σ)).mpr (S.atomic.mem_mono hrc hm)
      · exact (S.forces_snoc_congr φ v heq).mpr (S.atomic.forceFormula_mono hrc hφ)
    exact ⟨S.atomic_regular.2 p ν σ (fun q hq => by
      obtain ⟨r,hrq,hm,_⟩ := hd q hq
      exact ⟨r,hrq,hm⟩), S.atomic.forceFormula_of_dense S.atomic_regular (fun q hq => by
      obtain ⟨r,hrq,_,hφ⟩ := hd q hq
      exact ⟨r,hrq,hφ⟩)⟩
  · rintro ⟨hm,hφ⟩
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp hm) q hqp
    let i : Edges σ.raw := ⟨(τ.raw, S.code c), he⟩
    have hi : σ.child i.property = τ := Name.ext rfl
    have ht : S.separationTest σ v φ i r := by
      change S.atomic.MemF r (σ.child i.property) σ ∧ _
      rw [hi]
      exact ⟨S.mem_of_edge he hrc, (S.forces_snoc_congr φ v heq).mp
        (S.atomic.forceFormula_mono (hrq.trans hqp) hφ)⟩
    exact ⟨r,hrq,τ,r,(S.edge_separate σ v φ τ r).mpr ⟨i,hi,ht⟩,le_rfl,heq⟩

/-- Every individual instance of full Separation is forced. There is no bound
on the finite syntax, parameters, or ranks in this theorem. -/
theorem forces_separation {n} (φ : Formula (n+1)) (p : P) :
    S.Forces Fin.elim0 p (SetLanguage.separation φ) := by
  unfold SetLanguage.separation
  rw [Forces, S.atomic.forceFormula_close S.atomic_regular]
  simp only [S.atomic.forceFormula_all S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,
    S.atomic.forceFormula_rename S.atomic_regular, Fin.snoc_last, Fin.snoc_castSucc]
  intro v σ q hqp
  refine ⟨q,le_rfl,S.separate σ v φ,?_⟩
  intro ν
  have hv : Fin.snoc (Fin.snoc (Fin.snoc v σ) (S.separate σ v φ)) ν ∘
      Fin.lastCases (Fin.last (n + 2)) (fun i => i.castSucc.castSucc.castSucc) =
        Fin.snoc v ν := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hv]
  exact ⟨fun r _ => (S.mem_separate σ v φ ν r).mp,
    fun r _ => (S.mem_separate σ v φ ν r).mpr⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
