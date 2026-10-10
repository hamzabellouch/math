import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricNames

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The ordering on literal condition codes, false outside those codes. -/
def codeOrder (a b : ZFSet.{u}) : Prop :=
  ∃ p q : P, S.code p = a ∧ S.code q = b ∧ p ≤ q

theorem codeOrder_codes (p q : P) : S.codeOrder (S.code p) (S.code q) ↔ p ≤ q := by
  constructor
  · rintro ⟨p',q',hp,hq,h⟩
    obtain rfl := S.code_injective hp
    obtain rfl := S.code_injective hq
    exact h
  · exact fun h => ⟨p,q,rfl,rfl,h⟩

theorem codeOrder_symmetry (g : Γ) (a b : ZFSet.{u}) :
    S.codeOrder (S.action.actCode g a) (S.action.actCode g b) ↔ S.codeOrder a b := by
  have forward (g : Γ) (a b : ZFSet.{u}) (h : S.codeOrder a b) :
      S.codeOrder (S.action.actCode g a) (S.action.actCode g b) := by
    obtain ⟨p,q,rfl,rfl,h⟩ := h
    exact ⟨S.move g p, S.move g q, (S.actCode_code g p).symm,
      (S.actCode_code g q).symm, (S.move g).monotone h⟩
  exact ⟨fun h => by simpa only [S.action.actCode_inv_actCode] using forward g⁻¹ _ _ h,
    forward g a b⟩

namespace Name
variable {S}

noncomputable def union (σ : S.Name) : S.Name :=
  ⟨ConditionAction.Name.union S.codeOrder σ.val,
    ConditionAction.Name.union_HS S.normal S.codeOrder S.codeOrder_symmetry σ.hs⟩

end Name

theorem edge_union (σ ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ σ.union.raw ↔ ∃ (χ : S.Name) (c d : P),
    ZFSet.pair χ.raw (S.code c) ∈ σ.raw ∧
    ZFSet.pair ν.raw (S.code d) ∈ χ.raw ∧ p ≤ c ∧ p ≤ d := by
  change ZFSet.pair ν.raw (S.code p) ∈ unionName S.action.conditions S.codeOrder σ.raw ↔ _
  rw [edge_unionName_iff]
  constructor
  · rintro ⟨χ,c',d',hc,hd,_,hp,hq⟩
    obtain ⟨p',c,hp',rfl,hpc⟩ := hp
    obtain rfl := S.code_injective hp'
    obtain ⟨p',d,hp',rfl,hpd⟩ := hq
    obtain rfl := S.code_injective hp'
    exact ⟨σ.child hc,c,d,hc,hd,hpc,hpd⟩
  · rintro ⟨χ,c,d,hc,hd,hpc,hpd⟩
    exact ⟨χ.raw,S.code c,S.code d,hc,hd,S.code_mem p,
      (S.codeOrder_codes p c).mpr hpc,(S.codeOrder_codes p d).mpr hpd⟩

theorem mem_union (σ ν : S.Name) (p : P) : S.atomic.MemF p ν σ.union ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ χ : S.Name,
      S.atomic.MemF r χ σ ∧ S.atomic.MemF r ν χ := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨χ,a,b,ha,hb,hca,hcb⟩ := (S.edge_union σ τ c).mp he
    refine ⟨r,hrq,χ,S.mem_of_edge ha (hrc.trans hca),?_⟩
    exact (S.atomic.mem_congr heq (S.atomic.eq_refl r χ)).mpr
      (S.mem_of_edge hb (hrc.trans hcb))
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,χ,hχ,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,hτ,hsc,heq⟩ := (S.mem_iff.mp hχ) r le_rfl
    have hντ : S.atomic.MemF s ν τ :=
      (S.atomic.mem_congr (S.atomic.eq_refl s ν) heq).mp (S.atomic.mem_mono hsr hν)
    obtain ⟨t,hts,η,d,hη,htd,heq'⟩ := (S.mem_iff.mp hντ) s le_rfl
    exact ⟨t,hts.trans (hsr.trans hrq),η,t,
      (S.edge_union σ η t).mpr ⟨τ,c,d,hτ,hη,hts.trans hsc,htd⟩,le_rfl,heq'⟩

/-- The Union axiom for arbitrary HS input names. -/
theorem forces_union (p : P) : S.Forces Fin.elim0 p SetLanguage.union := by
  simp only [Forces, SetLanguage.union, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_ex, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro σ q hqp
  refine ⟨q,le_rfl,σ.union,?_⟩
  intro ν
  exact ⟨fun r _ => (S.mem_union σ ν r).mp, fun r _ => (S.mem_union σ ν r).mpr⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

@[simp] theorem code_top_fixed (g : Γ) : S.action.actCode g (S.code ⊤) = S.code ⊤ := by
  rw [S.actCode_code, (S.move g).map_top]

namespace Name
variable {S}

noncomputable def pair (σ τ : S.Name) : S.Name :=
  ⟨ConditionAction.Name.pair (S.code_mem ⊤) σ.val τ.val,
    ConditionAction.Name.pair_HS S.normal (S.code_mem ⊤) S.code_top_fixed σ.hs τ.hs⟩

noncomputable def check (x : ZFSet.{u}) : S.Name :=
  ⟨ConditionAction.Name.check (S.code_mem ⊤) x,
    ConditionAction.Name.check_HS S.normal.1 (S.code_mem ⊤) S.code_top_fixed x⟩

@[simp] theorem check_raw (x : ZFSet.{u}) : (check (S := S) x).raw = checkName (S.code ⊤) x := rfl

@[simp] theorem check_empty : check (S := S) ∅ = empty := by
  apply ext
  apply ZFSet.ext
  intro z
  simp [check_raw, mem_checkName_iff, empty_val]

end Name

theorem edge_pair (σ τ ν : S.Name) (c : P) :
    ZFSet.pair ν.raw (S.code c) ∈ (σ.pair τ).raw ↔ (ν = σ ∨ ν = τ) ∧ c = ⊤ := by
  change ZFSet.pair ν.raw (S.code c) ∈ pairName (S.code ⊤) σ.raw τ.raw ↔ _
  rw [edge_pairName_iff]
  have hinj : Function.Injective (Name.raw : S.Name → ZFSet.{u}) := fun _ _ => Name.ext
  simp only [hinj.eq_iff, S.code_injective.eq_iff]

theorem mem_pair (σ τ ν : S.Name) (p : P) : S.atomic.MemF p ν (σ.pair τ) ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ (S.atomic.EqF r ν σ ∨ S.atomic.EqF r ν τ) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,η,c,he,_,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨hη | hη,_⟩ := (S.edge_pair σ τ η c).mp he
    · exact ⟨r,hrq,Or.inl (hη ▸ heq)⟩
    · exact ⟨r,hrq,Or.inr (hη ▸ heq)⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,heq | heq⟩ := h q hqp
    · exact ⟨r,hrq,σ,⊤,(S.edge_pair σ τ σ ⊤).mpr ⟨Or.inl rfl,rfl⟩,le_top,heq⟩
    · exact ⟨r,hrq,τ,⊤,(S.edge_pair σ τ τ ⊤).mpr ⟨Or.inr rfl,rfl⟩,le_top,heq⟩

/-- The Pairing axiom, with the standard largest-condition name. -/
theorem forces_pairing (p : P) : S.Forces Fin.elim0 p SetLanguage.pairing := by
  simp only [Forces, SetLanguage.pairing, SetLanguage.unorderedPair, Formula.iff,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_disj, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal]
  intro σ τ q hqp
  refine ⟨q,le_rfl,σ.pair τ,?_⟩
  intro ν
  exact ⟨fun r _ => (S.mem_pair σ τ ν r).mp, fun r _ => (S.mem_pair σ τ ν r).mpr⟩

theorem mem_check (x : ZFSet.{u}) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (Name.check x) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y ∈ x, S.atomic.EqF r ν (Name.check y) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,_,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨y,hy,hτ,_⟩ := edge_checkName_iff.mp he
    have hyτ : Name.check y = τ := Name.ext hτ
    exact ⟨r,hrq,y,hy,hyτ ▸ heq⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,y,hy,heq⟩ := h q hqp
    exact ⟨r,hrq,Name.check y,⊤,edge_checkName_iff.mpr ⟨y,hy,rfl,rfl⟩,le_top,heq⟩

theorem check_mem_of_mem {x y : ZFSet.{u}} (h : y ∈ x) (p : P) :
    S.atomic.MemF p (Name.check y) (Name.check x) :=
  S.mem_of_edge (edge_checkName_iff.mpr ⟨y,h,rfl,rfl⟩) le_top

/-- The check name of a ground successor is its internal successor. -/
theorem check_successor (x : ZFSet.{u}) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (Name.check (insert x x)) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧
        (S.atomic.MemF r ν (Name.check x) ∨ S.atomic.EqF r ν (Name.check x)) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,y,hy,heq⟩ := (S.mem_check _ ν p).mp h q hqp
    rcases ZFSet.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨r,hrq,Or.inr heq⟩
    · exact ⟨r,hrq,Or.inl ((S.atomic.mem_congr heq (S.atomic.eq_refl r (Name.check x))).mpr
        (S.check_mem_of_mem hy r))⟩
  · intro h
    apply (S.mem_check _ ν p).mpr
    intro q hqp
    obtain ⟨r,hrq,hm | he⟩ := h q hqp
    · obtain ⟨s,hsr,y,hy,heq⟩ := (S.mem_check x ν r).mp hm r le_rfl
      exact ⟨s,hsr.trans hrq,y,ZFSet.mem_insert_iff.mpr (Or.inr hy),heq⟩
    · exact ⟨r,hrq,x,ZFSet.mem_insert_iff.mpr (Or.inl rfl),he⟩

/-- The Infinity witness is the literal check-name of the ground natural numbers. -/
theorem forces_infinity (p : P) : S.Forces Fin.elim0 p SetLanguage.infinity := by
  simp only [Forces, SetLanguage.infinity, SetLanguage.empty, SetLanguage.successor,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_conj, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_disj,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal,
    ForcingQuotient.AtomicData.forceFormula_bot]
  intro q hqp
  refine ⟨q,le_rfl,Name.check ZFSet.omega,?_,?_⟩
  · intro r hrq
    refine ⟨r,le_rfl,Name.check ∅,S.check_mem_of_mem ZFSet.omega_zero r,?_⟩
    intro ν t htr ht
    change S.atomic.MemF t ν (Name.check ∅) at ht
    exact S.not_mem_empty t ν (by simpa only [Name.check_empty] using ht)
  · intro ν r hrq hν t htr
    obtain ⟨s,hst,x,hx,heq⟩ := (S.mem_check ZFSet.omega ν r).mp hν t htr
    refine ⟨s,hst,Name.check (insert x x),S.check_mem_of_mem (ZFSet.omega_succ hx) s,?_⟩
    intro ρ
    constructor
    · intro a has ha b hba
      obtain ⟨c,hcb,hc | hc⟩ := (S.check_successor x ρ a).mp ha b hba
      · exact ⟨c,hcb,Or.inl ((S.atomic.mem_congr (S.atomic.eq_refl c ρ)
          (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq)).mpr hc)⟩
      · exact ⟨c,hcb,Or.inr (S.atomic.eq_trans hc
          (S.atomic.eq_symm (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq)))⟩
    · intro a has ha
      apply (S.check_successor x ρ a).mpr
      intro b hba
      obtain ⟨c,hcb,hc | hc⟩ := ha b hba
      · exact ⟨c,hcb,Or.inl ((S.atomic.mem_congr (S.atomic.eq_refl c ρ)
          (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq)).mp hc)⟩
      · exact ⟨c,hcb,Or.inr (S.atomic.eq_trans hc
          (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq))⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The same entry-permutation argument records the particular fixing subgroup,
not merely that some subgroup in the filter fixes the collected name. -/
theorem collectName_fixed {ι : Type t} [Small.{u} ι] (f : ι → S.Name) (R : ι → P → Prop)
    (H : Subgroup Γ)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) (g : Γ) (hg : g ∈ H) :
    g • S.collectName f R = S.collectName f R := by
  have hsub (g : Γ) (hg : g ∈ H) :
      (g • S.collectName f R).val ⊆ (S.collectName f R).val := by
    intro z hz
    obtain ⟨ν,c,he,rfl⟩ := mem_mapConditions_iff.mp hz
    obtain ⟨i,p,hR,rfl,rfl⟩ := (S.edge_collectRaw f R ν c).mp he
    obtain ⟨j,hj,hRj⟩ := permutes g hg i p hR
    apply (S.mem_collectRaw f R _).mpr
    refine ⟨j, S.move g p, hRj, ?_⟩
    rw [hj, Name.smul_val, S.actCode_code]
  apply ConditionAction.Name.ext
  apply le_antisymm (hsub g hg)
  have hi := mapConditions_mono (S.action.actCode g) (hsub g⁻¹ (H.inv_mem hg))
  change (g • (g⁻¹ • S.collectName f R)).val ⊆ (g • S.collectName f R).val at hi
  simpa only [smul_inv_smul] using hi

def SubsetF (p : P) (σ τ : S.Name) : Prop :=
  ∀ ν : S.Name, ∀ q, q ≤ p → S.atomic.MemF q ν σ → S.atomic.MemF q ν τ

theorem forces_subset {n} (v : Fin n → S.Name) (p : P) (a b : Fin n) :
    S.Forces v p (SetLanguage.subset a b) ↔ S.SubsetF p (v a) (v b) := by
  simp only [Forces, SetLanguage.subset, S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular, S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_mem]
  rfl

theorem subset_mono {p q : P} {σ τ : S.Name} (h : q ≤ p) (hsub : S.SubsetF p σ τ) :
    S.SubsetF q σ τ := fun ν r hr => hsub ν r (hr.trans h)

theorem subset_of_dense {p : P} {σ τ : S.Name}
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ S.SubsetF r σ τ) : S.SubsetF p σ τ := by
  intro ν q hqp hν
  apply S.atomic_regular.2 q ν τ
  intro r hrq
  obtain ⟨s,hsr,hs⟩ := h r (hrq.trans hqp)
  exact ⟨s,hsr,hs ν s le_rfl (S.atomic.mem_mono (hsr.trans hrq) hν)⟩

theorem subset_congr {p : P} {σ σ' τ τ' : S.Name}
    (hσ : S.atomic.EqF p σ σ') (hτ : S.atomic.EqF p τ τ') :
    S.SubsetF p σ τ ↔ S.SubsetF p σ' τ' := by
  constructor
  · intro h ν q hqp hν
    exact (S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hτ)).mp
      (h ν q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hσ)).mpr hν))
  · intro h ν q hqp hν
    exact (S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hτ)).mpr
      (h ν q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hσ)).mp hν))

theorem subset_symmetry (g : Γ) (p : P) (σ τ : S.Name) :
    S.SubsetF p σ τ ↔ S.SubsetF (S.move g p) (g • σ) (g • τ) := by
  have h := S.forces_symmetry g (SetLanguage.subset 0 1) ![σ,τ] p
  simpa only [S.forces_subset, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- All possible immediate pairs over the domain of a particular name form a
set. This is a bound on normalizations of subsets, not on all HS names. -/
noncomputable def subsetBound (σ : S.Name) : ZFSet.{u} :=
  S.collectRaw (fun i : Edges σ.raw => σ.child i.property) (fun _ _ => True)

theorem subsetBound_fixed (σ : S.Name) (g : Γ) (hg : g • σ = σ) :
    mapConditions (S.action.actCode g) (S.subsetBound σ) = S.subsetBound σ := by
  have hp : ∀ h ∈ MulAction.stabilizer Γ σ.val, ∀ (i : Edges σ.raw) (p : P),
      True → ∃ j : Edges σ.raw, σ.child j.property = h • σ.child i.property ∧ True := by
    intro h hh i p _
    have ht : h • σ = σ := Subtype.ext hh
    have he := S.entry_permute h σ i
    rw [ht] at he
    obtain ⟨j,hj⟩ := he
    exact ⟨j,hj,True.intro⟩
  exact congrArg (fun ν : S.action.Name => ν.val)
    (S.collectName_fixed (fun i : Edges σ.raw => σ.child i.property) (fun _ _ => True)
      (MulAction.stabilizer Γ σ.val) hp g (congrArg Subtype.val hg))

/-- The actual HS candidates inside the small set of normalization codes. -/
def PowerCandidate (σ : S.Name) := {ν : S.Name // ν.raw ⊆ S.subsetBound σ}

instance (σ : S.Name) : Small.{u} (S.PowerCandidate σ) := by
  apply small_of_injective (f := fun ν : S.PowerCandidate σ =>
    (⟨ν.val.raw,ZFSet.mem_powerset.mpr ν.property⟩ : (S.subsetBound σ).powerset))
  intro ν τ h
  exact Subtype.ext (Name.ext (congrArg Subtype.val h))

noncomputable def normalize (σ ν : S.Name) : S.Name :=
  S.separate σ ![ν] (.mem 1 0)

theorem mem_normalize (σ ν τ : S.Name) (p : P) :
    S.atomic.MemF p τ (S.normalize σ ν) ↔ S.atomic.MemF p τ σ ∧ S.atomic.MemF p τ ν :=
  S.mem_separate σ ![ν] (.mem 1 0) τ p

theorem normalize_bounded (σ ν : S.Name) : (S.normalize σ ν).raw ⊆ S.subsetBound σ := by
  intro z hz
  change z ∈ S.collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (S.separationTest σ ![ν] (.mem 1 0)) at hz
  obtain ⟨i,p,_,he⟩ := (S.mem_collectRaw _ _ _).mp hz
  exact (S.mem_collectRaw _ _ _).mpr ⟨i,p,True.intro,he⟩

theorem normalize_eq {p : P} (σ ν : S.Name) (h : S.SubsetF p ν σ) :
    S.atomic.EqF p ν (S.normalize σ ν) := by
  apply S.eq_of_same_members
  intro τ q hqp
  rw [S.mem_normalize]
  exact ⟨fun hτ => ⟨h τ q hqp hτ,hτ⟩, And.right⟩

theorem powerCandidate_permute (σ : S.Name) :
    ∀ g ∈ MulAction.stabilizer Γ σ.val, ∀ (i : S.PowerCandidate σ) p,
      S.SubsetF p i.val σ → ∃ j : S.PowerCandidate σ,
        j.val = g • i.val ∧ S.SubsetF (S.move g p) j.val σ := by
  intro g hg i p hi
  have hσ : g • σ = σ := Subtype.ext hg
  have hbound : (g • i.val).raw ⊆ S.subsetBound σ := by
    rw [Name.smul_val]
    have hb := mapConditions_mono (S.action.actCode g) i.property
    simpa only [S.subsetBound_fixed σ g hσ] using hb
  refine ⟨⟨g • i.val,hbound⟩,rfl,?_⟩
  simpa only [hσ] using (S.subset_symmetry g p i.val σ).mp hi

/-- The power-set name uses every HS normalized subset candidate and the
conditions which force that candidate to be a subset. -/
noncomputable def power (σ : S.Name) : S.Name :=
  S.collect (fun i : S.PowerCandidate σ => i.val) (fun i p => S.SubsetF p i.val σ)
    (MulAction.stabilizer Γ σ.val) σ.hs.symmetric (S.powerCandidate_permute σ)

theorem edge_power (σ ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ (S.power σ).raw ↔
      ν.raw ⊆ S.subsetBound σ ∧ S.SubsetF p ν σ := by
  change ZFSet.pair ν.raw (S.code p) ∈
    S.collectRaw (fun i : S.PowerCandidate σ => i.val) (fun i p => S.SubsetF p i.val σ) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,q,hi,hν,hq⟩
    obtain rfl := S.code_injective hq
    have heq : i.val = ν := Name.ext hν
    exact ⟨hν ▸ i.property,heq ▸ hi⟩
  · rintro ⟨hb,hs⟩
    exact ⟨⟨ν,hb⟩,p,hs,rfl,rfl⟩

theorem mem_power (σ ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.power σ) ↔ S.SubsetF p ν σ := by
  constructor
  · intro h
    apply S.subset_of_dense
    intro q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
    have hτ := S.subset_mono hrc ((S.edge_power σ τ c).mp he).2
    exact ⟨r,hrq,(S.subset_congr heq (S.atomic.eq_refl r σ)).mpr hτ⟩
  · intro h
    have heq := S.normalize_eq σ ν h
    have hs : S.SubsetF p (S.normalize σ ν) σ :=
      (S.subset_congr heq (S.atomic.eq_refl p σ)).mp h
    exact (S.atomic.mem_congr heq (S.atomic.eq_refl p (S.power σ))).mpr
      (S.mem_of_edge ((S.edge_power σ (S.normalize σ ν) p).mpr
        ⟨S.normalize_bounded σ ν,hs⟩) le_rfl)

/-- Power Set with quantification over every HS name, including subsets at
arbitrarily high name ranks. -/
theorem forces_powerSet (p : P) : S.Forces Fin.elim0 p SetLanguage.powerSet := by
  simp only [Forces, SetLanguage.powerSet, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_ex, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro σ q hqp
  refine ⟨q,le_rfl,S.power σ,?_⟩
  intro ν
  simp only [S.forces_subset]
  exact ⟨fun r _ => (S.mem_power σ ν r).mp, fun r _ => (S.mem_power σ ν r).mpr⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
