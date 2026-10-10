import OAI.SetTheory.PartitionPrinciple.Definability.UnionEntryFormula

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
open scoped ZFSet
universe u
variable {P : Type u} {s : Presentation P}

def grandchildrenBound (τ : Name s) : ZFSet.{u} := ⋃₀ (⋃₀ (⋃₀ (⋃₀ (⋃₀ τ.val))))

theorem grandchild_mem_bound {σ ν τ : Name s} {r q : P}
    (outer : Entry ν τ r) (inner : Entry σ ν q) : σ.val ∈ grandchildrenBound τ := by
  have h₁ : ({ν.val} : ZFSet.{u}) ∈ ⋃₀ τ.val :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair ν.val (s.encode r), outer, ZFSet.mem_pair.2 (Or.inl rfl)⟩
  have h₂ : ν.val ∈ ⋃₀ (⋃₀ τ.val) :=
    ZFSet.mem_sUnion.2 ⟨{ν.val}, h₁, ZFSet.mem_singleton.2 rfl⟩
  have h₃ : ZFSet.pair σ.val (s.encode q) ∈ ⋃₀ (⋃₀ (⋃₀ τ.val)) :=
    ZFSet.mem_sUnion.2 ⟨ν.val, h₂, inner⟩
  have h₄ : ({σ.val} : ZFSet.{u}) ∈ ⋃₀ (⋃₀ (⋃₀ (⋃₀ τ.val))) :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair σ.val (s.encode q), h₃, ZFSet.mem_pair.2 (Or.inl rfl)⟩
  exact ZFSet.mem_sUnion.2 ⟨{σ.val}, h₄, ZFSet.mem_singleton.2 rfl⟩

theorem isName_of_pair_mem (τ : Name s) (x : ZFSet.{u}) (p : P)
    (entry : ZFSet.pair x (s.encode p) ∈ τ.val) : IsName s x := by
  have property := τ.property
  cases property with
  | mk _ children => exact children x p entry

theorem unionName_subset_bound [Preorder P] (τ : Name s) (C : ZFSet.{u})
    (bound : ∀ x ∈ grandchildrenBound τ, ∀ y ∈ s.carrier, ZFSet.pair x y ∈ C) :
    (unionName τ).val ⊆ C := by
  intro z hz
  obtain ⟨σ, p, rfl⟩ := entries_cover (unionName τ) hz
  obtain ⟨ν, r, q, outer, inner, _, _⟩ := (entry_unionName τ σ p).1 hz
  exact bound σ.val (grandchild_mem_bound outer inner) (s.encode p) (s.encode_mem p)

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem grandchildrenBound_mem (unions : Realize M.sets SetFormula.union Fin.elim0)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) : Name.grandchildrenBound τ ∈ M.sets :=
  M.union_mem unions (M.union_mem unions (M.union_mem unions (M.union_mem unions (M.union_mem unions hτ))))

theorem exists_unionName_bound [Preorder P]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) :
    ∃ C ∈ M.sets, (Name.unionName τ).val ⊆ C := by
  obtain ⟨C, hC, bound⟩ := M.exists_pair_bound pairing unions powers
    (M.grandchildrenBound_mem s unions hτ) carrier
  exact ⟨C, hC, Name.unionName_subset_bound τ C bound⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def conditionOrder : ZFSet.{u} := (s.product s).subset (fun z => z.1 ≤ z.2)

theorem pair_mem_conditionOrder (p q : P) :
    ZFSet.pair (s.encode p) (s.encode q) ∈ s.conditionOrder ↔ p ≤ q :=
  (s.product s).encode_mem_subset (fun z => z.1 ≤ z.2) (p, q)

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def unionEntryParams (τ : Name s) : Fin 3 → ZFSet.{u} :=
  extend τ.val (extend s.carrier (extend s.conditionOrder Fin.elim0))

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem unionEntryParams_mem (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) :
    ∀ i, Name.unionEntryParams τ i ∈ M.sets := by
  intro i
  refine Fin.cases hτ (fun j => ?_) i
  refine Fin.cases carrier (fun k => ?_) j
  exact Fin.cases order (fun l => Fin.elim0 l) k

theorem unionEntry_iff_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) {z : ZFSet.{u}} (hz : z ∈ M.sets) :
    Realize M.sets unionEntryFormula (extend z (Name.unionEntryParams τ)) ↔
      z ∈ (Name.unionName τ).val := by
  have members : ∀ i, extend z (Name.unionEntryParams τ) i ∈ M.sets :=
    fun i => Fin.cases hz (M.unionEntryParams_mem s carrier order hτ) i
  rw [M.realize_unionEntryFormula pairing _ members]
  change (∃ x ∈ M.sets, ∃ p ∈ M.sets, ∃ ν ∈ M.sets, ∃ r ∈ M.sets, ∃ q ∈ M.sets,
    z = ZFSet.pair x p ∧ p ∈ s.carrier ∧ r ∈ s.carrier ∧ q ∈ s.carrier ∧
    ZFSet.pair ν r ∈ τ.val ∧ ZFSet.pair x q ∈ ν ∧
    ZFSet.pair p r ∈ s.conditionOrder ∧ ZFSet.pair p q ∈ s.conditionOrder) ↔ _
  constructor
  · rintro ⟨x, _, pc, _, v, _, rc, _, qc, _, eq, hp, hr, hq, outer, inner, pr, pq⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier pc).1 hp
    obtain ⟨r, rfl⟩ := (s.mem_carrier rc).1 hr
    obtain ⟨q, rfl⟩ := (s.mem_carrier qc).1 hq
    let ν : Name s := ⟨v, Name.isName_of_pair_mem τ v r outer⟩
    let σ : Name s := ⟨x, Name.isName_of_pair_mem ν x q inner⟩
    rw [eq]
    change Name.Entry σ (Name.unionName τ) p
    exact (Name.entry_unionName τ σ p).2
      ⟨ν, r, q, outer, inner, (s.pair_mem_conditionOrder p r).1 pr,
        (s.pair_mem_conditionOrder p q).1 pq⟩
  · intro member
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.unionName τ) member
    obtain ⟨ν, r, q, outer, inner, pr, pq⟩ := (Name.entry_unionName τ σ p).1 member
    have hν := (M.nameDomain s).children hτ outer
    have hσ := (M.nameDomain s).children hν inner
    exact ⟨σ.val, hσ, s.encode p, M.transitive carrier (s.encode_mem p),
      ν.val, hν, s.encode r, M.transitive carrier (s.encode_mem r),
      s.encode q, M.transitive carrier (s.encode_mem q), rfl,
      s.encode_mem p, s.encode_mem r, s.encode_mem q, outer, inner,
      (s.pair_mem_conditionOrder p r).2 pr, (s.pair_mem_conditionOrder p q).2 pq⟩

theorem unionName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) :
    Name.unionName τ ∈ (M.nameDomain s).names := by
  obtain ⟨C, hC, bound⟩ := M.exists_unionName_bound s pairing unions powers carrier hτ
  have selected := M.separation_mem separation unionEntryFormula (Name.unionEntryParams τ)
    (M.unionEntryParams_mem s carrier order hτ) hC
  have eq : ZFSet.sep (fun z => Realize M.sets unionEntryFormula
      (extend z (Name.unionEntryParams τ))) C = (Name.unionName τ).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, formula⟩
      exact (M.unionEntry_iff_mem s pairing carrier order hτ (M.transitive hC hz)).1 formula
    · intro hz
      exact ⟨bound hz,
        (M.unionEntry_iff_mem s pairing carrier order hτ (M.transitive hC (bound hz))).2 hz⟩
  change (Name.unionName τ).val ∈ M.sets
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)

theorem symmetric_union {G : Type v} [Group G]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p})
      SetFormula.union Fin.elim0 :=
  realize_symmetric_union a (M.nameDomain s) F
    (fun _ hτ => M.unionName_mem s pairing unions powers separation carrier order hτ) H

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.SetFormula

def allConditions {n : Nat} (carrier : Fin n) (φ : SetFormula (n + 1)) : SetFormula n :=
  .all (imp (.mem 0 carrier.succ) φ)

def exConditions {n : Nat} (carrier : Fin n) (φ : SetFormula (n + 1)) : SetFormula n :=
  ex (.conj (.mem 0 carrier.succ) φ)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_allConditions {n : Nat} (c : Fin n) (φ : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (carrier : s.carrier ∈ M.sets) (code : env c = s.carrier) :
    Realize M.sets (allConditions c φ) env ↔
      ∀ p : P, Realize M.sets φ (extend (s.encode p) env) := by
  simp only [allConditions, Realize, realize_imp]
  change (∀ x ∈ M.sets, x ∈ env c → Realize M.sets φ (extend x env)) ↔ _
  rw [code]
  constructor
  · intro h p
    exact h (s.encode p) (M.transitive carrier (s.encode_mem p)) (s.encode_mem p)
  · intro h x _ hx
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact h p

theorem realize_exConditions {n : Nat} (c : Fin n) (φ : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (carrier : s.carrier ∈ M.sets) (code : env c = s.carrier) :
    Realize M.sets (exConditions c φ) env ↔
      ∃ p : P, Realize M.sets φ (extend (s.encode p) env) := by
  simp only [exConditions, realize_ex]
  change (∃ x ∈ M.sets, x ∈ env c ∧ Realize M.sets φ (extend x env)) ↔ _
  rw [code]
  constructor
  · rintro ⟨x, _, hx, h⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨p, h⟩
  · rintro ⟨p, h⟩
    exact ⟨s.encode p, M.transitive carrier (s.encode_mem p), s.encode_mem p, h⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
