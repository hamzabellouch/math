import Mathlib.SetTheory.ZFC.Rank
import OAI.SetTheory.PartitionPrinciple.Definability.SetPresentations
import OAI.SetTheory.PartitionPrinciple.Forcing.GenericPartialFunctions

namespace OAI


namespace PartitionPilot.Forcing

section

open SetRealization
universe u v
variable {P : Type u}

inductive IsName (s : Presentation P) : ZFSet.{u} → Prop
  | mk {x} : (∀ z ∈ x, ∃ y p, z = ZFSet.pair y (s.encode p)) →
      (∀ y p, ZFSet.pair y (s.encode p) ∈ x → IsName s y) → IsName s x

def Name (s : Presentation P) := {x : ZFSet.{u} // IsName s x}

namespace Name
variable {s : Presentation P}

def Entry (σ τ : Name s) (p : P) : Prop :=
  ZFSet.pair σ.val (s.encode p) ∈ τ.val

theorem entries_cover (τ : Name s) {z : ZFSet.{u}} (hz : z ∈ τ.val) :
    ∃ σ : Name s, ∃ p, z = ZFSet.pair σ.val (s.encode p) := by
  obtain ⟨x, hx⟩ := τ
  cases hx with
  | mk h children =>
    obtain ⟨y, p, eq⟩ := h z hz
    exact ⟨⟨y, children y p (eq ▸ hz)⟩, p, eq⟩

theorem ext {τ ν : Name s} (h : ∀ σ p, Entry σ τ p ↔ Entry σ ν p) : τ = ν := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, rfl⟩ := entries_cover τ hz
    exact (h σ p).1 hz
  · intro hz
    obtain ⟨σ, p, rfl⟩ := entries_cover ν hz
    exact (h σ p).2 hz

theorem entry_rank_lt {σ τ : Name s} {p : P} (h : Entry σ τ p) :
    ZFSet.rank σ.val < ZFSet.rank τ.val := by
  have h₁ : σ.val ∈ ({σ.val} : ZFSet) := ZFSet.mem_singleton.2 rfl
  have h₂ : ({σ.val} : ZFSet) ∈ ZFSet.pair σ.val (s.encode p) := by
    exact ZFSet.mem_pair.2 (Or.inl rfl)
  exact (ZFSet.rank_lt_of_mem h₁).trans
    ((ZFSet.rank_lt_of_mem h₂).trans (ZFSet.rank_lt_of_mem h))

theorem inductionOn {motive : Name s → Prop} (τ : Name s)
    (step : ∀ ν, (∀ σ p, Entry σ ν p → motive σ) → motive ν) : motive τ := by
  apply (InvImage.wf (fun ν : Name s => ZFSet.rank ν.val) wellFounded_lt).induction τ
  intro ν ih
  exact step ν (fun σ p h => ih σ (entry_rank_lt h))

def Entries (τ : Name s) := {a : Name s × P // Entry a.1 τ a.2}

instance entries_small (τ : Name s) : Small.{u} (Entries τ) := by
  let f : Entries τ → τ.val :=
    fun a => ⟨ZFSet.pair a.val.1.val (s.encode a.val.2), a.property⟩
  apply small_of_injective (f := f)
  intro a b eq
  have parts := ZFSet.pair_inj.1 (congrArg Subtype.val eq)
  apply Subtype.ext
  exact Prod.ext (Subtype.ext parts.1) (s.injective parts.2)

noncomputable def assemble {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) : Name s := by
  refine ⟨ZFSet.range (fun i => ZFSet.pair (names i).val (s.encode (conditions i))),
    IsName.mk ?_ ?_⟩
  · intro z hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hz
    exact ⟨(names i).val, conditions i, rfl⟩
  · intro y p hp
    obtain ⟨i, eq⟩ := ZFSet.mem_range.1 hp
    have eqy := (ZFSet.pair_inj.1 eq).1
    exact eqy ▸ (names i).property

theorem entry_assemble {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (σ : Name s) (p : P) :
    Entry σ (assemble names conditions) p ↔ ∃ i, names i = σ ∧ conditions i = p := by
  change ZFSet.pair σ.val (s.encode p) ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    have parts := ZFSet.pair_inj.1 eq
    exact ⟨i, Subtype.ext parts.1, s.injective parts.2⟩
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i, rfl⟩

theorem assemble_entries (τ : Name s) :
    assemble (fun a : Entries τ => a.val.1) (fun a => a.val.2) = τ := by
  apply ext
  intro σ p
  rw [entry_assemble]
  constructor
  · rintro ⟨a, hs, hp⟩
    simpa only [← hs, ← hp] using a.property
  · intro h
    exact ⟨⟨(σ, p), h⟩, rfl, rfl⟩

def empty (s : Presentation P) : Name s :=
  ⟨∅, IsName.mk (by intro z hz; exact False.elim (ZFSet.notMem_empty z hz))
    (by intro y p hp; exact False.elim (ZFSet.notMem_empty _ hp))⟩

theorem not_entry_empty (σ : Name s) (p : P) : ¬ Entry σ (empty s) p :=
  ZFSet.notMem_empty _

end Name
end



namespace Name

open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

noncomputable def eval (H : Set P) (τ : Name s) : ZFSet.{u} :=
  ZFSet.range (fun a : {a : Entries τ // a.val.2 ∈ H} => eval H a.val.val.1)
termination_by ZFSet.rank τ.val
decreasing_by exact entry_rank_lt a.val.property

theorem mem_eval (H : Set P) (τ : Name s) (x : ZFSet.{u}) :
    x ∈ eval H τ ↔ ∃ σ p, Entry σ τ p ∧ p ∈ H ∧ eval H σ = x := by
  rw [eval, ZFSet.mem_range]
  constructor
  · rintro ⟨a, eq⟩
    exact ⟨a.val.val.1, a.val.val.2, a.val.property, a.property, eq⟩
  · rintro ⟨σ, p, h, hp, eq⟩
    exact ⟨⟨⟨(σ, p), h⟩, hp⟩, eq⟩

theorem mem_eval_assemble (H : Set P) {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (x : ZFSet.{u}) :
    x ∈ eval H (assemble names conditions) ↔
      ∃ i, conditions i ∈ H ∧ eval H (names i) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions σ p).1 entry
    exact ⟨i, hp, eq⟩
  · rintro ⟨i, hp, eq⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, hp, eq⟩

theorem eval_assemble (H : Set P) {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) :
    eval H (assemble names conditions) =
      ZFSet.range (fun i : {i // conditions i ∈ H} => eval H (names i.val)) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval_assemble, ZFSet.mem_range]
  constructor
  · rintro ⟨i, hp, eq⟩
    exact ⟨⟨i, hp⟩, eq⟩
  · rintro ⟨i, eq⟩
    exact ⟨i.val, i.property, eq⟩

theorem eval_empty (H : Set P) : eval H (empty s) = ∅ := by
  apply ZFSet.ext
  intro x
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, h, _, _⟩
    exact False.elim (not_entry_empty σ p h)
  · exact False.elim ∘ ZFSet.notMem_empty x

theorem eval_empty_conditions (τ : Name s) : eval (∅ : Set P) τ = ∅ := by
  apply ZFSet.ext
  intro x
  rw [mem_eval]
  constructor
  · rintro ⟨_, _, _, hp, _⟩
    exact False.elim hp
  · exact False.elim ∘ ZFSet.notMem_empty x

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def ForcesEq (p : P) (σ τ : Name s) : Prop :=
  (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r →
    ∃ t, t ≤ q ∧ ∃ ν k, Entry ν τ k ∧ t ≤ k ∧ ForcesEq t ρ ν) ∧
  (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k →
    ∃ t, t ≤ q ∧ ∃ ρ r, ∃ _ : Entry ρ σ r, t ≤ r ∧ ForcesEq t ρ ν)
termination_by ZFSet.rank σ.val
decreasing_by all_goals exact entry_rank_lt ‹Entry _ σ _›

theorem forcesEq_mono {p q : P} {σ τ : Name s} (h : ForcesEq p σ τ) (qp : q ≤ p) :
    ForcesEq q σ τ := by
  rw [ForcesEq] at h ⊢
  exact ⟨fun ρ r hr t tq tr => h.1 ρ r hr t (tq.trans qp) tr,
    fun ν k hk t tq tk => h.2 ν k hk t (tq.trans qp) tk⟩

theorem forcesEq_refl (σ : Name s) (p : P) : ForcesEq p σ σ := by
  induction σ using inductionOn generalizing p with
  | step σ ih =>
    rw [ForcesEq]
    constructor
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩

theorem forcesEq_symm {p : P} {σ τ : Name s} (h : ForcesEq p σ τ) : ForcesEq p τ σ := by
  induction σ using inductionOn generalizing p τ with
  | step σ ih =>
    rw [ForcesEq] at h ⊢
    constructor
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, eq⟩ := h.2 ν k hk q qp qk
      exact ⟨t, tq, ρ, r, hr, tr, ih ρ r hr eq⟩
    · intro ρ r hr q qp qr
      obtain ⟨t, tq, ν, k, hk, tk, eq⟩ := h.1 ρ r hr q qp qr
      exact ⟨t, tq, ν, k, hk, tk, ih ρ r hr eq⟩

theorem forcesEq_of_dense {p : P} {σ τ : Name s}
    (dense : DenseBelow p {q | ForcesEq q σ τ}) : ForcesEq p σ τ := by
  rw [ForcesEq]
  constructor
  · intro ρ r hr q qp qr
    obtain ⟨t, tq, ht⟩ := dense q qp
    change ForcesEq t σ τ at ht
    rw [ForcesEq] at ht
    obtain ⟨v, vt, ν, k, hk, vk, eq⟩ := ht.1 ρ r hr t le_rfl (tq.trans qr)
    exact ⟨v, vt.trans tq, ν, k, hk, vk, eq⟩
  · intro ν k hk q qp qk
    obtain ⟨t, tq, ht⟩ := dense q qp
    change ForcesEq t σ τ at ht
    rw [ForcesEq] at ht
    obtain ⟨v, vt, ρ, r, hr, vr, eq⟩ := ht.2 ν k hk t le_rfl (tq.trans qk)
    exact ⟨v, vt.trans tq, ρ, r, hr, vr, eq⟩

def MemWitness (σ τ : Name s) : Set P :=
  {p | ∃ ν r, Entry ν τ r ∧ p ≤ r ∧ ForcesEq p σ ν}

def ForcesMem (p : P) (σ τ : Name s) : Prop := DenseBelow p (MemWitness σ τ)

theorem forcesMem_mono {p q : P} {σ τ : Name s} (h : ForcesMem p σ τ) (qp : q ≤ p) :
    ForcesMem q σ τ := fun r rq => h r (rq.trans qp)

theorem forcesMem_of_witness {p : P} {σ τ : Name s} (h : p ∈ MemWitness σ τ) :
    ForcesMem p σ τ := by
  obtain ⟨ν, r, entry, pr, eq⟩ := h
  intro q qp
  exact ⟨q, le_rfl, ν, r, entry, qp.trans pr, forcesEq_mono eq qp⟩

theorem forcesMem_entry {σ τ : Name s} {r : P} (entry : Entry σ τ r) :
    ForcesMem r σ τ := forcesMem_of_witness ⟨σ, r, entry, le_rfl, forcesEq_refl σ r⟩

theorem forcesMem_of_dense {p : P} {σ τ : Name s}
    (dense : DenseBelow p {q | ForcesMem q σ τ}) : ForcesMem p σ τ := by
  intro q qp
  obtain ⟨r, rq, hr⟩ := dense q qp
  obtain ⟨t, tr, ht⟩ := hr r le_rfl
  exact ⟨t, tr.trans rq, ht⟩

theorem forcesEq_left {p q r : P} {σ τ ρ : Name s}
    (eq : ForcesEq p σ τ) (entry : Entry ρ σ r) (qp : q ≤ p) (qr : q ≤ r) :
    ForcesMem q ρ τ := by
  rw [ForcesEq] at eq
  intro t tq
  exact eq.1 ρ r entry t (tq.trans qp) (tq.trans qr)

theorem forcesEq_right {p q r : P} {σ τ ρ : Name s}
    (eq : ForcesEq p σ τ) (entry : Entry ρ τ r) (qp : q ≤ p) (qr : q ≤ r) :
    ForcesMem q ρ σ := forcesEq_left (forcesEq_symm eq) entry qp qr

theorem forcesEq_iff (p : P) (σ τ : Name s) : ForcesEq p σ τ ↔
    (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r → ForcesMem q ρ τ) ∧
    (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k → ForcesMem q ν σ) := by
  constructor
  · intro eq
    exact ⟨fun _ _ entry _ qp qr => forcesEq_left eq entry qp qr,
      fun _ _ entry _ qp qr => forcesEq_right eq entry qp qr⟩
  · rintro ⟨left, right⟩
    rw [ForcesEq]
    constructor
    · intro ρ r hr q qp qr
      exact left ρ r hr q qp qr q le_rfl
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, eq⟩ := right ν k hk q qp qk q le_rfl
      exact ⟨t, tq, ρ, r, hr, tr, forcesEq_symm eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

noncomputable def check (s : Presentation P) (one : P) (x : ZFSet.{u}) : Name s :=
  assemble (fun y : x => check s one y.val) (fun _ => one)
termination_by ZFSet.rank x
decreasing_by exact ZFSet.rank_lt_of_mem y.property

theorem entry_check (one : P) (x : ZFSet.{u}) (σ : Name s) (p : P) :
    Entry σ (check s one x) p ↔ ∃ y ∈ x, check s one y = σ ∧ one = p := by
  rw [check, entry_assemble]
  constructor
  · rintro ⟨y, eq, hp⟩
    exact ⟨y.val, y.property, eq, hp⟩
  · rintro ⟨y, hy, eq, hp⟩
    exact ⟨⟨y, hy⟩, eq, hp⟩

theorem eval_check (H : Set P) (one : P) (hone : one ∈ H) (x : ZFSet.{u}) :
    eval H (check s one x) = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [check]
    apply ZFSet.ext
    intro z
    rw [mem_eval_assemble]
    constructor
    · rintro ⟨y, _, eq⟩
      rw [ih y.val y.property] at eq
      exact eq ▸ y.property
    · intro hz
      exact ⟨⟨z, hz⟩, hone, ih z hz⟩

theorem check_injective (s : Presentation P) (one : P) :
    Function.Injective (check s one) := by
  intro x y eq
  have h := congrArg (eval (Set.univ : Set P)) eq
  simpa only [eval_check Set.univ one (Set.mem_univ one)] using h

noncomputable def singleton (one : P) (σ : Name s) : Name s :=
  assemble (fun _ : Unit => σ) (fun _ => one)

noncomputable def unorderedPair (one : P) (σ τ : Name s) : Name s :=
  assemble (fun b : Bool => if b then σ else τ) (fun _ => one)

noncomputable def orderedPair (one : P) (σ τ : Name s) : Name s :=
  unorderedPair one (singleton one σ) (unorderedPair one σ τ)

theorem eval_singleton (H : Set P) (one : P) (hone : one ∈ H) (σ : Name s) :
    eval H (singleton one σ) = {eval H σ} := by
  apply ZFSet.ext
  intro x
  rw [singleton, mem_eval_assemble, ZFSet.mem_singleton]
  constructor
  · rintro ⟨_, _, eq⟩
    exact eq.symm
  · intro eq
    exact ⟨(), hone, eq.symm⟩

theorem eval_unorderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (unorderedPair one σ τ) = {eval H σ, eval H τ} := by
  apply ZFSet.ext
  intro x
  rw [unorderedPair, mem_eval_assemble, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, _, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, hone, eq.symm⟩
    · exact ⟨false, hone, eq.symm⟩

theorem eval_orderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (orderedPair one σ τ) = ZFSet.pair (eval H σ) (eval H τ) := by
  rw [orderedPair, eval_unorderedPair H one hone,
    eval_singleton H one hone, eval_unorderedPair H one hone]
  rfl

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

structure NameDomain (s : Presentation P) where
  names : Set (Name s)
  children : ∀ {σ τ : Name s} {p : P}, τ ∈ names → Entry σ τ p → σ ∈ names

def ForcesNotMem (p : P) (σ τ : Name s) : Prop :=
  ∀ q, q ≤ p → ¬ ForcesMem q σ τ

theorem not_forcesMem_refine {p : P} {σ τ : Name s} (bad : ¬ ForcesMem p σ τ) :
    ∃ q, q ≤ p ∧ ForcesNotMem q σ τ := by
  classical
  change ¬ ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ MemWitness σ τ at bad
  push Not at bad
  obtain ⟨q, qp, hq⟩ := bad
  refine ⟨q, qp, ?_⟩
  intro r rq hr
  obtain ⟨t, tr, ht⟩ := hr r le_rfl
  exact hq t (tr.trans rq) ht

def EqDecisionWitness (σ τ : Name s) : Set P :=
  {p | ForcesEq p σ τ ∨
    (∃ ρ r, Entry ρ σ r ∧ p ≤ r ∧ ForcesNotMem p ρ τ) ∨
    ∃ ν k, Entry ν τ k ∧ p ≤ k ∧ ForcesNotMem p ν σ}

theorem eqDecisionWitness_dense (σ τ : Name s) : Dense (EqDecisionWitness σ τ) := by
  classical
  intro p
  by_cases eq : ForcesEq p σ τ
  · exact ⟨p, le_rfl, Or.inl eq⟩
  · rw [forcesEq_iff] at eq
    obtain bad | bad := not_and_or.mp eq
    · push Not at bad
      obtain ⟨ρ, r, entry, q, qp, qr, nmem⟩ := bad
      obtain ⟨t, tq, neg⟩ := not_forcesMem_refine nmem
      exact ⟨t, tq.trans qp, Or.inr (Or.inl ⟨ρ, r, entry, tq.trans qr, neg⟩)⟩
    · push Not at bad
      obtain ⟨ν, k, entry, q, qp, qk, nmem⟩ := bad
      obtain ⟨t, tq, neg⟩ := not_forcesMem_refine nmem
      exact ⟨t, tq.trans qp, Or.inr (Or.inr ⟨ν, k, entry, tq.trans qk, neg⟩)⟩

def atomicFamily (D : NameDomain s) : Set (Set P) :=
  {E | (∃ p σ τ, σ ∈ D.names ∧ τ ∈ D.names ∧ E = Localized p (MemWitness σ τ)) ∨
    ∃ σ τ, σ ∈ D.names ∧ τ ∈ D.names ∧ E = EqDecisionWitness σ τ}

theorem generic_mem_witness (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) {p : P} (hp : H.mem p)
    (h : ForcesMem p σ τ) : H.Meets (MemWitness σ τ) :=
  H.meets_below generic hp (Or.inl ⟨p, σ, τ, hσ, hτ, rfl⟩) h

end Name



namespace Name.NameDomain

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

def values (D : NameDomain s) (H : Set P) : Set ZFSet.{u} :=
  Set.range (fun τ : D.names => eval H τ.val)

theorem mem_values (D : NameDomain s) (H : Set P) (x : ZFSet.{u}) :
    x ∈ D.values H ↔ ∃ τ ∈ D.names, eval H τ = x := by
  constructor
  · rintro ⟨τ, eq⟩
    exact ⟨τ.val, τ.property, eq⟩
  · rintro ⟨τ, hτ, eq⟩
    exact ⟨⟨τ, hτ⟩, eq⟩

theorem values_transitive (D : NameDomain s) (H : Set P)
    {x y : ZFSet.{u}} (hx : x ∈ D.values H) (hy : y ∈ x) : y ∈ D.values H := by
  obtain ⟨τ, hτ, rfl⟩ := (D.mem_values H x).1 hx
  obtain ⟨σ, p, entry, _, eq⟩ := (mem_eval H τ y).1 hy
  exact (D.mem_values H y).2 ⟨σ, D.children hτ entry, eq⟩

theorem values_extensionality (D : NameDomain s) (H : Set P)
    {x y : ZFSet.{u}} (hx : x ∈ D.values H) (hy : y ∈ D.values H)
    (agree : ∀ z ∈ D.values H, z ∈ x ↔ z ∈ y) : x = y := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (agree z (D.values_transitive H hx hz)).1 hz
  · intro hz
    exact (agree z (D.values_transitive H hy hz)).2 hz

theorem values_foundation (D : NameDomain s) (H : Set P)
    {x : ZFSet.{u}} (hx : x ∈ D.values H) (nonempty : x ≠ ∅) :
    ∃ y ∈ D.values H, y ∈ x ∧ x ∩ y = ∅ := by
  obtain ⟨y, yx, disjoint⟩ := ZFSet.regularity x nonempty
  exact ⟨y, D.values_transitive H hx yx, yx, disjoint⟩

end Name.NameDomain

end PartitionPilot.Forcing

end OAI
