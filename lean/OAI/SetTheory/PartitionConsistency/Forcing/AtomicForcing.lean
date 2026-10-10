import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.NameActions

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v

/-- An edge of a literal name decreases the rank of its name component. -/
theorem Child.rank_lt {τ σ : ZFSet.{u}} (h : Child τ σ) : τ.rank < σ.rank := by
  obtain ⟨p, hp⟩ := h
  exact (ZFSet.rank_lt_of_mem (by simp : τ ∈ ({τ} : ZFSet))).trans
    ((ZFSet.rank_lt_of_mem (by simp [ZFSet.pair] : ({τ} : ZFSet) ∈ ZFSet.pair τ p)).trans
      (ZFSet.rank_lt_of_mem hp))

namespace AtomicForcing

/-- The rank multiset, rather than a lexicographic ordering, permits the swaps
in the recursive clauses of atomic forcing. -/
noncomputable def pairRanks (σ τ : ZFSet.{u}) : Multiset Ordinal.{u} := {σ.rank} + {τ.rank}

def PairLower (st uv : ZFSet.{u} × ZFSet.{u}) : Prop :=
  Multiset.IsDershowitzMannaLT (pairRanks st.1 st.2) (pairRanks uv.1 uv.2)

theorem pairLower_wf : WellFounded PairLower.{u} :=
  InvImage.wf (fun st : ZFSet.{u} × ZFSet.{u} => pairRanks st.1 st.2) Multiset.wellFounded_isDershowitzMannaLT

theorem rank_replace (R : Multiset Ordinal.{u}) {τ σ : ZFSet.{u}} (h : Child τ σ) :
    Multiset.IsDershowitzMannaLT (R + {τ.rank}) (R + {σ.rank}) := by
  refine ⟨R, {τ.rank}, {σ.rank}, by simp, rfl, rfl, ?_⟩
  simpa using h.rank_lt

theorem pairLower_right {σ τ ν : ZFSet.{u}} (h : Child ν τ) :
    PairLower (σ, ν) (σ, τ) := rank_replace _ h

theorem pairLower_left {σ τ ν : ZFSet.{u}} (h : Child ν σ) :
    PairLower (ν, τ) (σ, τ) := by
  simpa [PairLower, pairRanks, add_comm] using rank_replace {τ.rank} h

theorem pairLower_swap {σ τ ν : ZFSet.{u}} (h : Child ν τ) :
    PairLower (ν, σ) (σ, τ) := by
  simpa [PairLower, pairRanks, add_comm] using rank_replace {σ.rank} h

variable {P : Type v} [Preorder P] (code : P → ZFSet.{u})

/-- Ordinary atomic set forcing, on actual sets of Kuratowski pairs. The first
component is membership and the second is equality. No truth values or atomic
laws are supplied as parameters. -/
noncomputable def relations : ZFSet.{u} × ZFSet.{u} → (P → Prop) × (P → Prop) :=
  pairLower_wf.fix fun st rec =>
  ( (fun p => ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ (ν : ZFSet.{u}) (r : P),
      ∃ he : ZFSet.pair ν (code r) ∈ st.2,
        s ≤ r ∧ (rec (st.1, ν) (pairLower_right ⟨(code r), he⟩)).2 s),
    (fun p =>
      (∀ ν (r : P) (he : ZFSet.pair ν (code r) ∈ st.1), ∀ q, q ≤ p → q ≤ r →
        (rec (ν, st.2) (pairLower_left ⟨(code r), he⟩)).1 q) ∧
      (∀ ν (r : P) (he : ZFSet.pair ν (code r) ∈ st.2), ∀ q, q ≤ p → q ≤ r →
        (rec (ν, st.1) (pairLower_swap ⟨(code r), he⟩)).1 q)) )

noncomputable def MemAt (p : P) (σ τ : ZFSet.{u}) : Prop := (relations code (σ, τ)).1 p
noncomputable def EqAt (p : P) (σ τ : ZFSet.{u}) : Prop := (relations code (σ, τ)).2 p

variable {code}

theorem mem_iff {p : P} {σ τ : ZFSet.{u}} : MemAt code p σ τ ↔
    ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ (ν : ZFSet.{u}) (r : P),
      ZFSet.pair ν (code r) ∈ τ ∧ s ≤ r ∧ EqAt code s σ ν := by
  unfold MemAt relations
  rw [WellFounded.fix_eq]
  change (∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ (ν : ZFSet.{u}) (r : P),
    ∃ _he : ZFSet.pair ν (code r) ∈ τ, s ≤ r ∧ EqAt code s σ ν) ↔ _
  simp only [exists_prop]

theorem eq_iff {p : P} {σ τ : ZFSet.{u}} : EqAt code p σ τ ↔
    (∀ ν (r : P), ZFSet.pair ν (code r) ∈ σ → ∀ q, q ≤ p → q ≤ r → MemAt code q ν τ) ∧
    (∀ ν (r : P), ZFSet.pair ν (code r) ∈ τ → ∀ q, q ≤ p → q ≤ r → MemAt code q ν σ) := by
  unfold EqAt relations
  rw [WellFounded.fix_eq]
  rfl

theorem mem_mono {p q : P} {σ τ : ZFSet.{u}} (hqp : q ≤ p)
    (h : MemAt code p σ τ) : MemAt code q σ τ := by
  exact mem_iff.mpr fun r hr => mem_iff.mp h r (hr.trans hqp)

theorem eq_mono {p q : P} {σ τ : ZFSet.{u}} (hqp : q ≤ p)
    (h : EqAt code p σ τ) : EqAt code q σ τ := by
  obtain ⟨h₁, h₂⟩ := eq_iff.mp h
  exact eq_iff.mpr ⟨fun ν r he s hs hsr => h₁ ν r he s (hs.trans hqp) hsr,
    fun ν r he s hs hsr => h₂ ν r he s (hs.trans hqp) hsr⟩

theorem eq_symm {p : P} {σ τ : ZFSet.{u}} (h : EqAt code p σ τ) : EqAt code p τ σ :=
  eq_iff.mpr (eq_iff.mp h).symm

/-- Atomic membership is unchanged by closing densely below a condition. -/
theorem mem_of_dense {p : P} {σ τ : ZFSet.{u}}
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ MemAt code r σ τ) : MemAt code p σ τ := by
  apply mem_iff.mpr
  intro q hq
  obtain ⟨r, hrq, hr⟩ := h q hq
  obtain ⟨s, hsr, w⟩ := mem_iff.mp hr r le_rfl
  exact ⟨s, hsr.trans hrq, w⟩

/-- Atomic equality also has the dense-closure property. -/
theorem eq_of_dense {p : P} {σ τ : ZFSet.{u}}
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ EqAt code r σ τ) : EqAt code p σ τ := by
  have step : ∀ a b, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ EqAt code r a b) →
      ∀ ν (s : P), ZFSet.pair ν (code s) ∈ a → ∀ q, q ≤ p → q ≤ s → MemAt code q ν b := by
    intro a b hab ν s he q hqp hqs
    apply mem_of_dense
    intro t htq
    obtain ⟨r, hrt, hr⟩ := hab t (htq.trans hqp)
    exact ⟨r, hrt, (eq_iff.mp hr).1 ν s he r le_rfl ((hrt.trans htq).trans hqs)⟩
  exact eq_iff.mpr ⟨step σ τ h, step τ σ (fun q hq => by
    obtain ⟨r, hrq, hr⟩ := h q hq
    exact ⟨r, hrq, eq_symm hr⟩)⟩

theorem mem_of_edge_eq {p r : P} {σ τ ν : ZFSet.{u}}
    (hr : p ≤ r) (he : ZFSet.pair ν (code r) ∈ τ) (h : EqAt code p σ ν) :
    MemAt code p σ τ := by
  apply mem_iff.mpr
  intro q hq
  exact ⟨q, le_rfl, ν, r, he, hq.trans hr, eq_mono hq h⟩

theorem eq_refl (p : P) (σ : ZFSet.{u}) : EqAt code p σ σ := by
  induction σ using child_wf.induction generalizing p with
  | h σ ih =>
    apply eq_iff.mpr
    have step : ∀ ν (r : P), ZFSet.pair ν (code r) ∈ σ →
        ∀ q, q ≤ p → q ≤ r → MemAt code q ν σ := by
      intro ν r he q _ hqr
      exact mem_of_edge_eq hqr he (ih ν ⟨(code r), he⟩ q)
    exact ⟨step, step⟩

noncomputable def tripleRanks (a b c : ZFSet.{u}) : Multiset Ordinal.{u} :=
  {a.rank} + {b.rank} + {c.rank}

def TripleLower (s t : ZFSet.{u} × ZFSet.{u} × ZFSet.{u}) : Prop :=
  Multiset.IsDershowitzMannaLT (tripleRanks s.1 s.2.1 s.2.2)
    (tripleRanks t.1 t.2.1 t.2.2)

theorem tripleLower_wf : WellFounded TripleLower.{u} :=
  InvImage.wf (fun s : ZFSet.{u} × ZFSet.{u} × ZFSet.{u} => tripleRanks s.1 s.2.1 s.2.2)
    Multiset.wellFounded_isDershowitzMannaLT

/-- All three substitution rules are proved together. The induction measure
is invariant under permutations, while replacing a name by a child decreases
it. In particular transitivity is a consequence, not an assumed atomic law. -/
theorem atomic_laws (a b c : ZFSet.{u}) :
    (∀ p : P, EqAt code p a b → EqAt code p b c → EqAt code p a c) ∧
    (∀ p : P, EqAt code p a b → MemAt code p a c → MemAt code p b c) ∧
    (∀ p : P, EqAt code p b c → MemAt code p a b → MemAt code p a c) := by
  let T (s : ZFSet.{u} × ZFSet.{u} × ZFSet.{u}) :=
    (∀ p : P, EqAt code p s.1 s.2.1 → EqAt code p s.2.1 s.2.2 → EqAt code p s.1 s.2.2) ∧
    (∀ p : P, EqAt code p s.1 s.2.1 → MemAt code p s.1 s.2.2 → MemAt code p s.2.1 s.2.2) ∧
    (∀ p : P, EqAt code p s.2.1 s.2.2 → MemAt code p s.1 s.2.1 → MemAt code p s.1 s.2.2)
  change T (a, b, c)
  apply tripleLower_wf.induction (C := T)
  rintro ⟨a,b,c⟩ ih
  refine ⟨?_, ?_, ?_⟩
  · intro p hab hbc
    apply eq_iff.mpr
    constructor
    · intro ν r he q hqp hqr
      have hl : TripleLower (ν,b,c) (a,b,c) := by
        simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
          rank_replace ({b.rank} + {c.rank}) (show Child ν a from ⟨(code r), he⟩)
      exact (ih (ν,b,c) hl).2.2 q (eq_mono hqp hbc)
        ((eq_iff.mp hab).1 ν r he q hqp hqr)
    · intro ν r he q hqp hqr
      have hl : TripleLower (ν,b,a) (a,b,c) := by
        simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
          rank_replace ({a.rank} + {b.rank}) (show Child ν c from ⟨(code r), he⟩)
      exact (ih (ν,b,a) hl).2.2 q (eq_symm (eq_mono hqp hab))
        ((eq_iff.mp hbc).2 ν r he q hqp hqr)
  · intro p hab hac
    apply mem_iff.mpr
    intro q hqp
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hac q hqp
    have hl : TripleLower (b,a,ν) (a,b,c) := by
      simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
        rank_replace ({a.rank} + {b.rank}) (show Child ν c from ⟨(code r), he⟩)
    exact ⟨s, hsq, ν, r, he, hsr,
      (ih (b,a,ν) hl).1 s (eq_symm (eq_mono (hsq.trans hqp) hab)) heq⟩
  · intro p hbc hab
    apply mem_of_dense
    intro q hqp
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hab q hqp
    have hl : TripleLower (ν,a,c) (a,b,c) := by
      simpa only [TripleLower, tripleRanks, add_comm, add_left_comm, add_assoc] using
        rank_replace ({a.rank} + {c.rank}) (show Child ν b from ⟨(code r), he⟩)
    exact ⟨s, hsq, (ih (ν,a,c) hl).2.1 s (eq_symm heq)
      ((eq_iff.mp hbc).1 ν r he s (hsq.trans hqp) hsr)⟩

theorem eq_trans {p : P} {a b c : ZFSet.{u}} (hab : EqAt code p a b)
    (hbc : EqAt code p b c) : EqAt code p a c := (atomic_laws a b c).1 p hab hbc

theorem mem_congr_left {p : P} {a b c : ZFSet.{u}} (hab : EqAt code p a b) :
    MemAt code p a c ↔ MemAt code p b c :=
  ⟨(atomic_laws a b c).2.1 p hab, (atomic_laws b a c).2.1 p (eq_symm hab)⟩

theorem mem_congr_right {p : P} {a b c : ZFSet.{u}} (hbc : EqAt code p b c) :
    MemAt code p a b ↔ MemAt code p a c :=
  ⟨(atomic_laws a b c).2.2 p hbc, (atomic_laws a c b).2.2 p (eq_symm hbc)⟩

/-- The constructed atomic forcing relations instantiate the external
quotient machinery on any specified set of name codes. -/
noncomputable def data (code : P → ZFSet.{u}) (N : Set ZFSet.{u}) : ForcingQuotient.AtomicData P N where
  EqF p a b := EqAt code p a.val b.val
  MemF p a b := MemAt code p a.val b.val
  eq_mono := eq_mono
  mem_mono := mem_mono
  eq_refl p a := eq_refl p a.val
  eq_symm := eq_symm
  eq_trans := eq_trans
  mem_congr ha hb := (mem_congr_left ha).trans (mem_congr_right hb)

end AtomicForcing
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.AtomicForcing
universe u v w
open ForcingQuotient
variable {P : Type v} [Preorder P] {code : P → ZFSet.{u}}

/-- Failure of membership has a strengthening that forces its negation. -/
theorem exists_no_mem {p : P} {σ τ : ZFSet.{u}} (h : ¬ MemAt code p σ τ) :
    ∃ q, q ≤ p ∧ ∀ r, r ≤ q → ¬ MemAt code r σ τ := by
  classical
  by_contra! hn
  exact h (mem_of_dense hn)

/-- Conditions which either contain an atomic membership witness or exclude
membership at every strengthening. -/
def memberDecisions (code : P → ZFSet.{u}) (σ τ : ZFSet.{u}) : Set P :=
  {p | (∃ (ν : ZFSet.{u}) (r : P), ZFSet.pair ν (code r) ∈ τ ∧ p ≤ r ∧ EqAt code p σ ν) ∨
    ∀ q, q ≤ p → ¬ MemAt code q σ τ}

theorem memberDecisions_dense (code : P → ZFSet.{u}) (σ τ : ZFSet.{u}) :
    Dense (memberDecisions code σ τ) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ MemAt code q σ τ
  · obtain ⟨q, hqp, hq⟩ := h
    obtain ⟨s, hsq, hw⟩ := mem_iff.mp hq q le_rfl
    exact ⟨s, hsq.trans hqp, Or.inl hw⟩
  · exact ⟨p, le_rfl, Or.inr (by simpa only [not_exists, not_and] using h)⟩

/-- A named member of `σ` which a condition forces not to belong to `τ`.
This is a concrete witness to inequality, not a postulated decision law. -/
def Apart (code : P → ZFSet.{u}) (p : P) (σ τ : ZFSet.{u}) : Prop :=
  ∃ (ν : ZFSet.{u}) (r : P), ZFSet.pair ν (code r) ∈ σ ∧ p ≤ r ∧
    ∀ q, q ≤ p → ¬ MemAt code q ν τ

def equalityDecisions (code : P → ZFSet.{u}) (σ τ : ZFSet.{u}) : Set P :=
  {p | EqAt code p σ τ ∨ Apart code p σ τ ∨ Apart code p τ σ}

theorem equalityDecisions_dense (code : P → ZFSet.{u}) (σ τ : ZFSet.{u}) :
    Dense (equalityDecisions code σ τ) := by
  classical
  intro p
  by_cases h : EqAt code p σ τ
  · exact ⟨p, le_rfl, Or.inl h⟩
  · have h' := mt (@eq_iff _ _ code p σ τ).mpr h
    have step : ∀ a b, ¬ (∀ ν (r : P), ZFSet.pair ν (code r) ∈ a →
        ∀ q, q ≤ p → q ≤ r → MemAt code q ν b) → ∃ q, q ≤ p ∧ Apart code q a b := by
      intro a b hab
      push Not at hab
      obtain ⟨ν, r, he, q, hqp, hqr, hn⟩ := hab
      obtain ⟨s, hsq, hs⟩ := exists_no_mem hn
      exact ⟨s, hsq.trans hqp, ν, r, he, hsq.trans hqr, hs⟩
    rcases not_and_or.mp h' with h' | h'
    · obtain ⟨q, hqp, hq⟩ := step σ τ h'
      exact ⟨q, hqp, Or.inr (Or.inl hq)⟩
    · obtain ⟨q, hqp, hq⟩ := step τ σ h'
      exact ⟨q, hqp, Or.inr (Or.inr hq)⟩

/-- The set of active literal condition codes. -/
def activeCodes (code : P → ZFSet.{u}) (G : GenericFilter P) : Set ZFSet.{u} :=
  code '' {p | p ∈ G}

theorem mem_evaluate_active_iff {G : GenericFilter P} {σ x : ZFSet.{u}} :
    x ∈ evaluate (activeCodes code G) σ ↔
    ∃ (ν : ZFSet.{u}) (r : P), ZFSet.pair ν (code r) ∈ σ ∧ r ∈ G ∧
      evaluate (activeCodes code G) ν = x := by
  rw [mem_evaluate_iff]
  constructor
  · rintro ⟨ν, _, he, ⟨r, hr, rfl⟩, hx⟩
    exact ⟨ν, r, he, hr, hx⟩
  · rintro ⟨ν, r, he, hr, hx⟩
    exact ⟨ν, code r, he, ⟨r, hr, rfl⟩, hx⟩

/-- A collection of literal names is hereditary for edges using conditions
in `P`. Countability and this property impose no bound on name-rank. -/
def EdgeClosed (code : P → ZFSet.{u}) (N : Set ZFSet.{u}) : Prop :=
  ∀ σ ∈ N, ∀ ν (r : P), ZFSet.pair ν (code r) ∈ σ → ν ∈ N

/-- Precisely the two families of dense sets needed for the atomic truth
lemma. Their existence and density were proved above. -/
def IsAtomicGeneric (code : P → ZFSet.{u}) (N : Set ZFSet.{u})
    (G : GenericFilter P) : Prop :=
  ∀ σ ∈ N, ∀ τ ∈ N,
    (∃ p, p ∈ G ∧ p ∈ memberDecisions code σ τ) ∧
    (∃ p, p ∈ G ∧ p ∈ equalityDecisions code σ τ)

/-- The ordinary atomic truth lemma is proved by recursion on the literal
names. This supplies the link between the atomic quotient and actual set
interpretation in the transitive-ground route. -/
theorem atomic_truth {N : Set ZFSet.{u}} (hN : EdgeClosed code N)
    (G : GenericFilter P) (hG : IsAtomicGeneric code N G)
    {σ τ : ZFSet.{u}} (hσ : σ ∈ N) (hτ : τ ∈ N) :
    ((∃ p, p ∈ G ∧ MemAt code p σ τ) ↔
       evaluate (activeCodes code G) σ ∈ evaluate (activeCodes code G) τ) ∧
    ((∃ p, p ∈ G ∧ EqAt code p σ τ) ↔
       evaluate (activeCodes code G) σ = evaluate (activeCodes code G) τ) := by
  let T (st : ZFSet.{u} × ZFSet.{u}) := st.1 ∈ N → st.2 ∈ N →
    ((∃ p, p ∈ G ∧ MemAt code p st.1 st.2) ↔
       evaluate (activeCodes code G) st.1 ∈ evaluate (activeCodes code G) st.2) ∧
    ((∃ p, p ∈ G ∧ EqAt code p st.1 st.2) ↔
       evaluate (activeCodes code G) st.1 = evaluate (activeCodes code G) st.2)
  suffices hall : ∀ st, T st from hall (σ,τ) hσ hτ
  intro st
  apply pairLower_wf.induction (C := T) st
  rintro ⟨a,b⟩ ih ha hb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨p, hp, hm⟩
    obtain ⟨q, hq, hw | hn⟩ := (hG a ha b hb).1
    · obtain ⟨ν, r, he, hqr, heq⟩ := hw
      have hν := hN b hb ν r he
      have hv := ((ih (a,ν) (pairLower_right ⟨code r, he⟩) ha hν).2).mp ⟨q, hq, heq⟩
      exact mem_evaluate_active_iff.mpr ⟨ν, r, he, G.lower hqr hq, hv.symm⟩
    · obtain ⟨s, hs, hsp, hsq⟩ := G.directed _ hp _ hq
      exact (hn s hsq (mem_mono hsp hm)).elim
  · intro hm
    obtain ⟨ν, r, he, hr, hv⟩ := mem_evaluate_active_iff.mp hm
    have hν := hN b hb ν r he
    obtain ⟨q, hq, heq⟩ := ((ih (a,ν) (pairLower_right ⟨code r, he⟩) ha hν).2).mpr hv.symm
    obtain ⟨s, hs, hsq, hsr⟩ := G.directed _ hq _ hr
    exact ⟨s, hs, mem_of_edge_eq hsr he (eq_mono hsq heq)⟩
  · rintro ⟨p, hp, heq⟩
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨ν, r, he, hr, rfl⟩ := mem_evaluate_active_iff.mp hx
      obtain ⟨s, hs, hsp, hsr⟩ := G.directed _ hp _ hr
      exact ((ih (ν,b) (pairLower_left ⟨code r, he⟩) (hN a ha ν r he) hb).1).mp
        ⟨s, hs, (eq_iff.mp heq).1 ν r he s hsp hsr⟩
    · intro hx
      obtain ⟨ν, r, he, hr, rfl⟩ := mem_evaluate_active_iff.mp hx
      obtain ⟨s, hs, hsp, hsr⟩ := G.directed _ hp _ hr
      exact ((ih (ν,a) (pairLower_swap ⟨code r, he⟩) (hN b hb ν r he) ha).1).mp
        ⟨s, hs, (eq_iff.mp heq).2 ν r he s hsp hsr⟩
  · intro hv
    obtain ⟨p, hp, heq | hap | hap⟩ := (hG a ha b hb).2
    · exact ⟨p, hp, heq⟩
    · obtain ⟨ν, r, he, hpr, hn⟩ := hap
      have hν := hN a ha ν r he
      have hm : evaluate (activeCodes code G) ν ∈ evaluate (activeCodes code G) b := by
        rw [← hv]
        exact mem_evaluate_active_iff.mpr ⟨ν, r, he, G.lower hpr hp, rfl⟩
      obtain ⟨q, hq, hqm⟩ := ((ih (ν,b) (pairLower_left ⟨code r, he⟩) hν hb).1).mpr hm
      obtain ⟨s, hs, hsp, hsq⟩ := G.directed _ hp _ hq
      exact (hn s hsp (mem_mono hsq hqm)).elim
    · obtain ⟨ν, r, he, hpr, hn⟩ := hap
      have hν := hN b hb ν r he
      have hm : evaluate (activeCodes code G) ν ∈ evaluate (activeCodes code G) a := by
        rw [hv]
        exact mem_evaluate_active_iff.mpr ⟨ν, r, he, G.lower hpr hp, rfl⟩
      obtain ⟨q, hq, hqm⟩ := ((ih (ν,a) (pairLower_swap ⟨code r, he⟩) hν ha).1).mpr hm
      obtain ⟨s, hs, hsp, hsq⟩ := G.directed _ hp _ hq
      exact (hn s hsp (mem_mono hsq hqm)).elim

/-- Construct an external filter meeting both the actual atomic requirements
and every standard-formula request on a countable collection of names. The
additional dense sets may, for example, include every coded ground dense set.
No assertion that target-theory axioms are forced is used here. -/
theorem exists_truth_generic (code : P → ZFSet.{u}) {N : Set ZFSet.{u}} (hc : N.Countable)
    {I : Type w} [Countable I] (D : I → Set P) (hD : ∀ i, Dense (D i)) (p : P) :
    ∃ G : GenericFilter P, p ∈ G ∧ (∀ i, ∃ q, q ∈ G ∧ q ∈ D i) ∧
      (data code N).IsGeneric G ∧ IsAtomicGeneric code N G := by
  let : Countable N := hc.to_subtype
  let request : Bool × N × N → Set P := fun i =>
    if i.1 then memberDecisions code i.2.1.val i.2.2.val
    else equalityDecisions code i.2.1.val i.2.2.val
  have hreq : ∀ i, Dense (request i) := by
    rintro ⟨b,a,c⟩
    cases b
    · exact equalityDecisions_dense code a.val c.val
    · exact memberDecisions_dense code a.val c.val
  obtain ⟨G, hp, hsets, hlogic⟩ := (data code N).exists_generic
    (Sum.elim D request) (by rintro (i | i); exact hD i; exact hreq i) p
  refine ⟨G, hp, (fun i => hsets (.inl i)), hlogic, ?_⟩
  intro σ hσ τ hτ
  exact ⟨hsets (.inr (true, ⟨σ,hσ⟩, ⟨τ,hτ⟩)), hsets (.inr (false, ⟨σ,hσ⟩, ⟨τ,hτ⟩))⟩

end PartitionConsistency.SetForcingNames.AtomicForcing



namespace PartitionConsistency.SetForcingNames.AtomicForcing
universe u v
variable {P : Type v} [Preorder P] {code : P → ZFSet.{u}}

/-- The literal action transforms exactly the edges, including their condition
codes. Injectivity prevents an edge using a different code from entering this
fiber. -/
theorem edge_map_orderIso {f : ZFSet.{u} → ZFSet.{u}} (hf : Function.Injective f)
    (e : P ≃o P) (hcode : ∀ p, f (code p) = code (e p))
    {σ ν : ZFSet.{u}} {r : P} :
    ZFSet.pair ν (code (e r)) ∈ mapConditions f σ ↔
      ∃ ρ, ZFSet.pair ρ (code r) ∈ σ ∧ mapConditions f ρ = ν := by
  rw [← hcode r, edge_mapConditions_iff]
  constructor
  · rintro ⟨ρ, s, he, hn, hc⟩
    have hs := hf hc
    subst s
    exact ⟨ρ, he, hn⟩
  · rintro ⟨ρ, he, rfl⟩
    exact ⟨ρ, code r, he, rfl, rfl⟩

/-- Atomic symmetry on literal names. Conditions are moved together with the
names; this makes no assertion that a generic filter is fixed by the action. -/
theorem atomic_symmetry {f : ZFSet.{u} → ZFSet.{u}} (hf : Function.Injective f)
    (e : P ≃o P) (hcode : ∀ p, f (code p) = code (e p)) (σ τ : ZFSet.{u}) :
    (∀ p, MemAt code p σ τ ↔
      MemAt code (e p) (mapConditions f σ) (mapConditions f τ)) ∧
    (∀ p, EqAt code p σ τ ↔
      EqAt code (e p) (mapConditions f σ) (mapConditions f τ)) := by
  let T (st : ZFSet.{u} × ZFSet.{u}) :=
    (∀ p, MemAt code p st.1 st.2 ↔
      MemAt code (e p) (mapConditions f st.1) (mapConditions f st.2)) ∧
    (∀ p, EqAt code p st.1 st.2 ↔
      EqAt code (e p) (mapConditions f st.1) (mapConditions f st.2))
  change T (σ,τ)
  apply pairLower_wf.induction (C := T)
  rintro ⟨a,b⟩ ih
  refine ⟨fun p => ⟨?_, ?_⟩, fun p => ⟨?_, ?_⟩⟩
  · intro hm
    apply mem_iff.mpr
    intro q hqp
    obtain ⟨q, rfl⟩ := e.surjective q
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hm q (e.le_iff_le.mp hqp)
    refine ⟨e s, e.monotone hsq, mapConditions f ν, e r, ?_, e.monotone hsr, ?_⟩
    · exact (edge_map_orderIso hf e hcode).mpr ⟨ν, he, rfl⟩
    · exact ((ih (a,ν) (pairLower_right ⟨code r, he⟩)).2 s).mp heq
  · intro hm
    apply mem_iff.mpr
    intro q hqp
    obtain ⟨s, hsq, ν, r, he, hsr, heq⟩ := mem_iff.mp hm (e q) (e.monotone hqp)
    obtain ⟨s, rfl⟩ := e.surjective s
    obtain ⟨r, rfl⟩ := e.surjective r
    obtain ⟨ρ, hρ, hν⟩ := (edge_map_orderIso hf e hcode).mp he
    subst ν
    refine ⟨s, e.le_iff_le.mp hsq, ρ, r, hρ, e.le_iff_le.mp hsr, ?_⟩
    exact ((ih (a,ρ) (pairLower_right ⟨code r, hρ⟩)).2 s).mpr heq
  · intro heq
    apply eq_iff.mpr
    constructor
    · intro ν r he q hqp hqr
      obtain ⟨r, rfl⟩ := e.surjective r
      obtain ⟨q, rfl⟩ := e.surjective q
      obtain ⟨ρ, hρ, hν⟩ := (edge_map_orderIso hf e hcode).mp he
      subst ν
      exact ((ih (ρ,b) (pairLower_left ⟨code r, hρ⟩)).1 q).mp
        ((eq_iff.mp heq).1 ρ r hρ q (e.le_iff_le.mp hqp) (e.le_iff_le.mp hqr))
    · intro ν r he q hqp hqr
      obtain ⟨r, rfl⟩ := e.surjective r
      obtain ⟨q, rfl⟩ := e.surjective q
      obtain ⟨ρ, hρ, hν⟩ := (edge_map_orderIso hf e hcode).mp he
      subst ν
      exact ((ih (ρ,a) (pairLower_swap ⟨code r, hρ⟩)).1 q).mp
        ((eq_iff.mp heq).2 ρ r hρ q (e.le_iff_le.mp hqp) (e.le_iff_le.mp hqr))
  · intro heq
    apply eq_iff.mpr
    constructor
    · intro ν r he q hqp hqr
      have he' : ZFSet.pair (mapConditions f ν) (code (e r)) ∈ mapConditions f a :=
        (edge_map_orderIso hf e hcode).mpr ⟨ν, he, rfl⟩
      exact ((ih (ν,b) (pairLower_left ⟨code r, he⟩)).1 q).mpr
        ((eq_iff.mp heq).1 _ _ he' (e q) (e.monotone hqp) (e.monotone hqr))
    · intro ν r he q hqp hqr
      have he' : ZFSet.pair (mapConditions f ν) (code (e r)) ∈ mapConditions f b :=
        (edge_map_orderIso hf e hcode).mpr ⟨ν, he, rfl⟩
      exact ((ih (ν,a) (pairLower_swap ⟨code r, he⟩)).1 q).mpr
        ((eq_iff.mp heq).2 _ _ he' (e q) (e.monotone hqp) (e.monotone hqr))

end PartitionConsistency.SetForcingNames.AtomicForcing

end OAI
