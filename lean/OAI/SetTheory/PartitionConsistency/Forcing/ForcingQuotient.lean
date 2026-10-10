import Mathlib
import OAI.SetTheory.PartitionConsistency.Logic.Proofs
import OAI.SetTheory.PartitionConsistency.Logic.SetLanguage

namespace OAI

namespace PartitionConsistency
/-! External generic filters and the name-quotient truth lemma.
These results do not supply the internal symmetric system or its ZF axioms.
They work on a set of name codes with specified atomic forcing relations. -/
namespace ForcingQuotient

/-- Stronger conditions are smaller. -/
def Dense {P : Type*} [Preorder P] (D : Set P) : Prop :=
  ∀ p, ∃ q, q ≤ p ∧ q ∈ D

/-- A forcing filter is an order ideal for the opposite order. -/
abbrev GenericFilter (P : Type*) [Preorder P] := Order.Ideal (OrderDual P)

/-- Countably many dense sets can be met through any given condition. This is
Mathlib's Rasiowa–Sikorski lemma with the forcing order convention. -/
theorem exists_generic_through {P I : Type*} [Preorder P] [Countable I]
    (D : I → Set P) (dense : ∀ i, Dense (D i)) (p : P) :
    ∃ G : GenericFilter P, p ∈ G ∧ ∀ i, ∃ q, q ∈ G ∧ q ∈ D i := by
  let _ : Encodable I := Encodable.ofCountable I
  let D' : I → Order.Cofinal (OrderDual P) := fun i =>
    ⟨D i, fun q => by
      obtain ⟨r, hrq, hrD⟩ := dense i q
      exact ⟨r, hrD, hrq⟩⟩
  refine ⟨Order.idealOfCofinals (P := OrderDual P) p D', Order.mem_idealOfCofinals (P := OrderDual P) p D', ?_⟩
  intro i
  obtain ⟨q, hD, hG⟩ := Order.cofinal_meets_idealOfCofinals (P := OrderDual P) p D' i
  exact ⟨q, hG, hD⟩

variable {P : Type*} [Preorder P]

/-- Conditions have a common strengthening. -/
def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

/-- A below-`p` dense set, padded by conditions incompatible with `p`, is dense
in the whole poset. This is how existential local witnesses are obtained
from an external generic filter. -/
theorem dense_local_or_incompatible (p : P) (D : Set P)
    (hD : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ D) :
    Dense {q | q ∈ D ∨ ¬ Compatible q p} := by
  intro q
  by_cases h : Compatible q p
  · obtain ⟨r, hrq, hrp⟩ := h
    obtain ⟨s, hsr, hsD⟩ := hD r hrp
    exact ⟨s, hsr.trans hrq, Or.inl hsD⟩
  · exact ⟨q, le_rfl, Or.inr h⟩

theorem compatible_of_mem (G : GenericFilter P) {p q : P}
    (hp : p ∈ G) (hq : q ∈ G) : Compatible p q := by
  obtain ⟨r, _, hrp, hrq⟩ := G.directed _ hp _ hq
  exact ⟨r, hrp, hrq⟩

/-- Atomic forcing laws on a set of name codes. These are only the equality,
substitution and monotonicity laws; this structure contains no ZF axioms,
Choice or Partition Principle assertions. -/
structure AtomicData (P N : Type*) [Preorder P] where
  EqF : P → N → N → Prop
  MemF : P → N → N → Prop
  eq_mono {p q a b} : q ≤ p → EqF p a b → EqF q a b
  mem_mono {p q a b} : q ≤ p → MemF p a b → MemF q a b
  eq_refl (p a) : EqF p a a
  eq_symm {p a b} : EqF p a b → EqF p b a
  eq_trans {p a b c} : EqF p a b → EqF p b c → EqF p a c
  mem_congr {p a a' b b'} : EqF p a a' → EqF p b b' →
    (MemF p a b ↔ MemF p a' b')

namespace AtomicData
variable {N : Type*} (A : AtomicData P N) (G : GenericFilter P)

/-- Equality of codes after adjoining the generic filter. -/
def EqG (a b : N) : Prop := ∃ p, p ∈ G ∧ A.EqF p a b

/-- Membership before descent to equivalence classes. -/
def MemG (a b : N) : Prop := ∃ p, p ∈ G ∧ A.MemF p a b

theorem eqG_refl (a : N) : A.EqG G a a := by
  obtain ⟨p, hp⟩ := G.nonempty
  exact ⟨p, hp, A.eq_refl p a⟩

theorem eqG_symm {a b : N} (h : A.EqG G a b) : A.EqG G b a := by
  obtain ⟨p, hp, hab⟩ := h
  exact ⟨p, hp, A.eq_symm hab⟩

theorem eqG_trans {a b c : N} (h : A.EqG G a b) (k : A.EqG G b c) :
    A.EqG G a c := by
  obtain ⟨p, hp, hab⟩ := h
  obtain ⟨q, hq, hbc⟩ := k
  obtain ⟨r, hr, hrp, hrq⟩ := G.directed _ hp _ hq
  exact ⟨r, hr, A.eq_trans (A.eq_mono hrp hab) (A.eq_mono hrq hbc)⟩

/-- The setoid of internal name codes; no recursion on membership is used. -/
def nameSetoid : Setoid N where
  r := A.EqG G
  iseqv := ⟨A.eqG_refl G, A.eqG_symm G, A.eqG_trans G⟩

theorem memG_transport {a a' b b' : N} (ha : A.EqG G a a')
    (hb : A.EqG G b b') (hm : A.MemG G a b) : A.MemG G a' b' := by
  obtain ⟨p, hp, haa⟩ := ha
  obtain ⟨q, hq, hbb⟩ := hb
  obtain ⟨r, hr, hab⟩ := hm
  obtain ⟨s, hs, hsp, hsq⟩ := G.directed _ hp _ hq
  obtain ⟨t, ht, hts, htr⟩ := G.directed _ hs _ hr
  refine ⟨t, ht, (A.mem_congr ?_ ?_).1 (A.mem_mono htr hab)⟩
  · exact A.eq_mono (@le_trans P _ t s p hts hsp) haa
  · exact A.eq_mono (@le_trans P _ t s q hts hsq) hbb

theorem memG_congr {a a' b b' : N} (ha : A.EqG G a a') (hb : A.EqG G b b') :
    A.MemG G a b ↔ A.MemG G a' b' :=
  ⟨A.memG_transport G ha hb,
    A.memG_transport G (A.eqG_symm G ha) (A.eqG_symm G hb)⟩

/-- The domain of the extension is a quotient of a set of internal name codes. -/
abbrev Extension := Quotient (A.nameSetoid G)

def nameClass (a : N) : A.Extension G := Quotient.mk _ a

/-- Membership on the quotient is independent of both representatives. -/
def Membership (x y : A.Extension G) : Prop :=
  Quotient.liftOn₂ x y (A.MemG G)
    (fun _ _ _ _ ha hb => propext (A.memG_congr G ha hb))

@[simp] theorem nameClass_eq_iff (a b : N) :
    A.nameClass G a = A.nameClass G b ↔ A.EqG G a b := Quotient.eq

@[simp] theorem membership_nameClass (a b : N) :
    A.Membership G (A.nameClass G a) (A.nameClass G b) ↔ A.MemG G a b := Iff.rfl

end AtomicData

/-- A basis of classical first-order syntax, with last-variable binders.
All formulas in the target language translate to this basis. -/
inductive BasicFormula : ℕ → Type where
  | bot {n} : BasicFormula n
  | mem {n} (x y : Fin n) : BasicFormula n
  | equal {n} (x y : Fin n) : BasicFormula n
  | conj {n} (p q : BasicFormula n) : BasicFormula n
  | neg {n} (p : BasicFormula n) : BasicFormula n
  | ex {n} (p : BasicFormula (n + 1)) : BasicFormula n
  deriving Countable

namespace BasicFormula

def Realize {M : Type*} (E : M → M → Prop) {n} (v : Fin n → M) : BasicFormula n → Prop
  | .bot => False
  | .mem x y => E (v x) (v y)
  | .equal x y => v x = v y
  | .conj p q => Realize E v p ∧ Realize E v q
  | .neg p => ¬ Realize E v p
  | .ex p => ∃ x : M, Realize E (Fin.snoc v x) p

end BasicFormula

namespace AtomicData
variable {N : Type*} (A : AtomicData P N)

/-- Formula-by-formula forcing: existential forcing is local density, NOT a
maximum principle or selection of a single global witness name. -/
def Force (A : AtomicData P N) {n} (v : Fin n → N) (p : P) : BasicFormula n → Prop
  | .bot => False
  | .mem x y => A.MemF p (v x) (v y)
  | .equal x y => A.EqF p (v x) (v y)
  | .conj φ ψ => A.Force v p φ ∧ A.Force v p ψ
  | .neg φ => ∀ q, q ≤ p → ¬ A.Force v q φ
  | .ex φ => ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : N, A.Force (Fin.snoc v x) r φ

theorem force_mono {n} (φ : BasicFormula n) (v : Fin n → N) {p q : P}
    (hqp : q ≤ p) (h : A.Force v p φ) : A.Force v q φ := by
  induction φ with
  | bot => exact h
  | mem => exact A.mem_mono hqp h
  | equal => exact A.eq_mono hqp h
  | conj φ ψ hφ hψ => exact ⟨hφ v h.1, hψ v h.2⟩
  | neg φ _ => exact fun r hr => h r (hr.trans hqp)
  | ex φ _ => exact fun r hr => h r (hr.trans hqp)

/-- Conditions deciding the fixed standard formula at a fixed tuple of names. -/
def decisions {n} (φ : BasicFormula n) (v : Fin n → N) : Set P :=
  {p | A.Force v p φ ∨ A.Force v p (.neg φ)}

theorem decisions_dense {n} (φ : BasicFormula n) (v : Fin n → N) :
    Dense (A.decisions φ v) := by
  intro p
  by_cases h : ∃ q, q ≤ p ∧ A.Force v q φ
  · obtain ⟨q, hqp, hq⟩ := h
    exact ⟨q, hqp, Or.inl hq⟩
  · refine ⟨p, le_rfl, Or.inr ?_⟩
    intro q hqp hq
    exact h ⟨q, hqp, hq⟩

/-- Local existential witnesses, together with conditions which force that
there are no witnesses. A generic must meet this uniformly dense set. -/
def witnesses {n} (φ : BasicFormula (n + 1)) (v : Fin n → N) : Set P :=
  {p | (∃ x, A.Force (Fin.snoc v x) p φ) ∨ A.Force v p (.neg (.ex φ))}

theorem witnesses_dense {n} (φ : BasicFormula (n + 1)) (v : Fin n → N) :
    Dense (A.witnesses φ v) := by
  intro p
  by_cases h : ∃ q, q ≤ p ∧ ∃ x, A.Force (Fin.snoc v x) q φ
  · obtain ⟨q, hqp, hq⟩ := h
    exact ⟨q, hqp, Or.inl hq⟩
  · refine ⟨p, le_rfl, Or.inr ?_⟩
    intro q hqp hq
    obtain ⟨r, hrq, hr⟩ := hq q le_rfl
    exact h ⟨r, hrq.trans hqp, hr⟩

/-- All the dense sets needed for the external induction on standard formulas.
Because each formula has finitely many free variables, the requests are
countable whenever the set of name codes is countable. -/
abbrev Request (N : Type*) :=
  (Σ n, BasicFormula n × (Fin n → N)) ⊕ (Σ n, BasicFormula (n + 1) × (Fin n → N))

def requestSet : Request N → Set P
  | .inl ⟨_, φ, v⟩ => A.decisions φ v
  | .inr ⟨_, φ, v⟩ => A.witnesses φ v

theorem requestSet_dense (i : Request N) : Dense (A.requestSet i) := by
  rcases i with ⟨n, φ, v⟩ | ⟨n, φ, v⟩
  · exact A.decisions_dense φ v
  · exact A.witnesses_dense φ v

/-- A filter meets the decision and local-witness dense sets for each fixed
standard formula and tuple. This property is constructed below; it is not a
truth lemma or an assumption that any set-theoretic axiom is forced. -/
def IsGeneric (G : GenericFilter P) : Prop :=
  (∀ n (φ : BasicFormula n) (v : Fin n → N),
    ∃ p, p ∈ G ∧ p ∈ A.decisions φ v) ∧
  (∀ n (φ : BasicFormula (n + 1)) (v : Fin n → N),
    ∃ p, p ∈ G ∧ p ∈ A.witnesses φ v)

/-- Choose a filter through a prescribed condition, meeting any specified
countable family of dense sets as well as every standard formula request. -/
theorem exists_generic [Countable N] {I : Type*} [Countable I]
    (D : I → Set P) (hD : ∀ i, Dense (D i)) (p : P) :
    ∃ G : GenericFilter P, p ∈ G ∧ (∀ i, ∃ q, q ∈ G ∧ q ∈ D i) ∧ A.IsGeneric G := by
  let D' : I ⊕ Request N → Set P := Sum.elim D A.requestSet
  have dense' : ∀ i, Dense (D' i) := by
    intro i
    cases i with
    | inl i => exact hD i
    | inr i => exact A.requestSet_dense i
  obtain ⟨G, hp, hG⟩ := exists_generic_through D' dense' p
  refine ⟨G, hp, (fun i => hG (.inl i)), ?_, ?_⟩
  · intro n φ v
    exact hG (.inr (.inl ⟨n, φ, v⟩))
  · intro n φ v
    exact hG (.inr (.inr ⟨n, φ, v⟩))

/-- Truth in the quotient of names. The proof is an external induction on the
finite formula, never on the membership relation or rank of a name code.
Existential witnesses are obtained locally, without a maximum principle. -/
theorem truth (G : GenericFilter P) (hG : A.IsGeneric G)
    {n} (φ : BasicFormula n) (v : Fin n → N) :
    BasicFormula.Realize (A.Membership G) (A.nameClass G ∘ v) φ ↔
      ∃ p, p ∈ G ∧ A.Force v p φ := by
  induction φ with
  | bot => simp [BasicFormula.Realize, Force]
  | mem x y => rfl
  | equal x y => exact A.nameClass_eq_iff G (v x) (v y)
  | conj φ ψ hφ hψ =>
      change (_ ∧ _) ↔ _
      rw [hφ v, hψ v]
      constructor
      · rintro ⟨⟨p, hp, hpφ⟩, ⟨q, hq, hqψ⟩⟩
        obtain ⟨r, hr, hrp, hrq⟩ := G.directed _ hp _ hq
        exact ⟨r, hr, A.force_mono φ v hrp hpφ, A.force_mono ψ v hrq hqψ⟩
      · rintro ⟨p, hp, hpφ, hpψ⟩
        exact ⟨⟨p, hp, hpφ⟩, ⟨p, hp, hpψ⟩⟩
  | neg φ hφ =>
      change (¬ _) ↔ _
      rw [hφ v]
      constructor
      · intro hn
        obtain ⟨p, hp, hdec⟩ := hG.1 _ φ v
        rcases hdec with hpos | hneg
        · exact (hn ⟨p, hp, hpos⟩).elim
        · exact ⟨p, hp, hneg⟩
      · rintro ⟨p, hp, hneg⟩ ⟨q, hq, hpos⟩
        obtain ⟨r, _, hrp, hrq⟩ := G.directed _ hp _ hq
        exact hneg r hrp (A.force_mono φ v hrq hpos)
  | ex φ hφ =>
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨a, rfl⟩ := Quotient.exists_rep x
        have hx' : BasicFormula.Realize (A.Membership G)
            (A.nameClass G ∘ Fin.snoc v a) φ := by
          rw [Fin.comp_snoc]
          exact hx
        obtain ⟨p, hp, hpφ⟩ := (hφ (Fin.snoc v a)).1 hx'
        refine ⟨p, hp, ?_⟩
        intro q hqp
        exact ⟨q, le_rfl, a, A.force_mono φ (Fin.snoc v a) hqp hpφ⟩
      · rintro ⟨p, hp, hpex⟩
        obtain ⟨q, hq, hqw⟩ := hG.2 _ φ v
        rcases hqw with ⟨a, ha⟩ | hno
        · refine ⟨A.nameClass G a, ?_⟩
          have hx := (hφ (Fin.snoc v a)).2 ⟨q, hq, ha⟩
          rw [Fin.comp_snoc] at hx
          exact hx
        · obtain ⟨r, _, hrp, hrq⟩ := G.directed _ hp _ hq
          exact (hno r hrq (A.force_mono (.ex φ) v hrp hpex)).elim

end AtomicData
end ForcingQuotient

namespace Formula
open ForcingQuotient

/-- Translation to the finite Boolean/existential basis used in the quotient
truth proof. This changes no set-theoretic predicate or quantifier domain. -/
def toBasic {n} : Formula n → BasicFormula n
  | .bot => .bot
  | .mem x y => .mem x y
  | .equal x y => .equal x y
  | .imp φ ψ => .neg (.conj (toBasic φ) (.neg (toBasic ψ)))
  | .conj φ ψ => .conj (toBasic φ) (toBasic ψ)
  | .disj φ ψ => .neg (.conj (.neg (toBasic φ)) (.neg (toBasic ψ)))
  | .all φ => .neg (.ex (.neg (toBasic φ)))
  | .ex φ => .ex (toBasic φ)

/-- Classical truth is invariant under the translation to the basis. -/
theorem realize_toBasic {M : Type*} (E : M → M → Prop) {n}
    (φ : Formula n) (v : Fin n → M) :
    BasicFormula.Realize E v φ.toBasic ↔ Realize E v φ := by
  classical
  induction φ with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ hφ hψ =>
      simp only [toBasic, BasicFormula.Realize, hφ, hψ, Realize]
      tauto
  | conj φ ψ hφ hψ => simp only [toBasic, BasicFormula.Realize, hφ, hψ, Realize]
  | disj φ ψ hφ hψ =>
      simp only [toBasic, BasicFormula.Realize, hφ, hψ, Realize]
      tauto
  | all φ hφ => simp only [toBasic, BasicFormula.Realize, hφ, Realize, not_exists, not_not]
  | ex φ hφ => simp only [toBasic, BasicFormula.Realize, hφ, Realize]

end Formula

namespace ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

/-- The quotient truth lemma for the entire syntax used in the target
statement, including implication, disjunction and universal quantification. -/
theorem formula_truth (G : GenericFilter P) (hG : A.IsGeneric G)
    {n} (φ : Formula n) (v : Fin n → N) :
    Formula.Realize (A.Membership G) (A.nameClass G ∘ v) φ ↔
      ∃ p, p ∈ G ∧ A.Force v p φ.toBasic := by
  rw [← Formula.realize_toBasic]
  exact A.truth G hG φ.toBasic v

/-- The induced quotient satisfies exactly the sentences forced somewhere in
the generic filter. This is a general logical equivalence, not a construction
forcing the particular target theory. -/
theorem models_iff (G : GenericFilter P) (hG : A.IsGeneric G) (T : Theory) :
    Models (A.Membership G) T ↔
      ∀ φ ∈ T, ∃ p, p ∈ G ∧ A.Force Fin.elim0 p φ.toBasic := by
  have h₀ : A.nameClass G ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → A.Extension G) :=
    Subsingleton.elim _ _
  unfold Models
  apply forall_congr'
  intro φ
  apply forall_congr'
  intro _
  simpa only [h₀] using A.formula_truth G hG φ Fin.elim0

/-- General forcing-to-consistency soundness for countable names. This theorem
is uniform in the theory `T`; it does not assert that the target theory is
forced. Producing its atomic data and proving all of the forced-axiom premises
for the paper's symmetric system remain separate, uncompleted obligations. -/
theorem consistent_of_forcing [Countable N] [Nonempty N] (p₀ : P) {T : Theory}
    (h : ∀ φ ∈ T, A.Force Fin.elim0 p₀ φ.toBasic) : Consistent T := by
  obtain ⟨G, hp₀, _, hG⟩ := A.exists_generic
    (I := Empty) Empty.elim (fun i => nomatch i) p₀
  let _ : Nonempty (A.Extension G) :=
    ⟨A.nameClass G (Classical.choice (inferInstance : Nonempty N))⟩
  apply consistent_of_model (A.Membership G)
  exact (A.models_iff G hG T).2 (fun φ hφ => ⟨p₀, hp₀, h φ hφ⟩)

end ForcingQuotient.AtomicData
end PartitionConsistency

end OAI
