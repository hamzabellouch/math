import Mathlib
import OAI.SetTheory.PartitionConsistency.Logic.Proofs
import OAI.SetTheory.PartitionConsistency.Logic.CountableModels

namespace OAI

namespace PartitionConsistency
/-! Countable Henkin completeness for the target proof calculus. -/

deriving instance Countable for Formula

namespace Formula

@[simp] theorem liftRen_id (n : ℕ) : liftRen (id : Fin n → Fin n) = id := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem liftRen_comp {n m k : ℕ} (r : Fin n → Fin m) (s : Fin m → Fin k) :
    liftRen (s ∘ r) = liftRen s ∘ liftRen r := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem rename_id {n} (φ : Formula n) : φ.rename id = φ := by
  induction φ with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ hφ hψ => simp [rename, hφ, hψ]
  | conj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | disj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | all φ hφ => simp [rename, hφ]
  | ex φ hφ => simp [rename, hφ]

@[simp] theorem rename_comp {n m k} (φ : Formula n)
    (r : Fin n → Fin m) (s : Fin m → Fin k) :
    (φ.rename r).rename s = φ.rename (s ∘ r) := by
  induction φ generalizing m k with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ hφ hψ => simp [rename, hφ, hψ]
  | conj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | disj φ ψ hφ hψ => simp [rename, hφ, hψ]
  | all φ hφ => simp [rename, hφ, liftRen_comp]
  | ex φ hφ => simp [rename, hφ, liftRen_comp]

/-- Instantiation after renaming the free variables extends that renaming by
one chosen variable; this is the capture-avoidance identity for witnesses. -/
@[simp] theorem instantiate_rename {n m} (φ : Formula (n + 1))
    (r : Fin n → Fin m) (t : Fin m) :
    (φ.rename (liftRen r)).instantiate t = φ.rename (Fin.snoc r t) := by
  rw [instantiate, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem rename_snoc_castSucc_last {n} (φ : Formula (n + 1)) :
    φ.rename (Fin.snoc Fin.castSucc (Fin.last n)) = φ := by
  have h : Fin.snoc Fin.castSucc (Fin.last n) = (id : Fin (n+1) → Fin (n+1)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h, rename_id]

@[simp] theorem rename_instantiate {n m} (φ : Formula (n+1))
    (r : Fin n → Fin m) (t : Fin n) :
    (φ.instantiate t).rename r = (φ.rename (liftRen r)).instantiate (r t) := by
  rw [instantiate_rename, instantiate, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end Formula

namespace Derives

theorem eq_symm {n} {Γ : Set (Formula n)} {s t : Fin n} (h : Derives Γ (.equal s t)) :
    Derives Γ (.equal t s) := by
  have hp := Derives.eqSubst (.equal (Fin.last n) s.castSucc) h (by
    simpa [Formula.instantiate, Formula.rename] using (Derives.eqRefl (Γ := Γ) s))
  simpa [Formula.instantiate, Formula.rename] using hp

theorem eq_trans {n} {Γ : Set (Formula n)} {s t u : Fin n}
    (h : Derives Γ (.equal s t)) (h' : Derives Γ (.equal t u)) :
    Derives Γ (.equal s u) := by
  have hp := Derives.eqSubst (.equal s.castSucc (Fin.last n)) h' (by
    simpa [Formula.instantiate, Formula.rename] using h)
  simpa [Formula.instantiate, Formula.rename] using hp

theorem mem_congr {n} {Γ : Set (Formula n)} {s t s' t' : Fin n}
    (hs : Derives Γ (.equal s s')) (ht : Derives Γ (.equal t t'))
    (hm : Derives Γ (.mem s t)) : Derives Γ (.mem s' t') := by
  have h₁ : Derives Γ (.mem s' t) := by
    have hp := Derives.eqSubst (.mem (Fin.last n) t.castSucc) hs (by
      simpa [Formula.instantiate, Formula.rename] using hm)
    simpa [Formula.instantiate, Formula.rename] using hp
  have hp := Derives.eqSubst (.mem s'.castSucc (Fin.last n)) ht (by
    simpa [Formula.instantiate, Formula.rename] using h₁)
  simpa [Formula.instantiate, Formula.rename] using hp

end Derives

namespace Completeness

/-- Consistency of an open context, with its displayed finite variable supply. -/
def ContextConsistent {n} (Γ : Set (Formula n)) : Prop := ¬ Derives Γ .bot

/-- Enlarging the variable supply is conservative for a nonempty supply.
A retraction substitutes an existing variable for every extra variable. -/
theorem lift_consistent {n m} {Γ : Set (Formula n)} (hn : 0 < n) (hnm : n ≤ m)
    (hΓ : ContextConsistent Γ) :
    ContextConsistent (Formula.rename (Fin.castLE hnm) '' Γ) := by
  intro hd
  let r : Fin m → Fin n := fun i => if h : i.val < n then ⟨i.val, h⟩ else ⟨0, hn⟩
  have hr : r ∘ Fin.castLE hnm = id := by
    funext i
    simp [r]
  apply hΓ
  have h := hd.rename r
  simpa [Formula.rename, Set.image_image, hr] using h

/-- One of the two decisions can always be added without contradiction. -/
theorem consistent_decision {n} {Γ : Set (Formula n)} (hΓ : ContextConsistent Γ)
    (φ : Formula n) :
    ContextConsistent (insert φ Γ) ∨ ContextConsistent (insert φ.neg Γ) := by
  classical
  by_cases hp : ContextConsistent (insert φ Γ)
  · exact Or.inl hp
  · right
    intro hn
    apply hΓ
    exact Derives.impE (Derives.impI (not_not.mp hp)) (Derives.classical hn)

/-- Henkin conditions are genuine consistent first-order contexts. No
satisfiability or model-existence assertion occurs in their definition. -/
structure Condition where
  size : ℕ
  positive : 0 < size
  context : Set (Formula size)
  consistent : ContextConsistent context

namespace Condition

/-- A stronger condition may have more variables and more assumptions. -/
instance : Preorder Condition where
  le q p := ∃ h : p.size ≤ q.size,
    Formula.rename (Fin.castLE h) '' p.context ⊆ q.context
  le_refl p := by
    refine ⟨le_rfl, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have h : (Fin.castLE (le_rfl : p.size ≤ p.size)) = id := rfl
    simpa [h] using hφ
  le_trans q p r hqp hpr := by
    obtain ⟨hqp, hpq⟩ := hqp
    obtain ⟨hpr, hrp⟩ := hpr
    refine ⟨hpr.trans hqp, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hmiddle := hpq ⟨_, hrp ⟨φ, hφ, rfl⟩, rfl⟩
    simpa only [Formula.rename_comp, Function.comp_def, Fin.castLE_castLE] using hmiddle

/-- The canonical embedding of the old variables into a stronger condition. -/
def emb {q p : Condition} (h : q ≤ p) : Fin p.size → Fin q.size := Fin.castLE h.choose

@[simp] theorem emb_val {q p : Condition} (h : q ≤ p) (i : Fin p.size) :
    (emb h i).val = i.val := rfl

/-- Derivations are preserved by extension of conditions. -/
theorem transport {q p : Condition} (h : q ≤ p) {φ : Formula p.size}
    (hd : Derives p.context φ) : Derives q.context (φ.rename (emb h)) :=
  (hd.rename (emb h)).weaken h.choose_spec

def grow (p : Condition) (m : ℕ) (h : p.size ≤ m) : Condition :=
  ⟨m, p.positive.trans_le h, Formula.rename (Fin.castLE h) '' p.context,
    lift_consistent p.positive h p.consistent⟩

theorem grow_le (p : Condition) (m : ℕ) (h : p.size ≤ m) : p.grow m h ≤ p :=
  ⟨h, Set.Subset.rfl⟩

def add (p : Condition) (φ : Formula p.size)
    (h : ContextConsistent (insert φ p.context)) : Condition :=
  ⟨p.size, p.positive, insert φ p.context, h⟩

theorem add_le (p : Condition) (φ : Formula p.size)
    (h : ContextConsistent (insert φ p.context)) : p.add φ h ≤ p := by
  refine ⟨le_rfl, ?_⟩
  rintro _ ⟨ψ, hψ, rfl⟩
  have hid : (Fin.castLE (le_rfl : p.size ≤ p.size)) = id := rfl
  change ψ.rename (Fin.castLE (le_rfl : p.size ≤ p.size)) ∈ insert φ p.context
  rw [hid, Formula.rename_id]
  exact Set.mem_insert_of_mem φ hψ

/-- A condition can always accommodate a given finite tuple of variable codes. -/
theorem bound (p : Condition) {n} (v : Fin n → ℕ) :
    ∃ q : Condition, q ≤ p ∧ ∃ w : Fin n → Fin q.size, ∀ i, (w i).val = v i := by
  let m := max p.size (Finset.univ.sup v + 1)
  have hpm : p.size ≤ m := le_max_left _ _
  let q := p.grow m hpm
  have hv : ∀ i, v i < q.size := by
    intro i
    exact (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))).trans_le (le_max_right _ _)
  exact ⟨q, p.grow_le m hpm, fun i => ⟨v i, hv i⟩, fun _ => rfl⟩

end Condition

/-- Extending the variable map by a new last variable is the binder lift. -/
@[simp] theorem snoc_castSucc {n m} (w : Fin n → Fin m) :
    Fin.snoc (Fin.castSucc ∘ w) (Fin.last m) = Formula.liftRen w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Formula.liftRen]

namespace Condition

/-- Adding a fresh local witness is consistent when existence is derivable.
This is justified by the eigenvariable rule, not by a model assumption. -/
def exWitness (p : Condition) (φ : Formula (p.size + 1))
    (hφ : Derives p.context (.ex φ)) : Condition where
  size := p.size + 1
  positive := Nat.zero_lt_succ _
  context := insert φ (Formula.raise '' p.context)
  consistent := fun hc => p.consistent (Derives.exE hφ hc)

theorem exWitness_le (p : Condition) (φ : Formula (p.size + 1))
    (hφ : Derives p.context (.ex φ)) : p.exWitness φ hφ ≤ p := by
  refine ⟨Nat.le_succ _, ?_⟩
  rintro _ ⟨ψ, hψ, rfl⟩
  exact Or.inr ⟨ψ, hψ, rfl⟩

/-- A negated universal has a consistent fresh counterexample context. -/
def allCounterexample (p : Condition) (φ : Formula (p.size + 1))
    (hφ : Derives p.context (Formula.all φ).neg) : Condition where
  size := p.size + 1
  positive := Nat.zero_lt_succ _
  context := insert φ.neg (Formula.raise '' p.context)
  consistent := fun hc =>
    p.consistent (Derives.impE hφ (Derives.allI (Derives.classical hc)))

theorem allCounterexample_le (p : Condition) (φ : Formula (p.size + 1))
    (hφ : Derives p.context (Formula.all φ).neg) : p.allCounterexample φ hφ ≤ p := by
  refine ⟨Nat.le_succ _, ?_⟩
  rintro _ ⟨ψ, hψ, rfl⟩
  exact Or.inr ⟨ψ, hψ, rfl⟩

end Condition

/-- All finite tuples are explicitly included, so this construction treats
all parameters, not just sentences or quantifier-free formulas. -/
def decisions {n} (φ : Formula n) (v : Fin n → ℕ) : Set Condition :=
  {c | ∃ w : Fin n → Fin c.size, (∀ i, (w i).val = v i) ∧
    (Derives c.context (φ.rename w) ∨ Derives c.context (φ.neg.rename w))}

def exWitnesses {n} (φ : Formula (n+1)) (v : Fin n → ℕ) : Set Condition :=
  {c | ∃ w : Fin n → Fin c.size, (∀ i, (w i).val = v i) ∧
    (Derives c.context ((Formula.ex φ).neg.rename w) ∨
      ∃ a : Fin c.size, Derives c.context (φ.rename (Fin.snoc w a)))}

def allCounterexamples {n} (φ : Formula (n+1)) (v : Fin n → ℕ) : Set Condition :=
  {c | ∃ w : Fin n → Fin c.size, (∀ i, (w i).val = v i) ∧
    (Derives c.context ((Formula.all φ).rename w) ∨
      ∃ a : Fin c.size, Derives c.context (φ.neg.rename (Fin.snoc w a)))}

theorem decisions_dense {n} (φ : Formula n) (v : Fin n → ℕ) :
    ForcingQuotient.Dense (decisions φ v) := by
  intro p
  obtain ⟨q, hqp, w, hw⟩ := p.bound v
  rcases consistent_decision q.consistent (φ.rename w) with hpos | hneg
  · exact ⟨q.add (φ.rename w) hpos, (q.add_le _ _).trans hqp, w, hw,
      Or.inl (Derives.hyp (Set.mem_insert _ _))⟩
  · exact ⟨q.add (φ.rename w).neg hneg, (q.add_le _ _).trans hqp, w, hw,
      Or.inr (Derives.hyp (Set.mem_insert _ _))⟩

theorem exWitnesses_dense {n} (φ : Formula (n+1)) (v : Fin n → ℕ) :
    ForcingQuotient.Dense (exWitnesses φ v) := by
  intro p
  obtain ⟨q, hqp, w, hw⟩ := p.bound v
  let ψ := φ.rename (Formula.liftRen w)
  rcases consistent_decision q.consistent (.ex ψ) with hpos | hneg
  · let r := q.add (.ex ψ) hpos
    have hex : Derives r.context (.ex ψ) := Derives.hyp (Set.mem_insert _ _)
    let s := r.exWitness ψ hex
    refine ⟨s, (r.exWitness_le ψ hex).trans ((q.add_le _ _).trans hqp),
      Fin.castSucc ∘ w, hw, Or.inr ⟨Fin.last r.size, ?_⟩⟩
    dsimp only [s, r, Condition.exWitness, Condition.add]
    rw [snoc_castSucc]
    exact Derives.hyp (Set.mem_insert _ _)
  · exact ⟨q.add (Formula.ex ψ).neg hneg, (q.add_le _ _).trans hqp, w, hw,
      Or.inl (Derives.hyp (Set.mem_insert _ _))⟩

theorem allCounterexamples_dense {n} (φ : Formula (n+1)) (v : Fin n → ℕ) :
    ForcingQuotient.Dense (allCounterexamples φ v) := by
  intro p
  obtain ⟨q, hqp, w, hw⟩ := p.bound v
  let ψ := φ.rename (Formula.liftRen w)
  rcases consistent_decision q.consistent (.all ψ) with hpos | hneg
  · exact ⟨q.add (.all ψ) hpos, (q.add_le _ _).trans hqp, w, hw,
      Or.inl (Derives.hyp (Set.mem_insert _ _))⟩
  · let r := q.add (Formula.all ψ).neg hneg
    have hn : Derives r.context (Formula.all ψ).neg := Derives.hyp (Set.mem_insert _ _)
    let s := r.allCounterexample ψ hn
    refine ⟨s, (r.allCounterexample_le ψ hn).trans ((q.add_le _ _).trans hqp),
      Fin.castSucc ∘ w, hw, Or.inr ⟨Fin.last r.size, ?_⟩⟩
    dsimp only [s, r, Condition.allCounterexample, Condition.add]
    rw [snoc_castSucc]
    exact Derives.hyp (Set.mem_insert _ _)

abbrev GenericFilter := ForcingQuotient.GenericFilter Condition

/-- A filter meeting every decision and every local quantifier-witness request. -/
def IsHenkin (G : GenericFilter) : Prop :=
  (∀ n (φ : Formula n) (v : Fin n → ℕ), ∃ p ∈ G, p ∈ decisions φ v) ∧
  (∀ n (φ : Formula (n+1)) (v : Fin n → ℕ), ∃ p ∈ G, p ∈ exWitnesses φ v) ∧
  (∀ n (φ : Formula (n+1)) (v : Fin n → ℕ), ∃ p ∈ G, p ∈ allCounterexamples φ v)

/-- The countable Henkin construction, using only syntactic consistency. -/
theorem exists_henkin (p₀ : Condition) :
    ∃ G : GenericFilter, p₀ ∈ G ∧ IsHenkin G := by
  let Request (j : ℕ) := Σ n, Formula (n+j) × (Fin n → ℕ)
  let D : Request 0 ⊕ (Request 1 ⊕ Request 1) → Set Condition :=
    fun i => match i with
      | .inl ⟨_, φ, v⟩ => decisions φ v
      | .inr (.inl ⟨_, φ, v⟩) => exWitnesses φ v
      | .inr (.inr ⟨_, φ, v⟩) => allCounterexamples φ v
  have hD : ∀ i, ForcingQuotient.Dense (D i) := by
    rintro (⟨n, φ, v⟩ | ⟨n, φ, v⟩ | ⟨n, φ, v⟩)
    · exact decisions_dense φ v
    · exact exWitnesses_dense φ v
    · exact allCounterexamples_dense φ v
  obtain ⟨G, hp₀, hG⟩ := ForcingQuotient.exists_generic_through D hD p₀
  exact ⟨G, hp₀, (fun n φ v => hG (.inl ⟨n, φ, v⟩)),
    (fun n φ v => hG (.inr (.inl ⟨n, φ, v⟩))),
    (fun n φ v => hG (.inr (.inr ⟨n, φ, v⟩)))⟩

/-- Eventual derivability in the directed filter, with all free variables
interpreted as natural-number constant codes. -/
def Proven (G : GenericFilter) {n} (φ : Formula n) (v : Fin n → ℕ) : Prop :=
  ∃ p ∈ G, ∃ w : Fin n → Fin p.size,
    (∀ i, (w i).val = v i) ∧ Derives p.context (φ.rename w)

namespace Proven

variable {G : GenericFilter} {n : ℕ} {φ ψ : Formula n} {v : Fin n → ℕ}

/-- Any existing representation of the tuple can be extended to one carrying
the given derivation. Directedness, not an assumed complete theory, is used. -/
theorem at_condition (h : Proven G φ v) {p : Condition} (hp : p ∈ G)
    (w : Fin n → Fin p.size) (hw : ∀ i, (w i).val = v i) :
    ∃ q : Condition, q ∈ G ∧ ∃ hqp : q ≤ p,
      Derives q.context (φ.rename (Condition.emb hqp ∘ w)) := by
  obtain ⟨r, hr, u, hu, hd⟩ := h
  obtain ⟨q, hq, hqr, hqp⟩ := G.directed _ hr _ hp
  refine ⟨q, hq, hqp, ?_⟩
  have he : Condition.emb hqr ∘ u = Condition.emb hqp ∘ w := by
    funext i
    apply Fin.ext
    exact (hu i).trans (hw i).symm
  simpa only [Formula.rename_comp, he] using Condition.transport hqr hd

/-- Two eventual derivations with the same tuple can be put into a single
consistent context with exactly the same variable map. -/
theorem joint (hφ : Proven G φ v) (hψ : Proven G ψ v) :
    ∃ p ∈ G, ∃ w : Fin n → Fin p.size, (∀ i, (w i).val = v i) ∧
      Derives p.context (φ.rename w) ∧ Derives p.context (ψ.rename w) := by
  obtain ⟨p, hp, w, hw, hdφ⟩ := hφ
  obtain ⟨q, hq, hqp, hdψ⟩ := hψ.at_condition hp w hw
  refine ⟨q, hq, Condition.emb hqp ∘ w, hw, ?_, hdψ⟩
  simpa only [Formula.rename_comp] using Condition.transport hqp hdφ

theorem not_bot : ¬ Proven G (Formula.bot : Formula n) v := by
  rintro ⟨p, _, _, _, hd⟩
  exact p.consistent hd

theorem conjunction : Proven G (φ.conj ψ) v ↔ Proven G φ v ∧ Proven G ψ v := by
  constructor
  · rintro ⟨p, hp, w, hw, hd⟩
    exact ⟨⟨p, hp, w, hw, hd.conjL⟩, ⟨p, hp, w, hw, hd.conjR⟩⟩
  · rintro ⟨hφ, hψ⟩
    obtain ⟨p, hp, w, hw, hdφ, hdψ⟩ := hφ.joint hψ
    exact ⟨p, hp, w, hw, Derives.conjI hdφ hdψ⟩

theorem apply_imp (hpq : Proven G (φ.imp ψ) v) (hp : Proven G φ v) : Proven G ψ v := by
  obtain ⟨p, hp, w, hw, hd₁, hd₂⟩ := hpq.joint hp
  exact ⟨p, hp, w, hw, Derives.impE hd₁ hd₂⟩

theorem contradict (hn : Proven G φ.neg v) (hp : Proven G φ v) : False :=
  not_bot (hn.apply_imp hp)

variable (hG : IsHenkin G)
include hG

/-- This also supplies a filter condition containing any prescribed finite
collection of constant codes, including codes not used by a formula. -/
theorem tuple (v : Fin n → ℕ) :
    ∃ p ∈ G, ∃ w : Fin n → Fin p.size, ∀ i, (w i).val = v i := by
  obtain ⟨p, hp, w, hw, _⟩ := hG.1 n .bot v
  exact ⟨p, hp, w, hw⟩

theorem decision (φ : Formula n) (v : Fin n → ℕ) :
    Proven G φ v ∨ Proven G φ.neg v := by
  obtain ⟨p, hp, w, hw, hd | hd⟩ := hG.1 n φ v
  · exact Or.inl ⟨p, hp, w, hw, hd⟩
  · exact Or.inr ⟨p, hp, w, hw, hd⟩

theorem negation : Proven G φ.neg v ↔ ¬ Proven G φ v := by
  constructor
  · exact contradict
  · intro hn
    exact (decision hG φ v).resolve_left hn

/-- Full substitution of finite variable tuples, in both directions. The
reverse implication includes variables unused in the substituted formula. -/
theorem rename_iff {m} (φ : Formula n) (r : Fin n → Fin m) (v : Fin m → ℕ) :
    Proven G (φ.rename r) v ↔ Proven G φ (v ∘ r) := by
  constructor
  · rintro ⟨p, hp, w, hw, hd⟩
    refine ⟨p, hp, w ∘ r, (fun i => hw (r i)), ?_⟩
    simpa only [Formula.rename_comp] using hd
  · intro hφ
    obtain ⟨p, hp, w, hw⟩ := tuple hG v
    obtain ⟨q, hq, hqp, hd⟩ := hφ.at_condition hp (w ∘ r) (fun i => hw (r i))
    refine ⟨q, hq, Condition.emb hqp ∘ w, hw, ?_⟩
    simpa only [Formula.rename_comp, Function.comp_assoc] using hd

theorem implication : Proven G (φ.imp ψ) v ↔ (Proven G φ v → Proven G ψ v) := by
  constructor
  · exact apply_imp
  · intro h
    classical
    by_cases hφ : Proven G φ v
    · obtain ⟨p, hp, w, hw, hd⟩ := h hφ
      exact ⟨p, hp, w, hw, Derives.impI (hd.weaken (Set.subset_insert _ _))⟩
    · obtain ⟨p, hp, w, hw, hd⟩ := (negation hG).2 hφ
      refine ⟨p, hp, w, hw, Derives.impI ?_⟩
      exact (Derives.impE (hd.weaken (Set.subset_insert _ _))
        (Derives.hyp (Set.mem_insert _ _))).botE

theorem disjunction : Proven G (φ.disj ψ) v ↔ Proven G φ v ∨ Proven G ψ v := by
  constructor
  · intro h
    classical
    by_cases hφ : Proven G φ v
    · exact Or.inl hφ
    · right
      obtain ⟨p, hp, w, hw, hd, hn⟩ := h.joint ((negation hG).2 hφ)
      refine ⟨p, hp, w, hw, Derives.disjE hd ?_ ?_⟩
      · exact (Derives.impE (hn.weaken (Set.subset_insert _ _))
          (Derives.hyp (Set.mem_insert _ _))).botE
      · exact Derives.hyp (Set.mem_insert _ _)
  · rintro (⟨p, hp, w, hw, hd⟩ | ⟨p, hp, w, hw, hd⟩)
    · exact ⟨p, hp, w, hw, hd.disjL⟩
    · exact ⟨p, hp, w, hw, hd.disjR⟩

omit hG in
/-- Universal elimination is a derivable operation on the eventual theory. -/
theorem all_instance {φ : Formula (n+1)} (h : Proven G (.all φ) v) (t : Fin n) :
    Proven G (φ.instantiate t) v := by
  obtain ⟨p, hp, w, hw, hd⟩ := h
  refine ⟨p, hp, w, hw, ?_⟩
  rw [Formula.rename_instantiate]
  exact Derives.allE (w t) hd

/-- The Henkin requests turn existence into an actual constant-code witness. -/
theorem exists_iff (φ : Formula (n+1)) (v : Fin n → ℕ) :
    Proven G (.ex φ) v ↔ ∃ a : ℕ, Proven G φ (Fin.snoc v a) := by
  constructor
  · intro h
    obtain ⟨p, hp, w, hw, hn | ⟨a, ha⟩⟩ := hG.2.1 n φ v
    · exact (contradict ⟨p, hp, w, hw, hn⟩ h).elim
    · refine ⟨a.val, p, hp, Fin.snoc w a, ?_, ha⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hw]
  · rintro ⟨a, p, hp, w, hw, hd⟩
    refine ⟨p, hp, Fin.init w, ?_, ?_⟩
    · intro i
      simpa only [Fin.init, Fin.snoc_castSucc] using hw i.castSucc
    · apply Derives.exI (w (Fin.last n))
      simpa only [Formula.instantiate_rename, Fin.snoc_init_self] using hd

/-- Universal truth is equivalent to truth for every constant code. The
counterexample requests are essential to the reverse implication. -/
theorem all_iff (φ : Formula (n+1)) (v : Fin n → ℕ) :
    Proven G (.all φ) v ↔ ∀ a : ℕ, Proven G φ (Fin.snoc v a) := by
  constructor
  · intro h a
    have hr : Proven G (Formula.all φ).raise (Fin.snoc v a) := by
      apply (rename_iff hG (.all φ) Fin.castSucc _).2
      simpa only [Fin.snoc_comp_castSucc] using h
    have hi := all_instance hr (Fin.last n)
    simpa only [Formula.raise, Formula.rename, Formula.instantiate_rename,
      Formula.rename_snoc_castSucc_last] using hi
  · intro h
    obtain ⟨p, hp, w, hw, hall | ⟨a, ha⟩⟩ := hG.2.2 n φ v
    · exact ⟨p, hp, w, hw, hall⟩
    · have hn : Proven G φ.neg (Fin.snoc v a.val) := by
        refine ⟨p, hp, Fin.snoc w a, ?_, ha⟩
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hw]
      exact (contradict hn (h a.val)).elim

end Proven

/-- Equality and membership of constant codes in the canonical term model. -/
def EqRel (G : GenericFilter) (a b : ℕ) : Prop :=
  Proven G (.equal (0 : Fin 2) 1) ![a,b]

def MemRel (G : GenericFilter) (a b : ℕ) : Prop :=
  Proven G (.mem (0 : Fin 2) 1) ![a,b]

variable {G : GenericFilter} (hG : IsHenkin G)
include hG

theorem equal_iff {n} (i j : Fin n) (v : Fin n → ℕ) :
    Proven G (.equal i j) v ↔ EqRel G (v i) (v j) := by
  have h := Proven.rename_iff hG (.equal (0 : Fin 2) 1) ![i,j] v
  have hv : v ∘ ![i,j] = ![v i, v j] := by
    funext k
    fin_cases k <;> rfl
  rw [hv] at h
  exact h

theorem mem_iff {n} (i j : Fin n) (v : Fin n → ℕ) :
    Proven G (.mem i j) v ↔ MemRel G (v i) (v j) := by
  have h := Proven.rename_iff hG (.mem (0 : Fin 2) 1) ![i,j] v
  have hv : v ∘ ![i,j] = ![v i, v j] := by
    funext k
    fin_cases k <;> rfl
  rw [hv] at h
  exact h

theorem eqRel_refl (a : ℕ) : EqRel G a a := by
  obtain ⟨p, hp, w, hw⟩ := Proven.tuple hG ![a,a]
  refine ⟨p, hp, w, hw, ?_⟩
  have he : w 0 = w 1 := Fin.ext ((hw 0).trans (hw 1).symm)
  change Derives p.context (.equal (w 0) (w 1))
  rw [he]
  exact Derives.eqRefl _

omit hG in
theorem eqRel_symm {a b : ℕ} (h : EqRel G a b) : EqRel G b a := by
  obtain ⟨p, hp, w, hw, hd⟩ := h
  refine ⟨p, hp, ![w 1, w 0], ?_, hd.eq_symm⟩
  intro i
  fin_cases i <;> simp [hw]

theorem eqRel_trans {a b c : ℕ} (hab : EqRel G a b) (hbc : EqRel G b c) :
    EqRel G a c := by
  have h₁ := (equal_iff hG (0 : Fin 3) 1 ![a,b,c]).2 hab
  have h₂ := (equal_iff hG (1 : Fin 3) 2 ![a,b,c]).2 hbc
  obtain ⟨p, hp, w, hw, hd₁, hd₂⟩ := h₁.joint h₂
  have hc : Proven G (.equal (0 : Fin 3) 2) ![a,b,c] :=
    ⟨p, hp, w, hw, hd₁.eq_trans hd₂⟩
  exact (equal_iff hG (0 : Fin 3) 2 ![a,b,c]).1 hc

theorem memRel_congr {a b a' b' : ℕ} (ha : EqRel G a a') (hb : EqRel G b b') :
    MemRel G a b ↔ MemRel G a' b' := by
  have transport : ∀ {a b a' b' : ℕ}, EqRel G a a' → EqRel G b b' →
      MemRel G a b → MemRel G a' b' := by
    intro a b a' b' ha hb hm
    have h₁ := (equal_iff hG (0 : Fin 4) 2 ![a,b,a',b']).2 ha
    have h₂ := (equal_iff hG (1 : Fin 4) 3 ![a,b,a',b']).2 hb
    have h₃ := (mem_iff hG (0 : Fin 4) 1 ![a,b,a',b']).2 hm
    obtain ⟨p, hp, w, hw, hd₁₂, hd₃⟩ := ((Proven.conjunction).2 ⟨h₁,h₂⟩).joint h₃
    have h' : Proven G (.mem (2 : Fin 4) 3) ![a,b,a',b'] :=
      ⟨p, hp, w, hw, Derives.mem_congr hd₁₂.conjL hd₁₂.conjR hd₃⟩
    exact (mem_iff hG (2 : Fin 4) 3 ![a,b,a',b']).1 h'
  exact ⟨transport ha hb, transport (eqRel_symm ha) (eqRel_symm hb)⟩

/-- Quotient of the natural-number constant codes by their syntactically
provable equality. -/
def termSetoid (G : GenericFilter) (hG : IsHenkin G) : Setoid ℕ where
  r := EqRel G
  iseqv := ⟨eqRel_refl hG, eqRel_symm, eqRel_trans hG⟩

def TermModel (G : GenericFilter) (hG : IsHenkin G) : Type := Quotient (termSetoid G hG)

def termClass (G : GenericFilter) (hG : IsHenkin G) (a : ℕ) : TermModel G hG :=
  Quotient.mk _ a

instance termModel_nonempty : Nonempty (TermModel G hG) := ⟨termClass G hG 0⟩
instance termModel_countable : Countable (TermModel G hG) :=
  inferInstanceAs (Countable (Quotient (termSetoid G hG)))

/-- Membership is independent of representatives because first-order equality
has its actual substitution rule. -/
def termMem (G : GenericFilter) (hG : IsHenkin G) :
    TermModel G hG → TermModel G hG → Prop :=
  Quotient.lift₂ (MemRel G) (fun _ _ _ _ ha hb => propext (memRel_congr hG ha hb))

/-- Truth in the countable term model, for every formula and every tuple of
constant codes. This is syntactic completeness, not compactness assumed as a
premise or semantic consistency used as a definition. -/
theorem term_truth {n} (φ : Formula n) (v : Fin n → ℕ) :
    Formula.Realize (termMem G hG) (termClass G hG ∘ v) φ ↔ Proven G φ v := by
  induction φ with
  | bot => exact ⟨False.elim, Proven.not_bot⟩
  | mem i j => exact (mem_iff hG i j v).symm
  | equal i j => exact Quotient.eq.trans (equal_iff hG i j v).symm
  | conj φ ψ hφ hψ =>
      simp only [Formula.Realize, hφ v, hψ v, Proven.conjunction]
  | imp φ ψ hφ hψ =>
      simp only [Formula.Realize, hφ v, hψ v, Proven.implication hG]
  | disj φ ψ hφ hψ =>
      simp only [Formula.Realize, hφ v, hψ v, Proven.disjunction hG]
  | all φ hφ =>
      rw [Proven.all_iff hG]
      constructor
      · intro h a
        apply (hφ (Fin.snoc v a)).1
        simpa only [Fin.comp_snoc, termClass] using h (termClass G hG a)
      · intro h x
        obtain ⟨a, rfl⟩ := Quotient.exists_rep x
        simpa only [Fin.comp_snoc, termClass] using (hφ (Fin.snoc v a)).2 (h a)
  | ex φ hφ =>
      rw [Proven.exists_iff hG]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨a, rfl⟩ := Quotient.exists_rep x
        refine ⟨a, (hφ (Fin.snoc v a)).1 ?_⟩
        simpa only [Fin.comp_snoc, termClass] using hx
      · rintro ⟨a, ha⟩
        refine ⟨termClass G hG a, ?_⟩
        simpa only [Fin.comp_snoc, termClass] using (hφ (Fin.snoc v a)).2 ha

omit hG in
/-- Countable-model completeness for the actual finite-derivation consistency
predicate used in the target. No transitive or externally well-founded model
is asserted. The domain is concretely a quotient of `ℕ`. -/
theorem exists_countable_model {T : Theory} (hT : Consistent T) :
    ∃ M : Type, Nonempty M ∧ Countable M ∧ ∃ E : M → M → Prop, Models E T := by
  let p₀ : Condition := ⟨1, Nat.zero_lt_succ 0, T.at 1, hT 1⟩
  obtain ⟨G, hp₀, hG⟩ := exists_henkin p₀
  refine ⟨TermModel G hG, inferInstance, inferInstance, termMem G hG, ?_⟩
  intro φ hφ
  have ht := term_truth hG φ Fin.elim0
  have hv : termClass G hG ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → TermModel G hG) :=
    Subsingleton.elim _ _
  rw [hv] at ht
  apply ht.2
  refine ⟨p₀, hp₀, Fin.elim0, (fun i => Fin.elim0 i), Derives.hyp ?_⟩
  exact ⟨φ, hφ, rfl⟩

omit hG in
/-- Equivalence of syntactic consistency and countable nonempty models for
this first-order language. This does not perform the constructible or
symmetric-forcing interpretations required in `main_consistency`. -/
theorem consistent_iff_has_countable_model (T : Theory) :
    Consistent T ↔
      ∃ M : Type, Nonempty M ∧ Countable M ∧ ∃ E : M → M → Prop, Models E T := by
  constructor
  · exact exists_countable_model
  · rintro ⟨M, hM, _, E, hE⟩
    let _ := hM
    exact consistent_of_model E hE

end Completeness
end PartitionConsistency

end OAI
