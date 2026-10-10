import Mathlib.SetTheory.Cardinal.Arithmetic

namespace OAI


namespace PartitionPilot.Forcing

section

universe u
variable {P : Type u} [Preorder P]

def Dense (D : Set P) : Prop := ∀ p, ∃ q, q ≤ p ∧ q ∈ D

def DownwardClosed (D : Set P) : Prop := ∀ ⦃p q⦄, q ≤ p → p ∈ D → q ∈ D

def CountablyClosed (P : Type u) [Preorder P] : Prop :=
  ∀ chain : Nat → P, Antitone chain → ∃ lower, ∀ n, lower ≤ chain n

structure ConditionFilter (P : Type u) [Preorder P] where
  mem : P → Prop
  nonempty : ∃ p, mem p
  upward : ∀ ⦃p q⦄, mem p → p ≤ q → mem q
  directed : ∀ ⦃p q⦄, mem p → mem q → ∃ r, mem r ∧ r ≤ p ∧ r ≤ q

namespace ConditionFilter

def Meets (F : ConditionFilter P) (D : Set P) : Prop := ∃ p, F.mem p ∧ p ∈ D

def GenericFor (F : ConditionFilter P) (family : Set (Set P)) : Prop :=
  ∀ D ∈ family, Dense D → F.Meets D

theorem top_mem [OrderTop P] (F : ConditionFilter P) : F.mem ⊤ := by
  rcases F.nonempty with ⟨p, hp⟩
  exact F.upward hp le_top

theorem compatible (F : ConditionFilter P) {p q : P} (hp : F.mem p) (hq : F.mem q) :
    ∃ r, r ≤ p ∧ r ≤ q := by
  rcases F.directed hp hq with ⟨r, _, rp, rq⟩
  exact ⟨r, rp, rq⟩

end ConditionFilter

end



section

universe u v

structure CountableCondition (I : Type u) (A : Type v) where
  value : I → Option A
  countable_domain : Set.Countable {i | value i ≠ none}

namespace CountableCondition
variable {I : Type u} {A : Type v}

theorem ext {p q : CountableCondition I A} (values : p.value = q.value) : p = q := by
  cases p
  cases q
  cases values
  rfl

instance : PartialOrder (CountableCondition I A) where
  le p q := ∀ i a, q.value i = some a → p.value i = some a
  le_refl _ _ _ h := h
  le_trans _ _ _ h1 h2 i a h := h1 i a (h2 i a h)
  le_antisymm p q hpq hqp := by
    apply ext
    funext i
    cases hp : p.value i with
    | none =>
      cases hq : q.value i with
      | none => rfl
      | some a =>
        have impossible := hpq i a hq
        rw [hp] at impossible
        contradiction
    | some a => exact (hqp i a hp).symm

def domain (p : CountableCondition I A) : Set I := {i | p.value i ≠ none}

def empty : CountableCondition I A where
  value _ := none
  countable_domain := by simp

instance : OrderTop (CountableCondition I A) where
  top := empty
  le_top p i a h := by cases h

theorem value_eq_of_le {p q : CountableCondition I A} (le : p ≤ q) (i : I)
    (defined : i ∈ q.domain) : p.value i = q.value i := by
  cases h : q.value i with
  | none => exact False.elim (defined h)
  | some a => exact le i a h

theorem domain_mono {p q : CountableCondition I A} (le : p ≤ q) : q.domain ⊆ p.domain := by
  intro i hi
  change p.value i ≠ none
  rw [value_eq_of_le le i hi]
  exact hi

noncomputable def assign (p : CountableCondition I A) (i : I) (a : A) : CountableCondition I A := by
  classical
  refine ⟨fun j => if j = i then some a else p.value j, ?_⟩
  apply (p.countable_domain.insert i).mono
  intro j hj
  by_cases eq : j = i
  · exact Or.inl eq
  · exact Or.inr (by simpa only [Set.mem_ofPred_eq, ite_eq_right eq] using hj)

theorem assign_same (p : CountableCondition I A) (i : I) (a : A) :
    (p.assign i a).value i = some a := by
  classical
  simp [assign]

theorem assign_other (p : CountableCondition I A) (i j : I) (a : A) (ne : j ≠ i) :
    (p.assign i a).value j = p.value j := by
  classical
  simp only [assign, ite_eq_right ne]

theorem assign_le (p : CountableCondition I A) (i : I) (a : A) (fresh : p.value i = none) :
    p.assign i a ≤ p := by
  intro j b hb
  by_cases eq : j = i
  · subst j
    rw [fresh] at hb
    contradiction
  · rw [assign_other p i j a eq]
    exact hb

def definedAt (i : I) : Set (CountableCondition I A) := {p | p.value i ≠ none}

theorem definedAt_downwardClosed (i : I) : DownwardClosed (definedAt (A := A) i) := by
  intro p q le hp
  exact domain_mono le hp

theorem definedAt_dense [Nonempty A] (i : I) : Dense (definedAt (A := A) i) := by
  classical
  intro p
  by_cases defined : p.value i ≠ none
  · exact ⟨p, le_rfl, defined⟩
  · have fresh : p.value i = none := not_ne_iff.1 defined
    let a : A := Classical.choice inferInstance
    refine ⟨p.assign i a, assign_le p i a fresh, ?_⟩
    change (p.assign i a).value i ≠ none
    rw [assign_same]
    exact Option.some_ne_none _

theorem compatible_values {p q : CountableCondition I A} (compatible : ∃ r, r ≤ p ∧ r ≤ q)
    {i : I} {a b : A} (ha : p.value i = some a) (hb : q.value i = some b) : a = b := by
  rcases compatible with ⟨r, rp, rq⟩
  exact Option.some.inj ((rp i a ha).symm.trans (rq i b hb))

end CountableCondition
end



section

universe u
variable {P : Type u} [Preorder P]

theorem exists_filter_meeting_sequence (p : P) (D : Nat → Set P)
    (dense : ∀ n, Dense (D n)) :
    ∃ H : ConditionFilter P, H.mem p ∧ ∀ n, H.Meets (D n) := by
  classical
  let next (n : Nat) (q : P) : P := Classical.choose (dense n q)
  have next_le (n : Nat) (q : P) : next n q ≤ q := (Classical.choose_spec (dense n q)).1
  have next_mem (n : Nat) (q : P) : next n q ∈ D n := (Classical.choose_spec (dense n q)).2
  let chain : Nat → P := Nat.rec p next
  have step (n : Nat) : chain (n + 1) ≤ chain n := next_le n (chain n)
  have down : Antitone chain := antitone_nat_of_succ_le step
  let H : ConditionFilter P := {
    mem := fun q => ∃ n, chain n ≤ q
    nonempty := ⟨p, 0, le_rfl⟩
    upward := by
      rintro q r ⟨n, nq⟩ qr
      exact ⟨n, nq.trans qr⟩
    directed := by
      rintro q r ⟨n, nq⟩ ⟨m, mr⟩
      exact ⟨chain (max n m), ⟨max n m, le_rfl⟩,
        (down (le_max_left n m)).trans nq, (down (le_max_right n m)).trans mr⟩ }
  exact ⟨H, ⟨0, le_rfl⟩, fun n => ⟨chain (n + 1), ⟨n + 1, le_rfl⟩, next_mem n (chain n)⟩⟩

theorem exists_generic_for_countable_family (p : P) (family : Set (Set P))
    (small : family.Countable) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor family := by
  classical
  let listed := Set.enumerateCountable small (Set.univ : Set P)
  let D (n : Nat) : Set P := if Dense (listed n) then listed n else Set.univ
  have dense (n : Nat) : Dense (D n) := by
    dsimp [D]
    split_ifs with h
    · exact h
    · exact fun q => ⟨q, le_rfl, Set.mem_univ q⟩
  obtain ⟨H, hp, meets⟩ := exists_filter_meeting_sequence p D dense
  refine ⟨H, hp, ?_⟩
  intro E hE hDense
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate small (Set.univ : Set P) hE
  have eq : D n = E := by
    dsimp [D, listed]
    simp only [hn, ite_eq_left hDense]
  exact eq ▸ meets n






def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

def DenseBelow (p : P) (D : Set P) : Prop := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ D

def Localized (p : P) (D : Set P) : Set P := {q | q ∈ D ∨ ¬ Compatible q p}

theorem localized_dense {p : P} {D : Set P} (dense : DenseBelow p D) : Dense (Localized p D) := by
  classical
  intro q
  by_cases compat : Compatible q p
  · obtain ⟨r, rq, rp⟩ := compat
    obtain ⟨t, tr, ht⟩ := dense r rp
    exact ⟨t, tr.trans rq, Or.inl ht⟩
  · exact ⟨q, le_rfl, Or.inr compat⟩

theorem ConditionFilter.meets_below (H : ConditionFilter P) {family : Set (Set P)}
    (generic : H.GenericFor family) {p : P} (hp : H.mem p) {D : Set P}
    (registered : Localized p D ∈ family) (dense : DenseBelow p D) : H.Meets D := by
  obtain ⟨q, hq, good | bad⟩ := generic _ registered (localized_dense dense)
  · exact ⟨q, hq, good⟩
  · exact False.elim (bad (H.compatible hq hp))

theorem denseBelow_mono {p : P} {D E : Set P} (dense : DenseBelow p D) (included : D ⊆ E) :
    DenseBelow p E := by
  intro q qp
  obtain ⟨r, rq, hr⟩ := dense q qp
  exact ⟨r, rq, included hr⟩






theorem dense_countable_intersection (closed : CountablyClosed P)
    (D : Nat → Set P) (dense : ∀ n, Dense (D n))
    (open_ : ∀ n, DownwardClosed (D n)) : Dense {p | ∀ n, p ∈ D n} := by
  classical
  intro p
  let next (n : Nat) (q : P) : P := Classical.choose (dense n q)
  have next_le (n : Nat) (q : P) : next n q ≤ q := (Classical.choose_spec (dense n q)).1
  have next_mem (n : Nat) (q : P) : next n q ∈ D n := (Classical.choose_spec (dense n q)).2
  let chain : Nat → P := Nat.rec p next
  have step (n : Nat) : chain (n + 1) ≤ chain n := next_le n (chain n)
  rcases closed chain (antitone_nat_of_succ_le step) with ⟨q, lower⟩
  refine ⟨q, lower 0, ?_⟩
  intro n
  exact open_ n (lower (n + 1)) (next_mem n (chain n))

theorem dense_simultaneous_witnesses (closed : CountablyClosed P)
    {A : Nat → Type*} (R : P → (n : Nat) → A n → Prop)
    (monotone : ∀ ⦃p q⦄, q ≤ p → ∀ n a, R p n a → R q n a)
    (dense : ∀ n, Dense {p | ∃ a, R p n a}) :
    Dense {p | ∃ f : ∀ n, A n, ∀ n, R p n (f n)} := by
  intro p
  rcases dense_countable_intersection closed (fun n => {p | ∃ a, R p n a}) dense
    (fun n _ _ le ⟨a, ha⟩ => ⟨a, monotone le n a ha⟩) p with ⟨q, qp, all⟩
  exact ⟨q, qp, Classical.axiomOfChoice all⟩

end



namespace CountableCondition

universe u v
variable {I : Type u} {A : Type v}

def Agrees (p q : CountableCondition I A) : Prop :=
  ∀ i a b, p.value i = some a → q.value i = some b → a = b

theorem agrees_symm {p q : CountableCondition I A} (h : Agrees p q) : Agrees q p :=
  fun i a b ha hb => (h i b a hb ha).symm

noncomputable def merge (p q : CountableCondition I A) : CountableCondition I A where
  value i := match p.value i with
    | some a => some a
    | none => q.value i
  countable_domain := by
    apply (p.countable_domain.union q.countable_domain).mono
    intro i hi
    cases hp : p.value i with
    | none => exact Or.inr (by simpa only [Set.mem_ofPred_eq, hp] using hi)
    | some a => exact Or.inl (by
        change p.value i ≠ none
        rw [hp]
        exact Option.some_ne_none _)

theorem merge_le_left (p q : CountableCondition I A) : merge p q ≤ p := by
  intro i a ha
  change (match p.value i with | some a => some a | none => q.value i) = some a
  rw [ha]

theorem merge_le_right {p q : CountableCondition I A} (agree : Agrees p q) : merge p q ≤ q := by
  intro i b hb
  change (match p.value i with | some a => some a | none => q.value i) = some b
  cases hp : p.value i with
  | none => exact hb
  | some a => exact congrArg some (agree i a b hp hb)

theorem merge_value {p q : CountableCondition I A} (agree : Agrees p q) (i : I) (a : A) :
    (merge p q).value i = some a ↔ p.value i = some a ∨ q.value i = some a := by
  constructor
  · intro h
    cases hp : p.value i with
    | none => exact Or.inr (by simpa only [merge, hp] using h)
    | some b => exact Or.inl (by simpa only [merge, hp] using h)
  · rintro (hp | hq)
    · exact merge_le_left p q i a hp
    · exact merge_le_right agree i a hq

theorem merge_agrees {p q r : CountableCondition I A} (pq : Agrees p q)
    (pr : Agrees p r) (qr : Agrees q r) : Agrees (merge p q) r := by
  intro i a b hab hr
  obtain hp | hq := (merge_value pq i a).1 hab
  · exact pr i a b hp hr
  · exact qr i a b hq hr

theorem three_agree_common {p q r : CountableCondition I A}
    (pq : Agrees p q) (pr : Agrees p r) (qr : Agrees q r) :
    ∃ t, t ≤ p ∧ t ≤ q ∧ t ≤ r := by
  refine ⟨merge (merge p q) r, ?_, ?_, merge_le_right (merge_agrees pq pr qr)⟩
  · exact (merge_le_left _ _).trans (merge_le_left _ _)
  · exact (merge_le_left _ _).trans (merge_le_right pq)






noncomputable def unionValue (chain : Nat → CountableCondition I A) (i : I) : Option A := by
  classical
  exact if h : ∃ a, ∃ n, (chain n).value i = some a then some (Classical.choose h) else none

theorem unionValue_domain (chain : Nat → CountableCondition I A) :
    {i | unionValue chain i ≠ none} ⊆ ⋃ n, (chain n).domain := by
  classical
  intro i hi
  by_cases h : ∃ a, ∃ n, (chain n).value i = some a
  · rcases h with ⟨a, n, ha⟩
    apply Set.mem_iUnion.2 ⟨n, ?_⟩
    change (chain n).value i ≠ none
    rw [ha]
    exact Option.some_ne_none _
  · have value : unionValue chain i = none := by simp only [unionValue, dite_eq_right h]
    exact False.elim (hi value)

theorem unionValue_extends (chain : Nat → CountableCondition I A) (decreasing : Antitone chain)
    (n : Nat) (i : I) (a : A) (value : (chain n).value i = some a) :
    unionValue chain i = some a := by
  classical
  have h : ∃ a, ∃ n, (chain n).value i = some a := ⟨a, n, value⟩
  rw [unionValue, dite_eq_left h]
  rcases Classical.choose_spec h with ⟨m, hm⟩
  have compatible : ∃ r, r ≤ chain m ∧ r ≤ chain n :=
    ⟨chain (max m n), decreasing (le_max_left _ _), decreasing (le_max_right _ _)⟩
  exact congrArg some (compatible_values compatible hm value)

noncomputable def chainUnion (chain : Nat → CountableCondition I A) : CountableCondition I A where
  value := unionValue chain
  countable_domain := (Set.countable_iUnion (fun n => (chain n).countable_domain)).mono
    (unionValue_domain chain)

theorem chainUnion_le (chain : Nat → CountableCondition I A) (decreasing : Antitone chain)
    (n : Nat) : chainUnion chain ≤ chain n :=
  unionValue_extends chain decreasing n

theorem countablyClosed : CountablyClosed (CountableCondition I A) :=
  fun chain decreasing => ⟨chainUnion chain, chainUnion_le chain decreasing⟩

end CountableCondition



section

universe u v

structure DecisionSystem (P : Type u) [Preorder P] (A : Nat → Type v) where
  decides : P → (n : Nat) → A n → Prop
  persistent : ∀ ⦃p q⦄, q ≤ p → ∀ n a, decides p n a → decides q n a
  unique : ∀ p n a b, decides p n a → decides p n b → a = b
  dense : ∀ n, Dense {p | ∃ a, decides p n a}

namespace DecisionSystem
variable {P : Type u} [Preorder P] {A : Nat → Type v} (d : DecisionSystem P A)

def commonDecisions : Set P := {p | ∃ f : ∀ n, A n, ∀ n, d.decides p n (f n)}

theorem commonDecisions_dense (closed : CountablyClosed P) : Dense d.commonDecisions :=
  dense_simultaneous_witnesses closed d.decides d.persistent d.dense

theorem commonDecisions_downwardClosed : DownwardClosed d.commonDecisions := by
  rintro p q le ⟨f, hf⟩
  exact ⟨f, fun n => d.persistent le n (f n) (hf n)⟩

def Realizes (F : ConditionFilter P) (f : ∀ n, A n) : Prop :=
  ∀ n, ∃ p, F.mem p ∧ d.decides p n (f n)

theorem compatible_decisions (F : ConditionFilter P) {p q : P} (hp : F.mem p) (hq : F.mem q)
    (n : Nat) (a b : A n) (ha : d.decides p n a) (hb : d.decides q n b) : a = b := by
  rcases F.directed hp hq with ⟨r, _, rp, rq⟩
  exact d.unique r n a b (d.persistent rp n a ha) (d.persistent rq n b hb)

theorem realizes_unique (F : ConditionFilter P) {f g : ∀ n, A n}
    (hf : d.Realizes F f) (hg : d.Realizes F g) : f = g := by
  funext n
  rcases hf n with ⟨p, hp, ha⟩
  rcases hg n with ⟨q, hq, hb⟩
  exact d.compatible_decisions F hp hq n (f n) (g n) ha hb

theorem common_condition_decides (F : ConditionFilter P) (meets : F.Meets d.commonDecisions)
    (f : ∀ n, A n) (realizes : d.Realizes F f) :
    ∃ p, F.mem p ∧ ∀ n, d.decides p n (f n) := by
  rcases meets with ⟨p, hp, g, hg⟩
  have eq : g = f := d.realizes_unique F (fun n => ⟨p, hp, hg n⟩) realizes
  exact ⟨p, hp, eq ▸ hg⟩

theorem generic_condition_decides (closed : CountablyClosed P) (F : ConditionFilter P)
    (family : Set (Set P)) (generic : F.GenericFor family) (present : d.commonDecisions ∈ family)
    (f : ∀ n, A n) (realizes : d.Realizes F f) :
    ∃ p, F.mem p ∧ ∀ n, d.decides p n (f n) :=
  d.common_condition_decides F (generic _ present (d.commonDecisions_dense closed)) f realizes

end DecisionSystem
end



namespace CountableCondition

universe u v
variable {I : Type u} {A : Type v} (F : ConditionFilter (CountableCondition I A))

theorem exists_value (meets : ∀ i, F.Meets (definedAt i)) (i : I) :
    ∃ a, ∃ p, F.mem p ∧ p.value i = some a := by
  rcases meets i with ⟨p, hp, defined⟩
  cases value : p.value i with
  | none => exact False.elim (defined value)
  | some a => exact ⟨a, p, hp, value⟩

noncomputable def readValue (meets : ∀ i, F.Meets (definedAt i)) (i : I) : A :=
  Classical.choose (exists_value F meets i)

theorem readValue_realized (meets : ∀ i, F.Meets (definedAt i)) (i : I) :
    ∃ p, F.mem p ∧ p.value i = some (readValue F meets i) :=
  Classical.choose_spec (exists_value F meets i)

theorem readValue_of_condition (meets : ∀ i, F.Meets (definedAt i))
    {p : CountableCondition I A} (hp : F.mem p) {i : I} {a : A} (value : p.value i = some a) :
    readValue F meets i = a := by
  rcases readValue_realized F meets i with ⟨q, hq, read⟩
  exact compatible_values (F.compatible hq hp) read value

theorem readValue_iff (meets : ∀ i, F.Meets (definedAt i)) (i : I) (a : A) :
    readValue F meets i = a ↔ ∃ p, F.mem p ∧ p.value i = some a := by
  constructor
  · intro eq
    exact eq ▸ readValue_realized F meets i
  · rintro ⟨p, hp, value⟩
    exact readValue_of_condition F meets hp value

omit F in
def coordinateDecisions [Nonempty A] (index : Nat → I) :
    DecisionSystem (CountableCondition I A) (fun _ => A) where
  decides p n a := p.value (index n) = some a
  persistent := by
    intro p q le n a value
    exact le (index n) a value
  unique _ _ _ _ h1 h2 := Option.some.inj (h1.symm.trans h2)
  dense n := by
    intro p
    rcases definedAt_dense (A := A) (index n) p with ⟨q, qp, defined⟩
    cases value : q.value (index n) with
    | none => exact False.elim (defined value)
    | some a => exact ⟨q, qp, a, value⟩

omit F in
theorem coordinate_commonDecisions_dense [Nonempty A] (index : Nat → I) :
    Dense (coordinateDecisions (A := A) index).commonDecisions :=
  (coordinateDecisions index).commonDecisions_dense countablyClosed

theorem readValue_sequence_decided [Nonempty A] (meets : ∀ i, F.Meets (definedAt i))
    (index : Nat → I) (family : Set (Set (CountableCondition I A))) (generic : F.GenericFor family)
    (present : (coordinateDecisions (A := A) index).commonDecisions ∈ family) :
    ∃ p, F.mem p ∧ ∀ n, p.value (index n) = some (readValue F meets (index n)) :=
  (coordinateDecisions index).generic_condition_decides countablyClosed F family generic present
    (fun n => readValue F meets (index n)) (fun n => readValue_realized F meets (index n))

end CountableCondition

end PartitionPilot.Forcing

end OAI
