import Mathlib

namespace OAI



/-! ## Logical and set-forcing foundations -/

/-! Ordinary first-order membership syntax and classical natural deduction.
Consistency is syntactic. The forcing interpretation ranges over all
hereditarily symmetric pure-set names without a rank bound. -/












namespace PartitionConsistency

/-- Pure first-order membership syntax with equality. `n` variables are in scope.
A quantifier binds the last variable in its body. There are no atoms/urelements,
function symbols, constants, semantic predicates, or mathematical assumptions
in this syntax. -/
inductive Formula : ℕ → Type where
  | bot {n} : Formula n
  | mem {n} (x y : Fin n) : Formula n
  | equal {n} (x y : Fin n) : Formula n
  | imp {n} (p q : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | disj {n} (p q : Formula n) : Formula n
  | all {n} (p : Formula (n + 1)) : Formula n
  | ex {n} (p : Formula (n + 1)) : Formula n

namespace Formula

abbrev neg {n} (p : Formula n) : Formula n := p.imp .bot
abbrev iff {n} (p q : Formula n) : Formula n := (p.imp q).conj (q.imp p)

/-- Under a binder, a renaming leaves the newly bound variable bound. -/
def liftRen {n m} (r : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (r i).castSucc)

/-- Capture-avoiding renaming; in this relational language all terms are variables. -/
def rename {n m} (r : Fin n → Fin m) : Formula n → Formula m
  | .bot => .bot
  | .mem x y => .mem (r x) (r y)
  | .equal x y => .equal (r x) (r y)
  | .imp p q => .imp (rename r p) (rename r q)
  | .conj p q => .conj (rename r p) (rename r q)
  | .disj p q => .disj (rename r p) (rename r q)
  | .all p => .all (rename (liftRen r) p)
  | .ex p => .ex (rename (liftRen r) p)

abbrev raise {n} (p : Formula n) : Formula (n + 1) := rename Fin.castSucc p

/-- Substitution of a variable term for the variable just quantified. -/
def instantiate {n} (p : Formula (n + 1)) (x : Fin n) : Formula n :=
  rename (Fin.lastCases x id) p

/-- Universal closure of all the free variables. -/
def close : {n : ℕ} → Formula n → Formula 0
  | 0, p => p
  | _ + 1, p => close (.all p)

/-- Satisfaction in an arbitrary relational structure, not necessarily externally
well founded or transitive. In particular, `E` need not be Lean's membership. -/
def Realize {M : Type*} (E : M → M → Prop) {n} (v : Fin n → M) : Formula n → Prop
  | .bot => False
  | .mem x y => E (v x) (v y)
  | .equal x y => v x = v y
  | .imp p q => Realize E v p → Realize E v q
  | .conj p q => Realize E v p ∧ Realize E v q
  | .disj p q => Realize E v p ∨ Realize E v q
  | .all p => ∀ x : M, Realize E (Fin.snoc v x) p
  | .ex p => ∃ x : M, Realize E (Fin.snoc v x) p

@[simp] theorem snoc_comp_liftRen {M : Type*} {n m} (v : Fin m → M)
    (x : M) (r : Fin n → Fin m) :
    Fin.snoc v x ∘ liftRen r = Fin.snoc (v ∘ r) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftRen]

@[simp] theorem realize_rename {M : Type*} (E : M → M → Prop) {n m}
    (p : Formula n) (r : Fin n → Fin m) (v : Fin m → M) :
    Realize E v (rename r p) ↔ Realize E (v ∘ r) p := by
  induction p generalizing m with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp p q hp hq => simp only [rename, Realize, hp, hq]
  | conj p q hp hq => simp only [rename, Realize, hp, hq]
  | disj p q hp hq => simp only [rename, Realize, hp, hq]
  | all p hp => simp only [rename, Realize, hp, snoc_comp_liftRen]
  | ex p hp => simp only [rename, Realize, hp, snoc_comp_liftRen]

@[simp] theorem realize_raise {M : Type*} (E : M → M → Prop) {n}
    (p : Formula n) (v : Fin n → M) (x : M) :
    Realize E (Fin.snoc v x) p.raise ↔ Realize E v p := by
  rw [realize_rename]
  have h : Fin.snoc v x ∘ Fin.castSucc = v := by
    funext i
    simp
  rw [h]

@[simp] theorem realize_instantiate {M : Type*} (E : M → M → Prop) {n}
    (p : Formula (n + 1)) (t : Fin n) (v : Fin n → M) :
    Realize E v (p.instantiate t) ↔ Realize E (Fin.snoc v (v t)) p := by
  rw [instantiate, realize_rename]
  have h : v ∘ Fin.lastCases t id = Fin.snoc v (v t) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h]

end Formula

abbrev Sentence := Formula 0
abbrev Theory := Set Sentence

/-- Classical first-order natural deduction with equality. Hypotheses may be an
infinite theory, but a derivation is a finite inductive proof. The `allI` and
`exE` rules use a fresh last variable, and shift all assumptions to avoid
capture. We allow finitely many free variables in proofs of closed sentences. -/
inductive Derives : {n : ℕ} → Set (Formula n) → Formula n → Prop where
  | hyp {n} {Γ : Set (Formula n)} {p} : p ∈ Γ → Derives Γ p
  | weaken {n} {Γ Δ : Set (Formula n)} {p} :
      Γ ⊆ Δ → Derives Γ p → Derives Δ p
  | impI {n} {Γ : Set (Formula n)} {p q} :
      Derives (insert p Γ) q → Derives Γ (.imp p q)
  | impE {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.imp p q) → Derives Γ p → Derives Γ q
  | botE {n} {Γ : Set (Formula n)} {p} : Derives Γ .bot → Derives Γ p
  | classical {n} {Γ : Set (Formula n)} {p} :
      Derives (insert p.neg Γ) .bot → Derives Γ p
  | conjI {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ p → Derives Γ q → Derives Γ (.conj p q)
  | conjL {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.conj p q) → Derives Γ p
  | conjR {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.conj p q) → Derives Γ q
  | disjL {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ p → Derives Γ (.disj p q)
  | disjR {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ q → Derives Γ (.disj p q)
  | disjE {n} {Γ : Set (Formula n)} {p q r} :
      Derives Γ (.disj p q) → Derives (insert p Γ) r →
      Derives (insert q Γ) r → Derives Γ r
  | allI {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} :
      Derives (Formula.raise '' Γ) p → Derives Γ (.all p)
  | allE {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (.all p) → Derives Γ (p.instantiate t)
  | exI {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (p.instantiate t) → Derives Γ (.ex p)
  | exE {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} {q : Formula n} :
      Derives Γ (.ex p) → Derives (insert p (Formula.raise '' Γ)) q.raise →
      Derives Γ q
  | eqRefl {n} {Γ : Set (Formula n)} (t : Fin n) : Derives Γ (.equal t t)
  | eqSubst {n} {Γ : Set (Formula n)} {s t : Fin n} (p : Formula (n + 1)) :
      Derives Γ (.equal s t) → Derives Γ (p.instantiate s) →
      Derives Γ (p.instantiate t)
  | rename {n m} {Γ : Set (Formula n)} {p : Formula n} (r : Fin n → Fin m) :
      Derives Γ p → Derives (Formula.rename r '' Γ) (Formula.rename r p)

/-- Sentences are usable as open hypotheses with any finite supply of variables. -/
def Theory.at (T : Theory) (n : ℕ) : Set (Formula n) :=
  Formula.rename Fin.elim0 '' T

/-- Ordinary syntactic consistency: there is no finite natural-deduction proof
of falsity from the theory, with any finite supply of free variables. -/
def Consistent (T : Theory) : Prop := ∀ n, ¬ Derives (T.at n) .bot

/-- A model here is an arbitrary membership structure. This definition places no
external well-foundedness, transitivity, or cardinal assumptions on the model. -/
def Models {M : Type*} (E : M → M → Prop) (T : Theory) : Prop :=
  ∀ p ∈ T, Formula.Realize E Fin.elim0 p

/-- Soundness of the explicitly specified proof calculus. -/
theorem Derives.sound {n} {Γ : Set (Formula n)} {p : Formula n} (h : Derives Γ p)
    {M : Type*} (E : M → M → Prop) (v : Fin n → M)
    (hΓ : ∀ q ∈ Γ, Formula.Realize E v q) : Formula.Realize E v p := by
  induction h with
  | hyp hp => exact hΓ _ hp
  | weaken hsub _ ih => exact ih v (fun q hq => hΓ q (hsub hq))
  | impI _ ih =>
      intro hp
      exact ih v (fun q hq => by
        rcases hq with rfl | hq
        · exact hp
        · exact hΓ _ hq)
  | impE _ _ ih₁ ih₂ => exact ih₁ v hΓ (ih₂ v hΓ)
  | botE _ ih => exact False.elim (ih v hΓ)
  | classical _ ih =>
      by_contra hp
      exact ih v (fun q hq => by
        rcases hq with rfl | hq
        · exact hp
        · exact hΓ _ hq)
  | conjI _ _ ih₁ ih₂ => exact ⟨ih₁ v hΓ, ih₂ v hΓ⟩
  | conjL _ ih => exact (ih v hΓ).1
  | conjR _ ih => exact (ih v hΓ).2
  | disjL _ ih => exact Or.inl (ih v hΓ)
  | disjR _ ih => exact Or.inr (ih v hΓ)
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
      rcases ih₁ v hΓ with hp | hq
      · exact ih₂ v (fun r hr => by
          rcases hr with rfl | hr
          · exact hp
          · exact hΓ _ hr)
      · exact ih₃ v (fun r hr => by
          rcases hr with rfl | hr
          · exact hq
          · exact hΓ _ hr)
  | allI _ ih =>
      intro x
      apply ih (Fin.snoc v x)
      rintro q ⟨r, hr, rfl⟩
      exact (Formula.realize_raise E r v x).2 (hΓ r hr)
  | allE t _ ih =>
      exact (Formula.realize_instantiate E _ t v).2 (ih v hΓ (v t))
  | exI t _ ih =>
      exact ⟨v t, (Formula.realize_instantiate E _ t v).1 (ih v hΓ)⟩
  | exE _ _ ih₁ ih₂ =>
      obtain ⟨x, hx⟩ := ih₁ v hΓ
      apply (Formula.realize_raise E _ v x).1
      apply ih₂ (Fin.snoc v x)
      intro q hq
      rcases hq with rfl | hq
      · exact hx
      · obtain ⟨r, hr, rfl⟩ := hq
        exact (Formula.realize_raise E r v x).2 (hΓ r hr)
  | eqRefl => rfl
  | eqSubst p _ _ ih₁ ih₂ =>
      have he := ih₁ v hΓ
      change v _ = v _ at he
      have hp := ih₂ v hΓ
      rw [Formula.realize_instantiate] at hp
      exact (Formula.realize_instantiate E _ _ _).2 (by simpa only [he] using hp)
  | rename r _ ih =>
      apply (Formula.realize_rename E _ r v).2
      apply ih (v ∘ r)
      intro q hq
      exact (Formula.realize_rename E q r v).1 (hΓ _ ⟨q, hq, rfl⟩)

/-- The final soundness step of the source's metatheoretic argument.  Unlike
`main_consistency`, this helper does not construct any model. -/
theorem consistent_of_model {M : Type*} [Nonempty M] (E : M → M → Prop)
    {T : Theory} (h : Models E T) : Consistent T := by
  intro n d
  let v : Fin n → M := fun _ => Classical.choice ‹Nonempty M›
  apply d.sound E v
  rintro q ⟨r, hr, rfl⟩
  apply (Formula.realize_rename E r Fin.elim0 v).2
  have h₀ : v ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h₀]
  exact h r hr

/-! Finite support for first-order proof translation. -/

namespace Derives

/-- Removing an introduced assumption from a support leaves a subset of the
original context. -/
private theorem drop_subset {α : Type*} {S Γ : Set α} {p : α}
    (h : S ⊆ insert p Γ) : S \ {p} ⊆ Γ := by
  rintro q ⟨hq, hne⟩
  rcases h hq with heq | hq'
  · exact (hne heq).elim
  · exact hq'

private theorem subset_insert_drop {α : Type*} (S : Set α) (p : α) :
    S ⊆ insert p (S \ {p}) := by
  intro q hq
  by_cases hp : q = p
  · exact Or.inl hp
  · exact Or.inr ⟨hq, hp⟩

/-- Every natural-deduction proof uses only finitely many assumptions, even
though its context is allowed to be an arbitrary set. This statement covers
both variable renaming and the fresh-variable quantifier rules. -/
theorem finite_support {n} {Γ : Set (Formula n)} {p : Formula n} (h : Derives Γ p) :
    ∃ Δ : Set (Formula n), Δ.Finite ∧ Δ ⊆ Γ ∧ Derives Δ p := by
  induction h with
  | hyp hp =>
      exact ⟨{_}, Set.finite_singleton _, Set.singleton_subset_iff.mpr hp,
        Derives.hyp (Set.mem_singleton _)⟩
  | weaken hsub _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ.trans hsub, hd⟩
  | @impI n Γ p q _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ \ {p}, hf.sdiff, drop_subset hΔ,
        Derives.impI (hd.weaken (subset_insert_drop Δ p))⟩
  | impE _ _ ih₁ ih₂ =>
      obtain ⟨Δ₁, hf₁, hΔ₁, hd₁⟩ := ih₁
      obtain ⟨Δ₂, hf₂, hΔ₂, hd₂⟩ := ih₂
      exact ⟨Δ₁ ∪ Δ₂, hf₁.union hf₂, Set.union_subset hΔ₁ hΔ₂,
        Derives.impE (hd₁.weaken Set.subset_union_left)
          (hd₂.weaken Set.subset_union_right)⟩
  | botE _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, hd.botE⟩
  | @classical n Γ p _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ \ {p.neg}, hf.sdiff, drop_subset hΔ,
        Derives.classical (hd.weaken (subset_insert_drop Δ p.neg))⟩
  | conjI _ _ ih₁ ih₂ =>
      obtain ⟨Δ₁, hf₁, hΔ₁, hd₁⟩ := ih₁
      obtain ⟨Δ₂, hf₂, hΔ₂, hd₂⟩ := ih₂
      exact ⟨Δ₁ ∪ Δ₂, hf₁.union hf₂, Set.union_subset hΔ₁ hΔ₂,
        Derives.conjI (hd₁.weaken Set.subset_union_left)
          (hd₂.weaken Set.subset_union_right)⟩
  | conjL _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, hd.conjL⟩
  | conjR _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, hd.conjR⟩
  | disjL _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, hd.disjL⟩
  | disjR _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, hd.disjR⟩
  | @disjE n Γ p q r _ _ _ ih₁ ih₂ ih₃ =>
      obtain ⟨Δ₁, hf₁, hΔ₁, hd₁⟩ := ih₁
      obtain ⟨Δ₂, hf₂, hΔ₂, hd₂⟩ := ih₂
      obtain ⟨Δ₃, hf₃, hΔ₃, hd₃⟩ := ih₃
      let Δ := Δ₁ ∪ ((Δ₂ \ {p}) ∪ (Δ₃ \ {q}))
      have h₂ : Δ₂ \ {p} ⊆ Δ :=
        Set.subset_union_left.trans Set.subset_union_right
      have h₃ : Δ₃ \ {q} ⊆ Δ :=
        Set.subset_union_right.trans Set.subset_union_right
      refine ⟨Δ, hf₁.union (hf₂.sdiff.union hf₃.sdiff),
        Set.union_subset hΔ₁ (Set.union_subset (drop_subset hΔ₂) (drop_subset hΔ₃)), ?_⟩
      apply Derives.disjE (hd₁.weaken Set.subset_union_left)
      · exact hd₂.weaken ((subset_insert_drop Δ₂ p).trans (Set.insert_subset_insert h₂))
      · exact hd₃.weaken ((subset_insert_drop Δ₃ q).trans (Set.insert_subset_insert h₃))
  | allI _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      obtain ⟨D, hD, hDf, heq⟩ := hf.exists_subset_finite_image_eq hΔ
      refine ⟨D, hDf, hD, Derives.allI ?_⟩
      rwa [heq]
  | allE t _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, Derives.allE t hd⟩
  | exI t _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Δ, hf, hΔ, Derives.exI t hd⟩
  | @exE n Γ p q _ _ ih₁ ih₂ =>
      obtain ⟨Δ₁, hf₁, hΔ₁, hd₁⟩ := ih₁
      obtain ⟨Δ₂, hf₂, hΔ₂, hd₂⟩ := ih₂
      obtain ⟨D, hD, hDf, heq⟩ :=
        (show (Δ₂ \ {p}).Finite from hf₂.sdiff).exists_subset_finite_image_eq (drop_subset hΔ₂)
      refine ⟨Δ₁ ∪ D, hf₁.union hDf, Set.union_subset hΔ₁ hD, ?_⟩
      apply Derives.exE (hd₁.weaken Set.subset_union_left)
      apply Derives.weaken ?_ hd₂
      apply (subset_insert_drop Δ₂ p).trans
      apply Set.insert_subset_insert
      rw [← heq]
      exact Set.image_mono Set.subset_union_right
  | eqRefl t =>
      exact ⟨∅, Set.finite_empty, Set.empty_subset _, Derives.eqRefl t⟩
  | eqSubst p _ _ ih₁ ih₂ =>
      obtain ⟨Δ₁, hf₁, hΔ₁, hd₁⟩ := ih₁
      obtain ⟨Δ₂, hf₂, hΔ₂, hd₂⟩ := ih₂
      exact ⟨Δ₁ ∪ Δ₂, hf₁.union hf₂, Set.union_subset hΔ₁ hΔ₂,
        Derives.eqSubst p (hd₁.weaken Set.subset_union_left)
          (hd₂.weaken Set.subset_union_right)⟩
  | rename r _ ih =>
      obtain ⟨Δ, hf, hΔ, hd⟩ := ih
      exact ⟨Formula.rename r '' Δ, hf.image _, Set.image_mono hΔ,
        Derives.rename r hd⟩

end Derives

/-- Restricting the axioms of a consistent theory preserves consistency. -/
theorem Consistent.mono {T S : Theory} (h : Consistent T) (hST : S ⊆ T) :
    Consistent S := by
  intro n hd
  apply h n
  exact hd.weaken (Set.image_mono hST)

/-- A finite contradiction from a theory already follows from a finite
subtheory. This formulates the finite-axiom step needed by the source's
proof-translation alternative, without assuming that translation exists. -/
theorem consistent_iff_finite {T : Theory} :
    Consistent T ↔ ∀ S : Theory, S.Finite → S ⊆ T → Consistent S := by
  constructor
  · intro h S _ hST
    exact h.mono hST
  · intro h n hd
    obtain ⟨Δ, hf, hΔ, hd'⟩ := hd.finite_support
    obtain ⟨S, hST, hSf, heq⟩ := hf.exists_subset_finite_image_eq hΔ
    apply h S hSf hST n
    simpa only [Theory.at, heq] using hd'

-- The set-theoretic sentences are defined below, with only first-order binders.
end PartitionConsistency

end OAI
