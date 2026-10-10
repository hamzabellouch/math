import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.AtomicForcing
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingQuotient

namespace OAI

namespace PartitionConsistency.ForcingQuotient.AtomicData

variable {P N : Type*} [Preorder P] (A : AtomicData P N)

/-- Induction through the defined logical forcing relation propagates a
condition/name automorphism from the atomic cases to each fixed formula.
The existential clause remains density of local witnesses. -/
theorem force_symmetry (e : P ≃o P) (f : N ≃ N)
    (heq : ∀ p a b, A.EqF p a b ↔ A.EqF (e p) (f a) (f b))
    (hmem : ∀ p a b, A.MemF p a b ↔ A.MemF (e p) (f a) (f b))
    {n} (φ : BasicFormula n) (v : Fin n → N) (p : P) :
    A.Force v p φ ↔ A.Force (f ∘ v) (e p) φ := by
  induction φ generalizing p with
  | bot => rfl
  | mem a b => exact hmem p (v a) (v b)
  | equal a b => exact heq p (v a) (v b)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v p) (ihψ v p)
  | neg φ ih =>
    constructor
    · intro h q hqp hq
      obtain ⟨q, rfl⟩ := e.surjective q
      exact h q (e.le_iff_le.mp hqp) ((ih v q).mpr hq)
    · intro h q hqp hq
      exact h (e q) (e.monotone hqp) ((ih v q).mp hq)
  | ex φ ih =>
    constructor
    · intro h q hqp
      obtain ⟨q, rfl⟩ := e.surjective q
      obtain ⟨r, hrq, x, hx⟩ := h q (e.le_iff_le.mp hqp)
      refine ⟨e r, e.monotone hrq, f x, ?_⟩
      simpa only [Fin.comp_snoc] using (ih (Fin.snoc v x) r).mp hx
    · intro h q hqp
      obtain ⟨r, hrq, x, hx⟩ := h (e q) (e.monotone hqp)
      obtain ⟨r, rfl⟩ := e.surjective r
      obtain ⟨x, rfl⟩ := f.surjective x
      refine ⟨r, e.le_iff_le.mp hrq, x, (ih (Fin.snoc v x) r).mpr ?_⟩
      simpa only [Fin.comp_snoc] using hx

end PartitionConsistency.ForcingQuotient.AtomicData



namespace PartitionConsistency.ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

/-- The ordinary forcing relation is regular: density of atomic forcing below
`p` already implies forcing at `p`. This property is separately verified by the
actual name recursion, not assumed for any target axiom. -/
def Regular : Prop :=
  (∀ p a b, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.EqF r a b) → A.EqF p a b) ∧
  (∀ p a b, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.MemF r a b) → A.MemF p a b)

/-- Dense closure extends from the atomic relations to every fixed formula. -/
theorem force_of_dense (hA : A.Regular) {n} (φ : BasicFormula n) (v : Fin n → N)
    (p : P) (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.Force v r φ) : A.Force v p φ := by
  induction φ generalizing p with
  | bot => obtain ⟨r, _, hr⟩ := h p le_rfl; exact hr
  | mem x y => exact hA.2 p (v x) (v y) h
  | equal x y => exact hA.1 p (v x) (v y) h
  | conj φ ψ ihφ ihψ =>
    refine ⟨ihφ v p ?_, ihψ v p ?_⟩
    · intro q hq
      obtain ⟨r, hrq, hr⟩ := h q hq
      exact ⟨r, hrq, hr.1⟩
    · intro q hq
      obtain ⟨r, hrq, hr⟩ := h q hq
      exact ⟨r, hrq, hr.2⟩
  | neg φ _ =>
    intro q hqp hq
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact hr r le_rfl (A.force_mono φ v hrq hq)
  | ex φ _ =>
    intro q hqp
    obtain ⟨r, hrq, hr⟩ := h q hqp
    obtain ⟨s, hsr, hs⟩ := hr r le_rfl
    exact ⟨s, hsr.trans hrq, hs⟩

theorem exists_force_neg (hA : A.Regular) {n} (φ : BasicFormula n) (v : Fin n → N)
    {p : P} (h : ¬ A.Force v p φ) : ∃ q, q ≤ p ∧ A.Force v q (.neg φ) := by
  classical
  by_contra! hn
  apply h
  apply A.force_of_dense hA φ v
  intro q hqp
  have hnot := hn q hqp
  change ¬ (∀ r, r ≤ q → ¬ A.Force v r φ) at hnot
  push Not at hnot
  exact hnot

/-- Forcing in the full syntax of the statement is the previously defined
Boolean/existential-basis forcing, with no change of quantifier domain. -/
def ForceFormula {n} (v : Fin n → N) (p : P) (φ : Formula n) : Prop :=
  A.Force v p φ.toBasic

theorem forceFormula_mono {n} {v : Fin n → N} {p q : P} {φ : Formula n}
    (hqp : q ≤ p) (h : A.ForceFormula v p φ) : A.ForceFormula v q φ :=
  A.force_mono φ.toBasic v hqp h

theorem forceFormula_of_dense (hA : A.Regular) {n} {v : Fin n → N} {p : P}
    {φ : Formula n} (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.ForceFormula v r φ) :
    A.ForceFormula v p φ := A.force_of_dense hA φ.toBasic v p h

@[simp] theorem forceFormula_bot {n} (v : Fin n → N) (p : P) :
    A.ForceFormula v p .bot ↔ False := Iff.rfl

@[simp] theorem forceFormula_mem {n} (v : Fin n → N) (p : P) (x y : Fin n) :
    A.ForceFormula v p (.mem x y) ↔ A.MemF p (v x) (v y) := Iff.rfl

@[simp] theorem forceFormula_equal {n} (v : Fin n → N) (p : P) (x y : Fin n) :
    A.ForceFormula v p (.equal x y) ↔ A.EqF p (v x) (v y) := Iff.rfl

@[simp] theorem forceFormula_conj {n} (v : Fin n → N) (p : P) (φ ψ : Formula n) :
    A.ForceFormula v p (.conj φ ψ) ↔ A.ForceFormula v p φ ∧ A.ForceFormula v p ψ := Iff.rfl

theorem forceFormula_imp (hA : A.Regular) {n} (v : Fin n → N) (p : P) (φ ψ : Formula n) :
    A.ForceFormula v p (.imp φ ψ) ↔
      ∀ q, q ≤ p → A.ForceFormula v q φ → A.ForceFormula v q ψ := by
  constructor
  · intro h q hqp hq
    by_contra! hn
    obtain ⟨r, hrq, hr⟩ := A.exists_force_neg hA ψ.toBasic v hn
    exact h r (hrq.trans hqp) ⟨A.forceFormula_mono hrq hq, hr⟩
  · intro h q hqp hq
    exact hq.2 q le_rfl (h q hqp hq.1)

theorem forceFormula_neg (hA : A.Regular) {n} (v : Fin n → N) (p : P) (φ : Formula n) :
    A.ForceFormula v p φ.neg ↔ ∀ q, q ≤ p → ¬ A.ForceFormula v q φ :=
  A.forceFormula_imp hA v p φ .bot

theorem forceFormula_disj {n} (v : Fin n → N) (p : P) (φ ψ : Formula n) :
    A.ForceFormula v p (.disj φ ψ) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ (A.ForceFormula v r φ ∨ A.ForceFormula v r ψ) := by
  classical
  constructor
  · intro h q hqp
    by_contra! hn
    apply h q hqp
    exact ⟨fun r hrq hr => (hn r hrq).1 hr, fun r hrq hr => (hn r hrq).2 hr⟩
  · intro h q hqp hq
    obtain ⟨r, hrq, hr | hr⟩ := h q hqp
    · exact hq.1 r hrq hr
    · exact hq.2 r hrq hr

@[simp] theorem forceFormula_ex {n} (v : Fin n → N) (p : P) (φ : Formula (n+1)) :
    A.ForceFormula v p (.ex φ) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x, A.ForceFormula (Fin.snoc v x) r φ := Iff.rfl

theorem forceFormula_all (hA : A.Regular) {n} (v : Fin n → N) (p : P)
    (φ : Formula (n+1)) : A.ForceFormula v p (.all φ) ↔
      ∀ x, A.ForceFormula (Fin.snoc v x) p φ := by
  constructor
  · intro h x
    by_contra! hn
    obtain ⟨q, hqp, hq⟩ := A.exists_force_neg hA φ.toBasic (Fin.snoc v x) hn
    apply h q hqp
    intro r hrq
    exact ⟨r, le_rfl, x, A.force_mono (.neg φ.toBasic) (Fin.snoc v x) hrq hq⟩
  · intro h q hqp hq
    obtain ⟨r, hrq, x, hr⟩ := hq q le_rfl
    exact hr r le_rfl (A.forceFormula_mono (hrq.trans hqp) (h x))

theorem forceFormula_rename (hA : A.Regular) {n m} (φ : Formula n) (r : Fin n → Fin m)
    (v : Fin m → N) (p : P) :
    A.ForceFormula v p (φ.rename r) ↔ A.ForceFormula (v ∘ r) p φ := by
  induction φ generalizing m p with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.rename, A.forceFormula_imp hA, ihφ, ihψ]
  | conj φ ψ ihφ ihψ =>
    simp only [Formula.rename, forceFormula_conj, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [Formula.rename, forceFormula_disj, ihφ, ihψ]
  | all φ ih =>
    simp only [Formula.rename, A.forceFormula_all hA, ih, Formula.snoc_comp_liftRen]
  | ex φ ih =>
    simp only [Formula.rename, forceFormula_ex, ih, Formula.snoc_comp_liftRen]

theorem forceFormula_raise (hA : A.Regular) {n} (φ : Formula n) (v : Fin n → N)
    (x : N) (p : P) :
    A.ForceFormula (Fin.snoc v x) p φ.raise ↔ A.ForceFormula v p φ := by
  rw [A.forceFormula_rename hA]
  have h : Fin.snoc v x ∘ Fin.castSucc = v := by funext i; simp
  rw [h]

theorem forceFormula_instantiate (hA : A.Regular) {n} (φ : Formula (n+1))
    (t : Fin n) (v : Fin n → N) (p : P) :
    A.ForceFormula v p (φ.instantiate t) ↔ A.ForceFormula (Fin.snoc v (v t)) p φ := by
  rw [Formula.instantiate, A.forceFormula_rename hA]
  have h : v ∘ Fin.lastCases t id = Fin.snoc v (v t) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h]

/-- Equality substitution for all formulas follows from the atomic laws. -/
theorem force_tuple_congr {n} (φ : BasicFormula n) (v w : Fin n → N) (p : P)
    (hvw : ∀ i, A.EqF p (v i) (w i)) : A.Force v p φ ↔ A.Force w p φ := by
  induction φ generalizing p with
  | bot => rfl
  | mem x y => exact A.mem_congr (hvw x) (hvw y)
  | equal x y =>
    constructor
    · intro h
      exact A.eq_trans (A.eq_symm (hvw x)) (A.eq_trans h (hvw y))
    · intro h
      exact A.eq_trans (hvw x) (A.eq_trans h (A.eq_symm (hvw y)))
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v w p hvw) (ihψ v w p hvw)
  | neg φ ih =>
    constructor
    · intro h q hqp hq
      exact h q hqp ((ih v w q (fun i => A.eq_mono hqp (hvw i))).mpr hq)
    · intro h q hqp hq
      exact h q hqp ((ih v w q (fun i => A.eq_mono hqp (hvw i))).mp hq)
  | @ex n φ ih =>
    have step : ∀ v w : Fin n → N, (∀ i, A.EqF p (v i) (w i)) →
        A.Force v p (.ex φ) → A.Force w p (.ex φ) := by
      intro v w he h q hqp
      obtain ⟨r, hrq, x, hr⟩ := h q hqp
      refine ⟨r, hrq, x, (ih (Fin.snoc v x) (Fin.snoc w x) r ?_).mp hr⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using A.eq_refl r x
      · simpa using A.eq_mono (hrq.trans hqp) (he j)
    exact ⟨step v w hvw, step w v (fun i => A.eq_symm (hvw i))⟩

theorem forceFormula_tuple_congr {n} (φ : Formula n) (v w : Fin n → N) (p : P)
    (hvw : ∀ i, A.EqF p (v i) (w i)) :
    A.ForceFormula v p φ ↔ A.ForceFormula w p φ := A.force_tuple_congr φ.toBasic v w p hvw

/-- Soundness for the actual classical calculus in forcing semantics. Unlike
the quotient-model argument this needs no countability assumption on the full
collection of names and constructs no generic over all names. -/
theorem forcing_sound (hA : A.Regular) {n} {Γ : Set (Formula n)} {φ : Formula n}
    (h : Derives Γ φ) (v : Fin n → N) (p : P)
    (hΓ : ∀ ψ ∈ Γ, A.ForceFormula v p ψ) : A.ForceFormula v p φ := by
  induction h generalizing p with
  | hyp hp => exact hΓ _ hp
  | weaken hsub _ ih => exact ih v p (fun ψ hψ => hΓ ψ (hsub hψ))
  | impI _ ih =>
    apply (A.forceFormula_imp hA _ _ _ _).mpr
    intro q hqp hq
    exact ih v q (fun ψ hψ => by
      rcases hψ with rfl | hψ
      · exact hq
      · exact A.forceFormula_mono hqp (hΓ _ hψ))
  | impE _ _ ih₁ ih₂ =>
    exact (A.forceFormula_imp hA _ _ _ _).mp (ih₁ v p hΓ) p le_rfl (ih₂ v p hΓ)
  | botE _ ih => exact (ih v p hΓ).elim
  | @classical n Γ φ _ ih =>
    apply A.forceFormula_of_dense hA
    intro q hqp
    by_contra! hn
    have hneg : A.ForceFormula v q φ.neg :=
      (A.forceFormula_neg hA _ _ _).mpr hn
    exact ih v q (fun ψ hψ => by
      rcases hψ with rfl | hψ
      · exact hneg
      · exact A.forceFormula_mono hqp (hΓ _ hψ))
  | conjI _ _ ih₁ ih₂ => exact ⟨ih₁ v p hΓ, ih₂ v p hΓ⟩
  | conjL _ ih => exact (ih v p hΓ).1
  | conjR _ ih => exact (ih v p hΓ).2
  | disjL _ ih =>
    apply (A.forceFormula_disj _ _ _ _).mpr
    intro q hqp
    exact ⟨q, le_rfl, Or.inl (A.forceFormula_mono hqp (ih v p hΓ))⟩
  | disjR _ ih =>
    apply (A.forceFormula_disj _ _ _ _).mpr
    intro q hqp
    exact ⟨q, le_rfl, Or.inr (A.forceFormula_mono hqp (ih v p hΓ))⟩
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
    apply A.forceFormula_of_dense hA
    intro q hqp
    obtain ⟨r, hrq, hr | hr⟩ := (A.forceFormula_disj _ _ _ _).mp (ih₁ v p hΓ) q hqp
    · exact ⟨r, hrq, ih₂ v r (fun ψ hψ => by
        rcases hψ with rfl | hψ
        · exact hr
        · exact A.forceFormula_mono (hrq.trans hqp) (hΓ _ hψ))⟩
    · exact ⟨r, hrq, ih₃ v r (fun ψ hψ => by
        rcases hψ with rfl | hψ
        · exact hr
        · exact A.forceFormula_mono (hrq.trans hqp) (hΓ _ hψ))⟩
  | allI _ ih =>
    apply (A.forceFormula_all hA _ _ _).mpr
    intro x
    apply ih (Fin.snoc v x) p
    rintro ψ ⟨χ, hχ, rfl⟩
    exact (A.forceFormula_raise hA _ _ _ _).mpr (hΓ _ hχ)
  | allE t _ ih =>
    exact (A.forceFormula_instantiate hA _ _ _ _).mpr
      ((A.forceFormula_all hA _ _ _).mp (ih v p hΓ) (v t))
  | exI t _ ih =>
    intro q hqp
    exact ⟨q, le_rfl, v t, A.forceFormula_mono hqp
      ((A.forceFormula_instantiate hA _ _ _ _).mp (ih v p hΓ))⟩
  | exE _ _ ih₁ ih₂ =>
    apply A.forceFormula_of_dense hA
    intro q hqp
    obtain ⟨r, hrq, x, hr⟩ := ih₁ v p hΓ q hqp
    refine ⟨r, hrq, (A.forceFormula_raise hA _ _ _ _).mp (ih₂ (Fin.snoc v x) r ?_)⟩
    intro ψ hψ
    rcases hψ with rfl | hψ
    · exact hr
    · obtain ⟨χ, hχ, rfl⟩ := hψ
      exact (A.forceFormula_raise hA _ _ _ _).mpr
        (A.forceFormula_mono (hrq.trans hqp) (hΓ _ hχ))
  | eqRefl t => exact A.eq_refl p (v t)
  | eqSubst ψ _ _ ih₁ ih₂ =>
    apply (A.forceFormula_instantiate hA _ _ _ _).mpr
    apply (A.forceFormula_tuple_congr ψ _ _ p ?_).mp
      ((A.forceFormula_instantiate hA _ _ _ _).mp (ih₂ v p hΓ))
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using ih₁ v p hΓ
    · simpa using A.eq_refl p (v j)
  | rename r _ ih =>
    apply (A.forceFormula_rename hA _ _ _ _).mpr
    apply ih (v ∘ r) p
    intro ψ hψ
    exact (A.forceFormula_rename hA _ _ _ _).mp (hΓ _ ⟨ψ,hψ,rfl⟩)

/-- A nonempty regular forcing semantics yields ordinary syntactic consistency
for any theory whose axioms are all forced. Neither an externally generic
filter nor a countable class of names is needed. This is not an assertion that
the target axioms are forced in the constructed symmetric system. -/
theorem consistent_of_regular_forcing (hA : A.Regular) [Nonempty N] (p : P)
    {T : Theory} (hT : ∀ φ ∈ T, A.ForceFormula Fin.elim0 p φ) : Consistent T := by
  intro n hcontra
  let v : Fin n → N := fun _ => Classical.choice (inferInstance : Nonempty N)
  apply A.forcing_sound hA hcontra v p
  rintro _ ⟨φ,hφ,rfl⟩
  apply (A.forceFormula_rename hA _ _ _ _).mpr
  have hv : v ∘ (Fin.elim0 : Fin 0 → Fin n) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
  rw [hv]
  exact hT φ hφ

end PartitionConsistency.ForcingQuotient.AtomicData

namespace PartitionConsistency.SetForcingNames.AtomicForcing
universe u v
variable {P : Type v} [Preorder P]

/-- Actual name forcing has all the regularity needed for classical logical
soundness, as a theorem of the recursion on sets. -/
theorem data_regular (code : P → ZFSet.{u}) (N : Set ZFSet.{u}) : (data code N).Regular := by
  constructor
  · intro p a b h
    exact eq_of_dense h
  · intro p a b h
    exact mem_of_dense h

end PartitionConsistency.SetForcingNames.AtomicForcing

end OAI
