import Mathlib
import OAI.SetTheory.PartitionConsistency.Logic.Proofs
import OAI.SetTheory.PartitionConsistency.Logic.SetLanguage
import OAI.SetTheory.PartitionConsistency.Logic.CountableModels
import OAI.SetTheory.PartitionConsistency.Logic.Completeness

namespace OAI

/-! A concrete choice ground and collapse in Lean's universe metatheory.

This supplies an actual well-founded choice ground rather than hypothesizing
one. It does not supply the source's symmetric extension, does not prove the
constructible interpretation in ZF; the main proof below instead uses the concrete forcing interpretation.
-/


namespace PartitionConsistency

namespace Formula
variable {M : Type*} (E : M → M → Prop)

theorem realize_close {n} (φ : Formula n) :
    Realize E Fin.elim0 φ.close ↔ ∀ v : Fin n → M, Realize E v φ := by
  induction n with
  | zero =>
    exact ⟨fun h v => Subsingleton.elim (Fin.elim0 : Fin 0 → M) v ▸ h,
      fun h => h Fin.elim0⟩
  | succ n ih =>
    rw [close, ih]
    change (∀ v : Fin n → M, ∀ x : M, Realize E (Fin.snoc v x) φ) ↔ _
    constructor
    · intro h v
      have hv : Fin.snoc (fun i => v i.castSucc) (v (Fin.last n)) = v := by
        funext i
        refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp
      exact hv ▸ h _ _
    · exact fun h v x => h (Fin.snoc v x)
end Formula


namespace SetLanguage
open Formula
variable {M : Type*} (E : M → M → Prop)

theorem realize_relation {n m} (p : Formula (n + 2))
    (r : Fin n → Fin m) (x y : Fin m) (v : Fin m → M) :
    Realize E v (relation p r x y) ↔
      Realize E (Fin.snoc (Fin.snoc (v ∘ r) (v x)) (v y)) p := by
  rw [relation, realize_rename]
  have hv : v ∘ Fin.lastCases y (Fin.lastCases x r) =
      Fin.snoc (Fin.snoc (v ∘ r) (v x)) (v y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Function.comp_def]
  rw [hv]

theorem realize_separation {n} (p : Formula (n + 1)) :
    Realize E Fin.elim0 (separation p) ↔
      ∀ v : Fin n → M, ∀ A, ∃ B, ∀ x,
        E x B ↔ E x A ∧ Realize E (Fin.snoc v x) p := by
  unfold separation
  rw [realize_close]
  simp only [Realize, realize_rename, Fin.snoc_last, Fin.snoc_castSucc]
  apply forall_congr'
  intro v
  apply forall_congr'
  intro A
  apply exists_congr
  intro B
  apply forall_congr'
  intro x
  have h : Fin.snoc (Fin.snoc (Fin.snoc v A) B) x ∘
      Fin.lastCases (Fin.last (n + 2)) (fun i => i.castSucc.castSucc.castSucc) =
        Fin.snoc v x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h]
  simp only [iff_def]

theorem realize_replacement {n} (p : Formula (n + 2)) :
    Realize E Fin.elim0 (replacement p) ↔
      ∀ v : Fin n → M, ∀ A,
        (∀ x, E x A → ∃ y, Realize E (Fin.snoc (Fin.snoc v x) y) p ∧
          ∀ z, Realize E (Fin.snoc (Fin.snoc v x) z) p → z = y) →
        ∃ B, ∀ y, E y B ↔ ∃ x, E x A ∧
          Realize E (Fin.snoc (Fin.snoc v x) y) p := by
  unfold replacement
  rw [realize_close]
  simp only [Realize, realize_relation, Fin.snoc_last, Fin.snoc_castSucc]
  have h3 (v : Fin n → M) (a b c : M) :
      Fin.snoc (Fin.snoc (Fin.snoc v a) b) c ∘ (fun i => i.castSucc.castSucc.castSucc) = v := by
    ext i
    simp
  have h4 (v : Fin n → M) (a b c d : M) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc v a) b) c) d ∘
        (fun i => i.castSucc.castSucc.castSucc.castSucc) = v := by
    ext i
    simp
  simp only [h3, h4, ← iff_def]

end SetLanguage

namespace ZFUniverse
universe u
abbrev E : ZFSet.{u} → ZFSet.{u} → Prop := (· ∈ ·)
open Formula SetLanguage

@[simp] theorem realize_subset {n} (v : Fin n → ZFSet.{u}) (a b : Fin n) :
    Realize E.{u} v (subset a b) ↔ v a ⊆ v b := by
  simp [subset, Realize, ZFSet.subset_def, Fin.snoc, Fin.castPred, Fin.castLT, E]

@[simp] theorem realize_empty {n} (v : Fin n → ZFSet.{u}) (a : Fin n) :
    Realize E.{u} v (empty a) ↔ v a = ∅ := by
  simp [empty, Realize, Fin.snoc, Fin.castLT, E, ZFSet.eq_empty]

@[simp] theorem realize_nonempty {n} (v : Fin n → ZFSet.{u}) (a : Fin n) :
    Realize E.{u} v (nonempty a) ↔ ∃ x, x ∈ v a := by
  simp [nonempty, Realize, Fin.snoc, Fin.castLT, E]

@[simp] theorem realize_pair {n} (v : Fin n → ZFSet.{u}) (p x y : Fin n) :
    Realize E.{u} v (unorderedPair p x y) ↔ v p = ({v x, v y} : ZFSet) := by
  rw [ZFSet.ext_iff]
  simp [unorderedPair, Realize, Fin.snoc, Fin.castPred, Fin.castLT, E, ← iff_def]

@[simp] theorem realize_successor {n} (v : Fin n → ZFSet.{u}) (b a : Fin n) :
    Realize E.{u} v (successor b a) ↔ v b = insert (v a) (v a) := by
  rw [ZFSet.ext_iff]
  simp [successor, Realize, Fin.snoc, Fin.castPred, Fin.castLT, E, or_comm, ← iff_def]

@[simp] theorem realize_orderedPair {n} (v : Fin n → ZFSet.{u}) (p x y : Fin n) :
    Realize E.{u} v (orderedPair p x y) ↔ v p = ZFSet.pair (v x) (v y) := by
  simp [orderedPair, Realize, Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT, ZFSet.pair]

@[simp] theorem realize_edge {n} (v : Fin n → ZFSet.{u}) (f x y : Fin n) :
    Realize E.{u} v (edge f x y) ↔ ZFSet.pair (v x) (v y) ∈ v f := by
  simp [edge, Realize, Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT, E]

@[simp] theorem realize_functionOn {n} (v : Fin n → ZFSet.{u}) (f d : Fin n) :
    Realize E.{u} v (functionOn f d) ↔
      (∀ p ∈ v f, ∃ x ∈ v d, ∃ y, p = ZFSet.pair x y) ∧
      ∀ x ∈ v d, ∃! y, ZFSet.pair x y ∈ v f := by
  simp [functionOn, Realize, Fin.snoc, Fin.castPred, Fin.castLT, E, ExistsUnique]

@[simp] theorem realize_mapsTo {n} (v : Fin n → ZFSet.{u}) (f d r : Fin n) :
    Realize E.{u} v (mapsTo f d r) ↔ ZFSet.IsFunc (v d) (v r) (v f) := by
  simp only [mapsTo, realize_rename, Realize, realize_functionOn, realize_edge]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.snoc, Fin.castLT, E]
  simp only [Fin.isValue, Fin.val_zero, Fin.zero_eta]
  constructor
  · rintro ⟨h, hmem⟩
    refine ⟨?_, h.2⟩
    intro p hp
    obtain ⟨x, hx, y, rfl⟩ := h.1 p hp
    exact ZFSet.pair_mem_prod.mpr ⟨hx, hmem x y hx hp⟩
  · rintro ⟨hsub, hfun⟩
    refine ⟨⟨?_, hfun⟩, ?_⟩
    · intro p hp
      obtain ⟨x, hx, y, _, heq⟩ := ZFSet.mem_prod.mp (hsub hp)
      exact ⟨x, hx, y, heq⟩
    · intro x y _ hp
      exact (ZFSet.pair_mem_prod.mp (hsub hp)).2

/-- The full parameterized Separation schema holds in the genuine set universe. -/
theorem separation_true {n} (p : Formula (n + 1)) :
    Realize E.{u} Fin.elim0 (separation p) := by
  rw [SetLanguage.realize_separation]
  intro v A
  exact ⟨ZFSet.sep (fun x => Realize E.{u} (Fin.snoc v x) p) A, fun _ => ZFSet.mem_sep⟩

/-- The full parameterized Replacement schema holds in the genuine set universe. -/
theorem replacement_true {n} (p : Formula (n + 2)) :
    Realize E.{u} Fin.elim0 (replacement p) := by
  classical
  rw [SetLanguage.realize_replacement]
  intro v A h
  let f : A → ZFSet.{u} := fun x => Classical.choose (h x.val x.property)
  have hf (x : A) : Realize E.{u} (Fin.snoc (Fin.snoc v x.val) (f x)) p ∧
      ∀ y, Realize E.{u} (Fin.snoc (Fin.snoc v x.val) y) p → y = f x :=
    Classical.choose_spec (h x.val x.property)
  refine ⟨ZFSet.range f, fun y => ?_⟩
  rw [E, ZFSet.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, (hf x).1⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨x, hx⟩, ((hf ⟨x, hx⟩).2 y hp).symm⟩

/-- A concrete model of every axiom and schema instance of pure ZF. -/
theorem models_ZF : Models E.{u} SetLanguage.ZF := by
  intro p hp
  cases hp with
  | extensionality =>
    simp only [extensionality, Realize]
    intro a b h
    apply ZFSet.ext
    intro x
    exact ⟨(h x).1, (h x).2⟩
  | emptySet =>
    simp only [emptySet, Realize, realize_empty]
    exact ⟨∅, rfl⟩
  | pairing =>
    simp only [pairing, Realize, realize_pair]
    intro a b
    exact ⟨{a, b}, rfl⟩
  | union =>
    simp only [union, Realize]
    intro a
    refine ⟨ZFSet.sUnion a, ?_⟩
    intro x
    exact ⟨ZFSet.mem_sUnion.mp, ZFSet.mem_sUnion.mpr⟩
  | powerSet =>
    simp only [powerSet, Realize, realize_subset]
    intro a
    refine ⟨ZFSet.powerset a, ?_⟩
    intro x
    exact ⟨ZFSet.mem_powerset.mp, ZFSet.mem_powerset.mpr⟩
  | infinity =>
    simp only [infinity, Realize, realize_empty, realize_successor]
    refine ⟨ZFSet.omega, ⟨∅, ZFSet.omega_zero, rfl⟩, ?_⟩
    intro x hx
    exact ⟨insert x x, ZFSet.omega_succ hx, rfl⟩
  | foundation =>
    simp only [foundation, Realize, realize_nonempty]
    intro a ha
    have hne : a ≠ ∅ := by
      rintro rfl
      obtain ⟨x, hx⟩ := ha
      exact ZFSet.notMem_empty x hx
    obtain ⟨b, hb, hi⟩ := ZFSet.regularity a hne
    refine ⟨b, hb, ?_⟩
    intro x hx hxa
    have : x ∈ a ∩ b := ZFSet.mem_inter.mpr ⟨hxa, hx⟩
    exact ZFSet.notMem_empty x (hi ▸ this)
  | separation p => exact separation_true p
  | replacement p => exact replacement_true p

@[simp] theorem realize_choiceOn {n} (v : Fin n → ZFSet.{u}) (c a : Fin n) :
    Realize E.{u} v (choiceOn c a) ↔
      Realize E v (functionOn c a) ∧ ∀ x ∈ v a, ∃ y, ZFSet.pair x y ∈ v c ∧ y ∈ x := by
  simp [choiceOn, Realize, Fin.snoc, Fin.castPred, Fin.castLT, E]

/-- The set-graph version of Choice is true in the ambient universe. It is
obtained from Lean's permitted `Classical.choice`, not an additional axiom. -/
theorem AC_true : Realize E.{u} Fin.elim0 AC := by
  classical
  simp only [AC, Realize, realize_nonempty, realize_choiceOn, realize_functionOn]
  intro a h
  change (∀ x ∈ a, ∃ y, y ∈ x) at h
  let f : a → ZFSet.{u} := fun x => Classical.choose (h x.val x.property)
  have hf (x : a) : f x ∈ x.val := Classical.choose_spec (h x.val x.property)
  let c := ZFSet.range (fun x : a => ZFSet.pair x.val (f x))
  have hc (p) : p ∈ c ↔ ∃ x : a, ZFSet.pair x.val (f x) = p := ZFSet.mem_range
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, rfl⟩ := (hc p).mp hp
    exact ⟨x.val, x.property, f x, rfl⟩
  · intro x hx
    refine ⟨f ⟨x, hx⟩, (hc _).mpr ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨z, hz⟩ := (hc _).mp hy
    obtain ⟨he, hfz⟩ := ZFSet.pair_inj.mp hz
    obtain rfl : z = (⟨x, hx⟩ : a) := Subtype.ext he
    exact hfz.symm
  · intro x hx
    exact ⟨f ⟨x, hx⟩, (hc _).mpr ⟨⟨x, hx⟩, rfl⟩, hf ⟨x, hx⟩⟩

/-- Full ZFC in exactly the syntax used for the selected consistency target. -/
theorem models_ZFC : Models E.{u} (SetLanguage.ZF ∪ {AC}) := by
  intro p hp
  rcases hp with hp | hp
  · exact models_ZF p hp
  · obtain rfl : p = AC := Set.mem_singleton_iff.mp hp
    exact AC_true

end ZFUniverse
namespace Formula

/-- Truth in the target syntax is invariant under genuine structure isomorphisms. -/
theorem realize_equiv {M N : Type*} (E : M → M → Prop) (F : N → N → Prop)
    (e : M ≃ N) (he : ∀ a b, E a b ↔ F (e a) (e b)) {n} (p : Formula n)
    (v : Fin n → M) : Realize E v p ↔ Realize F (e ∘ v) p := by
  induction p with
  | bot => rfl
  | mem x y => exact he (v x) (v y)
  | equal x y => exact e.injective.eq_iff.symm
  | imp p q hp hq => exact imp_congr (hp v) (hq v)
  | conj p q hp hq => exact and_congr (hp v) (hq v)
  | disj p q hp hq => exact or_congr (hp v) (hq v)
  | all p hp =>
    constructor
    · intro h x
      obtain ⟨y, rfl⟩ := e.surjective x
      simpa only [Fin.comp_snoc] using (hp (Fin.snoc v y)).1 (h y)
    · intro h y
      apply (hp (Fin.snoc v y)).2
      simpa only [Fin.comp_snoc] using h (e y)
  | ex p hp =>
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e y, by simpa only [Fin.comp_snoc] using (hp (Fin.snoc v y)).1 hy⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := e.surjective x
      exact ⟨y, (hp (Fin.snoc v y)).2 (by simpa only [Fin.comp_snoc] using hx)⟩
end Formula

/-- Transport of a whole theory, including schemas, across a relational isomorphism. -/
theorem models_equiv {M N : Type*} (E : M → M → Prop) (F : N → N → Prop)
    (e : M ≃ N) (he : ∀ a b, E a b ↔ F (e a) (e b)) (T : Theory) :
    Models E T ↔ Models F T := by
  have hv : e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) :=
    Subsingleton.elim _ _
  unfold Models
  exact forall₂_congr fun p _ => by rw [Formula.realize_equiv E F e he p, hv]

namespace Mostowski
universe u v
variable {M : Type v} [Small.{u} M] {E : M → M → Prop} (hw : WellFounded E)

/-- Collapse by genuine external well-founded recursion, not recursion over an
arbitrary first-order model's internal membership relation. -/
noncomputable def collapse : M → ZFSet.{u} :=
  hw.fix (fun a f => ZFSet.range (fun x : {x // E x a} => f x.val x.property))

theorem collapse_eq (a : M) : collapse hw a =
    ZFSet.range (fun x : {x // E x a} => collapse hw x.val) := by
  exact hw.fix_eq _ a

theorem mem_collapse_iff (a : M) (x : ZFSet.{u}) :
    x ∈ collapse hw a ↔ ∃ b, E b a ∧ collapse hw b = x := by
  rw [collapse_eq, ZFSet.mem_range]
  exact ⟨fun ⟨b, hb⟩ => ⟨b.val, b.property, hb⟩,
    fun ⟨b, hb, he⟩ => ⟨⟨b, hb⟩, he⟩⟩

variable (he : ∀ a b, (∀ x, E x a ↔ E x b) → a = b)

include he in
/-- Extensionality makes the collapse injective. -/
theorem collapse_injective : Function.Injective (collapse.{u} hw) := by
  intro a
  induction a using hw.induction with
  | h a ih =>
    intro b hab
    apply he a b
    intro x
    constructor
    · intro hxa
      have hx : collapse hw x ∈ collapse hw b :=
        hab ▸ (mem_collapse_iff hw a _).2 ⟨x, hxa, rfl⟩
      obtain ⟨y, hy, hxy⟩ := (mem_collapse_iff hw b _).1 hx
      have : x = y := ih x hxa hxy.symm
      exact this.symm ▸ hy
    · intro hxb
      have hx : collapse hw x ∈ collapse hw a :=
        hab.symm ▸ (mem_collapse_iff hw b _).2 ⟨x, hxb, rfl⟩
      obtain ⟨y, hy, hxy⟩ := (mem_collapse_iff hw a _).1 hx
      have : y = x := ih y hy hxy
      exact this ▸ hy

include he in
theorem collapse_mem_collapse (a b : M) :
    collapse.{u} hw a ∈ collapse hw b ↔ E a b := by
  rw [mem_collapse_iff]
  constructor
  · rintro ⟨x, hx, hx'⟩
    exact collapse_injective hw he hx' ▸ hx
  · exact fun hab => ⟨a, hab, rfl⟩

/-- The range of the collapse is transitive as a collection of actual sets. -/
theorem range_transitive : ∀ a ∈ Set.range (collapse.{u} hw), ∀ b ∈ a,
    b ∈ Set.range (collapse hw) := by
  rintro a ⟨x, rfl⟩ b hb
  obtain ⟨y, _, hy⟩ := (mem_collapse_iff hw x b).1 hb
  exact ⟨y, hy⟩

/-- Collapse is a membership isomorphism onto its transitive range. -/
noncomputable def rangeEquiv : M ≃ Set.range (collapse.{u} hw) :=
  Equiv.ofInjective (collapse hw) (collapse_injective hw he)

theorem rangeEquiv_mem (a b : M) :
    (rangeEquiv.{u} hw he a).val ∈ (rangeEquiv hw he b).val ↔ E a b :=
  collapse_mem_collapse hw he a b

include he in
/-- A well-founded extensional small model has an isomorphic transitive model. -/
theorem range_models {T : Theory} (hT : Models E T) :
    Models (fun a b : Set.range (collapse.{u} hw) => a.val ∈ b.val) T :=
  (models_equiv E _ (rangeEquiv hw he) (fun a b => (rangeEquiv_mem hw he a b).symm) T).mp hT

end Mostowski

namespace ZFUniverse
open Formula SetLanguage

/-- In Lean's universe metatheory there is a countable, transitive pure-set
model of full ZFC. This is proved using `ZFSet`, downward Löwenheim–Skolem,
and the collapse; it is NOT an assumption inferred from bare Con(ZF). -/
theorem exists_countable_transitive_ZFC :
    ∃ M : Set ZFSet.{0}, M.Nonempty ∧ M.Countable ∧
      (∀ a ∈ M, ∀ b ∈ a, b ∈ M) ∧
      Models (fun a b : M => a.val ∈ b.val) (SetLanguage.ZF ∪ {AC}) := by
  obtain ⟨N, hN, hct, hmodel⟩ :=
    CountableModel.exists_countable_model E.{0} models_ZFC
  have : Countable N := hct.to_subtype
  let r : N → N → Prop := fun a b => a.val ∈ b.val
  have hw : WellFounded r := InvImage.wf Subtype.val ZFSet.mem_wf
  have he : ∀ a b : N, (∀ x, r x a ↔ r x b) → a = b := by
    have hex : Realize r Fin.elim0 extensionality :=
      hmodel _ (Or.inl IsZFAxiom.extensionality)
    intro a b hab
    apply hex a b
    intro x
    exact ⟨(hab x).mp, (hab x).mpr⟩
  let c : N → ZFSet.{0} := Mostowski.collapse hw
  refine ⟨Set.range c, ?_, Set.countable_range c,
    Mostowski.range_transitive.{0} hw, Mostowski.range_models.{0} hw he hmodel⟩
  obtain ⟨x, hx⟩ := hN
  exact ⟨c ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩

/-- Existence of an actual choice ground, not yet an extension violating Choice. -/
theorem consistent_ZFC : Consistent (SetLanguage.ZF ∪ {AC}) :=
  consistent_of_model E.{0} models_ZFC

end ZFUniverse
end PartitionConsistency

end OAI
