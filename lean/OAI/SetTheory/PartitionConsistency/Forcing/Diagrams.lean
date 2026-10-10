import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.DiagramOrder
import OAI.SetTheory.PartitionConsistency.Algebra.Placements

namespace OAI

namespace PartitionConsistency
namespace DiagramForcing
universe u
variable {M I : Type u}

/-- An actual injective diagram on all of the monoid, with no finite or rank
cutoff. Stronger diagrams are the larger diagrams in the translation order. -/
structure Diagram (M I : Type u) where
  toEmbedding : M ↪ I

namespace Diagram
instance : CoeFun (Diagram M I) (fun _ => M → I) := ⟨fun r => (r.toEmbedding : M → I)⟩
@[ext] theorem ext {r s : Diagram M I} (h : ∀ x, r x = s x) : r = s :=
  by cases r; cases s; congr 1; exact Function.Embedding.ext h

theorem injective (r : Diagram M I) : Function.Injective r :=
  r.toEmbedding.injective

variable [LeftCancelMonoid M]
def sub (r : Diagram M I) (n : M) : Diagram M I :=
  ⟨⟨fun x => r (n * x), r.injective.comp (fun _ _ h => mul_left_cancel h)⟩⟩

@[simp] theorem sub_apply (r : Diagram M I) (n x : M) : sub r n x = r (n * x) := rfl
@[simp] theorem sub_one (r : Diagram M I) : sub r 1 = r := by ext; simp
@[simp] theorem sub_sub (r : Diagram M I) (n m : M) : sub (sub r n) m = sub r (n * m) := by
  ext x
  simp [mul_assoc]

theorem index_unique {r : Diagram M I} {n m : M} (h : sub r n = sub r m) : n = m := by
  have he := congrArg (fun s : Diagram M I => s 1) h
  exact r.injective (by simpa using he)

def range (r : Diagram M I) : Set I := Set.range r

theorem range_sub_subset (r : Diagram M I) (n : M) : (sub r n).range ⊆ r.range := by
  rintro i ⟨x, hx⟩
  exact ⟨n * x, hx⟩

instance [DiagramOrder.IsConical M] : PartialOrder (Diagram M I) where
  le r s := ∃ n, sub r n = s
  le_refl r := ⟨1, sub_one r⟩
  le_trans r s t hrs hst := by
    obtain ⟨n, hn⟩ := hrs
    obtain ⟨m, hm⟩ := hst
    exact ⟨n * m, by rw [← sub_sub, hn, hm]⟩
  le_antisymm r s hrs hsr := by
    obtain ⟨n, hn⟩ := hrs
    obtain ⟨m, hm⟩ := hsr
    have he : sub r (n * m) = sub r 1 := by rw [← sub_sub, hn, hm, sub_one]
    have hn₁ := (DiagramOrder.IsConical.eq_one_of_mul_eq_one (index_unique he)).1
    simpa [hn₁] using hn

@[simp] theorem le_iff [DiagramOrder.IsConical M] (r s : Diagram M I) :
    r ≤ s ↔ ∃ n, sub r n = s := Iff.rfl

theorem range_antitone [DiagramOrder.IsConical M] :
    Antitone (range : Diagram M I → Set I) := by
  rintro r s ⟨n, rfl⟩
  exact range_sub_subset r n

/-- Label permutations act on the entire diagram, not on its monoid positions. -/
def permute (π : Equiv.Perm I) (r : Diagram M I) : Diagram M I :=
  ⟨r.toEmbedding.trans π.toEmbedding⟩

omit [LeftCancelMonoid M] in
@[simp] theorem permute_apply (π : Equiv.Perm I) (r : Diagram M I) (x : M) :
    permute π r x = π (r x) := rfl
omit [LeftCancelMonoid M] in
@[simp] theorem permute_one (r : Diagram M I) : permute 1 r = r := by ext; rfl
omit [LeftCancelMonoid M] in
@[simp] theorem permute_mul (π σ : Equiv.Perm I) (r : Diagram M I) :
    permute (π * σ) r = permute π (permute σ r) := by ext; rfl
@[simp] theorem permute_sub (π : Equiv.Perm I) (r : Diagram M I) (n : M) :
    permute π (sub r n) = sub (permute π r) n := by ext; rfl

omit [LeftCancelMonoid M] in
@[simp] theorem permute_inv_permute (π : Equiv.Perm I) (r : Diagram M I) :
    permute π⁻¹ (permute π r) = r := by ext; simp
omit [LeftCancelMonoid M] in
@[simp] theorem permute_permute_inv (π : Equiv.Perm I) (r : Diagram M I) :
    permute π (permute π⁻¹ r) = r := by ext; simp

/-- The label action preserves and reflects the forcing order. -/
def permuteOrderIso [DiagramOrder.IsConical M] (π : Equiv.Perm I) :
    Diagram M I ≃o Diagram M I where
  toFun := permute π
  invFun := permute π⁻¹
  left_inv r := by ext; simp
  right_inv r := by ext; simp
  map_rel_iff' := by
    intro r s
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have he := congrArg (permute π⁻¹) hn
      simpa using he
    · rintro ⟨n, rfl⟩
      exact ⟨n, (permute_sub _ _ _).symm⟩

/-- The distinguished-probe complement bound is exactly what is needed to
extend a diagram through `e` while covering any prescribed `μ` labels.
Source `lem:diagram-amalgamation`, first part. -/
theorem extend_through [Infinite I] (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (p : Diagram M I) {J : Set I} (hJ : Cardinal.mk J ≤ Cardinal.mk M) :
    ∃ r : Diagram M I, sub r e = p ∧ J ⊆ r.range := by
  classical
  let ee : M ≃ Set.range (fun x : M => e * x) :=
    Equiv.ofInjective (fun x => e * x) (fun _ _ h => mul_left_cancel h)
  let f : Set.range (fun x : M => e * x) ↪ I := ee.symm.toEmbedding.trans p.toEmbedding
  obtain ⟨r, hr, hcover⟩ := SmallPlacements.extend_embedding_cover hsize f (by rwa [he])
  refine ⟨⟨r⟩, ?_, hcover⟩
  ext x
  have ht : r (e * x) = p (ee.symm (ee x)) := hr (ee x)
  simpa only [Equiv.symm_apply_apply, sub_apply] using ht

end Diagram

/-- A finite overlap prescription, before transitive closure. `none` specifies
no overlap; `some (a,b)` identifies `(i,a*x)` with `(j,b*x)` for each `x`. -/
structure OverlapPrescription (M : Type u) (n : ℕ) where
  start : Fin n → Fin n → Option (M × M)

namespace OverlapPrescription
variable [Monoid M] {n : ℕ}

def Rel (P : OverlapPrescription M n) (z w : Fin n × M) : Prop :=
  if z.1 = w.1 then z.2 = w.2 else
    match P.start z.1 w.1 with
    | none => False
    | some (a, b) => ∃ t, z.2 = a * t ∧ w.2 = b * t

/-- The indicated pair identifications must already be an equivalence,
without adding further overlaps by transitive closure. Equality within a copy
is built into `Rel`. -/
def Valid (P : OverlapPrescription M n) : Prop := Equivalence P.Rel

@[simp] theorem rel_same_copy (P : OverlapPrescription M n) (i : Fin n) (x y : M) :
    P.Rel (i, x) (i, y) ↔ x = y := by simp [Rel]

end OverlapPrescription

/-- Precisely the finite-overlap realization property in `thm:monoid`, item 2.
Existence of a monoid having this property is still a separate obligation. -/
def HasFiniteMergers (M : Type u) [Monoid M] : Prop :=
  ∀ (n : ℕ) (P : OverlapPrescription M n), P.Valid →
    ∃ l : Fin n → M, ∀ z w : Fin n × M,
      l z.1 * z.2 = l w.1 * w.2 ↔ P.Rel z w

namespace Diagram
variable [LeftCancelMonoid M]

/-- The pairwise hypothesis of the diagram amalgamation lemma. -/
def ExactOverlap (r s : Diagram M I) : Prop :=
  Disjoint r.range s.range ∨ ∃ a b : M,
    sub r a = sub s b ∧ r.range ∩ s.range = (sub r a).range

theorem equal_iff_of_common_sub {r s : Diagram M I} {a b : M}
    (he : sub r a = sub s b) (hr : r.range ∩ s.range = (sub r a).range) (x y : M) :
    r x = s y ↔ ∃ t, x = a * t ∧ y = b * t := by
  constructor
  · intro hxy
    have hm : r x ∈ (sub r a).range := hr ▸ ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, (r.injective ht).symm, ?_⟩
    apply s.injective
    have hte := congrArg (fun d : Diagram M I => d t) he
    exact hxy.symm.trans (ht.symm.trans hte)
  · rintro ⟨t, rfl, rfl⟩
    exact congrArg (fun d : Diagram M I => d t) he

/-- Actual equality of labels gives a valid finite prescription whenever all
pairwise range intersections are exact common subdiagrams. -/
theorem exists_overlap_prescription {n : ℕ} (s : Fin n → Diagram M I)
    (hs : ∀ i j, i ≠ j → ExactOverlap (s i) (s j)) :
    ∃ P : OverlapPrescription M n, P.Valid ∧ ∀ z w : Fin n × M,
      s z.1 z.2 = s w.1 w.2 ↔ P.Rel z w := by
  classical
  have choices : ∀ i j : Fin n, ∃ o : Option (M × M), ∀ x y : M,
      s i x = s j y ↔ (if i = j then x = y else
        match o with
        | none => False
        | some (a, b) => ∃ t, x = a * t ∧ y = b * t) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact ⟨none, fun x y => by simp⟩
    · rcases hs i j hij with hdisj | ⟨a, b, he, hr⟩
      · refine ⟨none, ?_⟩
        intro x y
        simp only [hij, ↓reduceIte, iff_false]
        intro heq
        exact Set.disjoint_left.1 hdisj ⟨x, rfl⟩ ⟨y, heq.symm⟩
      · exact ⟨some (a, b), fun x y => by
          simpa only [hij, ↓reduceIte] using equal_iff_of_common_sub he hr x y⟩
  choose start hstart using choices
  let P : OverlapPrescription M n := ⟨start⟩
  have hp : ∀ z w : Fin n × M, s z.1 z.2 = s w.1 w.2 ↔ P.Rel z w :=
    fun z w => hstart z.1 w.1 z.2 w.2
  refine ⟨P, ⟨?_, ?_, ?_⟩, hp⟩
  · intro z
    exact (hp z z).1 rfl
  · intro z w hzw
    exact (hp w z).1 ((hp z w).2 hzw).symm
  · intro z w v hzw hwv
    exact (hp z v).1 (((hp z w).2 hzw).trans ((hp w v).2 hwv))

/-- Source `lem:diagram-amalgamation`, second part. The extension is an actual
embedding on the whole monoid. The prescribed range overlaps are used to
invoke the finite-merger property; no amalgamating diagram is a premise. -/
theorem amalgamate [Infinite I] (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) {n : ℕ} (s : Fin n → Diagram M I)
    (hs : ∀ i j, i ≠ j → ExactOverlap (s i) (s j)) :
    ∃ (r : Diagram M I) (l : Fin n → M), ∀ i, sub r (l i) = s i := by
  classical
  obtain ⟨P, hP, hlabels⟩ := exists_overlap_prescription s hs
  obtain ⟨l, hl⟩ := hmerger n P hP
  let U : Set M := {m | ∃ i x, l i * x = m}
  have hreps : ∀ z : U, ∃ i x, l i * x = z.val := fun z => z.property
  choose idx arg hrep using hreps
  let f : U → I := fun z => s (idx z) (arg z)
  have hf : Function.Injective f := by
    intro z w hzw
    have hh := (hl (idx z, arg z) (idx w, arg w)).2
      ((hlabels (idx z, arg z) (idx w, arg w)).1 hzw)
    apply Subtype.ext
    simpa only [hrep] using hh
  have hfval : ∀ i x, f ⟨l i * x, ⟨i, x, rfl⟩⟩ = s i x := by
    intro i x
    let z : U := ⟨l i * x, ⟨i, x, rfl⟩⟩
    exact (hlabels (idx z, arg z) (i, x)).2
      ((hl (idx z, arg z) (i, x)).1 (hrep z))
  obtain ⟨r, hr⟩ := SmallPlacements.extend_embedding hsize ⟨f, hf⟩
  refine ⟨⟨r⟩, l, ?_⟩
  intro i
  ext x
  exact (hr ⟨l i * x, ⟨i, x, rfl⟩⟩).trans (hfval i x)

theorem common_extension [Infinite I] [DiagramOrder.IsConical M]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n : ℕ} (s : Fin n → Diagram M I)
    (hs : ∀ i j, i ≠ j → ExactOverlap (s i) (s j)) :
    ∃ r : Diagram M I, ∀ i, r ≤ s i := by
  obtain ⟨r, l, hl⟩ := amalgamate hsize hmerger s hs
  exact ⟨r, fun i => ⟨l i, hl i⟩⟩

end Diagram
end DiagramForcing
end PartitionConsistency

end OAI
