import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeHom

namespace OAI

/-! Support of an element of the actual positive Artin monoid. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable

@[ext] structure SupportValue (S : Type) where
  carrier : Set S

instance {S : Type} : CommMonoid (SupportValue S) where
  mul a b := ⟨a.carrier ∪ b.carrier⟩
  one := ⟨∅⟩
  mul_assoc a b c := by ext s; exact or_assoc
  one_mul a := by ext s; change (False ∨ s ∈ a.carrier) ↔ s ∈ a.carrier; tauto
  mul_one a := by ext s; change (s ∈ a.carrier ∨ False) ↔ s ∈ a.carrier; tauto
  mul_comm a b := by ext s; exact or_comm

private lemma supportValue_word {S : Type} (w : List S) (s : S) :
    s ∈ ((w.map (fun t => (⟨{t}⟩ : SupportValue S))).prod).carrier ↔ s ∈ w := by
  induction w with
  | nil => change False ↔ s ∈ ([] : List S); simp
  | cons t w ih =>
    change (s=t ∨ s ∈ ((w.map (fun t => (⟨{t}⟩ : SupportValue S))).prod).carrier) ↔ _
    rw [ih, List.mem_cons]

private lemma altList_support {S : Type} (i j s : S) (n : ℕ) (hn : 2 ≤ n) :
    s ∈ altList i j n ↔ s=i ∨ s=j := by
  constructor
  · exact mem_altList i j n s
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, n=k+2 := ⟨n-2, by omega⟩
    simp only [altList_succ, List.mem_cons]
    exact h.elim Or.inl (fun hs => Or.inr (Or.inl hs))

variable {S : Type} (M : CoxeterMatrix S)

private lemma support_relations : ∀ a b : FreeMonoid S, positiveBraidRelations M a b →
    FreeMonoid.lift (fun s => (⟨{s}⟩ : SupportValue S)) a =
      FreeMonoid.lift (fun s => (⟨{s}⟩ : SupportValue S)) b := by
  rintro a b ⟨i,j,rfl,rfl⟩
  simp only [FreeMonoid.lift_ofList]
  ext s
  rw [supportValue_word, supportValue_word]
  by_cases hij : i=j
  · rw [hij]
  by_cases hn : M i j=0
  · simp only [hn, altList_zero]
  · have hge : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
    rw [altList_support i j s _ hge, altList_support j i s _ hge, or_comm]

noncomputable def positiveSupportHom : PositiveArtin M →* SupportValue S :=
  PresentedMonoid.lift (fun s => ⟨{s}⟩) (support_relations M)

noncomputable def positiveSupport (a : PositiveArtin M) : Set S :=
  (positiveSupportHom M a).carrier

@[simp] lemma positiveSupport_one : positiveSupport M 1 = ∅ := by
  unfold positiveSupport
  rw [map_one]
  rfl

@[simp] lemma positiveSupport_generator (s : S) :
    positiveSupport M (positiveGenerator M s) = {s} := rfl

@[simp] lemma positiveSupport_mul (a b : PositiveArtin M) :
    positiveSupport M (a*b) = positiveSupport M a ∪ positiveSupport M b := by
  unfold positiveSupport
  rw [map_mul]
  rfl

@[simp] lemma positiveSupport_word (w : List S) :
    positiveSupport M (wordPositive M w) = {s | s ∈ w} := by
  ext s
  induction w with
  | nil => simp only [wordPositive, List.map_nil, List.prod_nil, positiveSupport_one,
      Set.mem_empty_iff_false, Set.mem_ofPred_eq, List.not_mem_nil]
  | cons t w ih =>
    change s ∈ positiveSupport M (positiveGenerator M t*wordPositive M w) ↔ _
    rw [positiveSupport_mul, Set.mem_union, positiveSupport_generator, Set.mem_singleton_iff, ih]
    exact List.mem_cons.symm

/-- Support inclusion gives a word using only the specified colors. -/
theorem positiveSupport_word_exists (a : PositiveArtin M) (J : Set S)
    (ha : positiveSupport M a ⊆ J) :
    ∃ w : List S, wordPositive M w=a ∧ ∀ s ∈ w, s ∈ J := by
  obtain ⟨w, rfl⟩ := positive_word_surjective M a
  exact ⟨w, rfl, fun s hs => ha ((positiveSupport_word M w).symm ▸ hs)⟩

end HarmonicArtin.ParabolicIntersections

end OAI
