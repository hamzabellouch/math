import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import OAI.SetTheory.PartitionPrinciple.Geometry.RectangleTile

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry

universe u

variable (J S : Type u) [Group J]

def Factor : Bool → Type u
  | false => J
  | true => FreeGroup S

instance factorGroup (b : Bool) : Group (Factor J S b) := by
  cases b <;> dsimp [Factor] <;> infer_instance

abbrev External := Monoid.CoprodI (Factor J S)

def old : J →* External J S := Monoid.CoprodI.of (M := Factor J S) (i := false)
def free : FreeGroup S →* External J S := Monoid.CoprodI.of (M := Factor J S) (i := true)
def generator (s : S) : External J S := free J S (FreeGroup.of s)
def signed (a : S × Bool) : External J S := free J S (FreeGroup.mk [a])

theorem old_injective : Function.Injective (old J S) := Monoid.CoprodI.of_injective (M := Factor J S) false

def Cancel (a b : S × Bool) : Prop := a.1 = b.1 ∧ a.2 = !b.2

def Reduced : List ((S × Bool) × J) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => (x.2 = 1 → ¬ Cancel S x.1 y.1) ∧ Reduced (y :: rest)

def eval : List ((S × Bool) × J) → External J S
  | [] => 1
  | (a, j) :: rest => signed J S a * old J S j * eval rest

open Monoid.CoprodI

noncomputable def oldWord (j : J) : Word (Factor J S) := by
  classical
  exact if h : j = 1 then Word.empty else Word.cons (i := false) j Word.empty (by simp [Word.fstIdx, Word.empty]) h

theorem oldWord_prod (j : J) : (oldWord J S j).prod = old J S j := by
  classical
  by_cases h : j = 1
  · subst j
    rw [oldWord, dite_eq_left rfl]
    exact (map_one (old J S)).symm
  · rw [oldWord, dite_eq_right h]
    exact (Word.prod_cons (M := Factor J S) false j Word.empty h _).trans (mul_one _)

theorem oldWord_not_free (j : J) : (oldWord J S j).fstIdx ≠ some true := by
  classical
  by_cases h : j = 1
  · simp [oldWord, h, Word.fstIdx, Word.empty]
  · rw [oldWord, dite_eq_right h]
    change (some false : Option Bool) ≠ some true
    decide

theorem free_head_not_old (w : Word (Factor J S)) (head : w.fstIdx = some true) (j : J) :
    w.prod ≠ old J S j := by
  classical
  intro eq
  have same : w = oldWord J S j := by
    apply (Word.equiv (M := Factor J S)).symm.injective
    exact eq.trans (oldWord_prod J S j).symm
  exact oldWord_not_free J S j (same ▸ head)

variable [DecidableEq S]

theorem free_prepend (a b : S × Bool) (f : FreeGroup S)
    (head : f.toWord.head? = some b) (safe : ¬ Cancel S a b) :
    (FreeGroup.mk (a :: f.toWord)).toWord = a :: f.toWord := by
  classical
  rw [FreeGroup.toWord_mk, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases h : f.toWord with
  | nil => simp [h] at head
  | cons c rest =>
    have cb : c = b := by simpa [h] using head
    subst c
    change (if a.1 = b.1 ∧ a.2 = !b.2 then rest else a :: b :: rest) = a :: b :: rest
    change ¬ (a.1 = b.1 ∧ a.2 = !b.2) at safe
    rw [ite_eq_right safe]

theorem signed_mul_free (a : S × Bool) (f : FreeGroup S) :
    signed J S a * free J S f = free J S (FreeGroup.mk (a :: f.toWord)) := by
  change free J S (FreeGroup.mk [a]) * free J S f = _
  rw [← map_mul]
  apply congrArg (free J S)
  calc
    FreeGroup.mk [a] * f = FreeGroup.mk [a] * FreeGroup.mk f.toWord := by rw [FreeGroup.mk_toWord]
    _ = _ := FreeGroup.mul_mk

theorem head_nontrivial (a : S × Bool) (f : FreeGroup S)
    (head : f.toWord.head? = some a) : f ≠ 1 := by
  intro eq
  simp [eq] at head

theorem relative_normal_form (a : S × Bool) (j : J) (rest : List ((S × Bool) × J))
    (reduced : Reduced J S ((a, j) :: rest)) :
    ∃ (f : FreeGroup S) (tail : Word (Factor J S)),
      f.toWord.head? = some a ∧ tail.fstIdx ≠ some true ∧
      eval J S ((a, j) :: rest) = free J S f * tail.prod := by
  classical
  induction rest generalizing a j with
  | nil =>
    refine ⟨FreeGroup.mk [a], oldWord J S j, rfl, oldWord_not_free J S j, ?_⟩
    rw [oldWord_prod]
    exact mul_one _
  | cons b rest ih =>
    rcases b with ⟨b, k⟩
    rcases ih b k reduced.2 with ⟨f, tail, first, tailHead, value⟩
    by_cases jone : j = 1
    · subst j
      have safe := reduced.1 rfl
      have prep := free_prepend S a b f first safe
      refine ⟨FreeGroup.mk (a :: f.toWord), tail, ?_, tailHead, ?_⟩
      · rw [prep]
        rfl
      · change signed J S a * old J S 1 * eval J S ((b, k) :: rest) = _
        rw [map_one, mul_one, value, ← mul_assoc, signed_mul_free]
    · let w := Word.cons (i := true) f tail tailHead (head_nontrivial S b f first)
      have wHead : w.fstIdx ≠ some false := by
        change (some true : Option Bool) ≠ some false
        decide
      let t := Word.cons (i := false) j w wHead jone
      refine ⟨FreeGroup.mk [a], t, rfl, ?_, ?_⟩
      · change (some false : Option Bool) ≠ some true
        decide
      · change signed J S a * old J S j * eval J S ((b, k) :: rest) =
          signed J S a * (old J S j * (free J S f * tail.prod))
        rw [value, mul_assoc]

theorem reduced_not_old (a : S × Bool) (j : J) (rest : List ((S × Bool) × J))
    (reduced : Reduced J S ((a, j) :: rest)) (k : J) :
    eval J S ((a, j) :: rest) ≠ old J S k := by
  classical
  rcases relative_normal_form J S a j rest reduced with ⟨f, tail, head, tailHead, value⟩
  let w := Word.cons (i := true) f tail tailHead (head_nontrivial S a f head)
  have prod : w.prod = eval J S ((a, j) :: rest) := by
    rw [value]
    exact Word.prod_cons true f tail _ _
  intro eq
  exact free_head_not_old J S w rfl k (prod.trans eq)

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry



namespace PartitionPilot.Forcing.ExternalWordRewrite

universe u
abbrev Alphabet (J S : Type u) := J ⊕ (S × Bool)

variable {J S : Type u} [Group J]

inductive Atomic : List (Alphabet J S) → List (Alphabet J S) → Prop
  | old_one : Atomic [.inl 1] []
  | old_mul (g h : J) : Atomic [.inl g, .inl h] [.inl (g * h)]
  | cancel (s : S) (b : Bool) : Atomic [.inr (s, b), .inr (s, !b)] []

def Step (xs ys : List (Alphabet J S)) : Prop :=
  ∃ pre post l r, Atomic l r ∧
    ((xs = pre ++ l ++ post ∧ ys = pre ++ r ++ post) ∨
      (ys = pre ++ l ++ post ∧ xs = pre ++ r ++ post))

def Path : List (Alphabet J S) → List (Alphabet J S) → Prop :=
  Relation.ReflTransGen Step

def congruence (J S : Type u) [Group J] : Con (FreeMonoid (Alphabet J S)) :=
  conGen Atomic

theorem Atomic.step {xs ys : List (Alphabet J S)} (h : Atomic xs ys) : Step xs ys :=
  ⟨[], [], xs, ys, h, Or.inl ⟨by simp, by simp⟩⟩

theorem Step.symm {xs ys : List (Alphabet J S)} (h : Step xs ys) : Step ys xs := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  exact ⟨pre, post, l, r, atom, eq.symm⟩

theorem Step.append_left (p : List (Alphabet J S)) {xs ys : List (Alphabet J S)}
    (h : Step xs ys) : Step (p ++ xs) (p ++ ys) := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  refine ⟨p ++ pre, post, l, r, atom, ?_⟩
  rcases eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩
  · exact Or.inr ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩

theorem Step.append_right (p : List (Alphabet J S)) {xs ys : List (Alphabet J S)}
    (h : Step xs ys) : Step (xs ++ p) (ys ++ p) := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  refine ⟨pre, post ++ p, l, r, atom, ?_⟩
  rcases eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩
  · exact Or.inr ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩

theorem Path.symm {xs ys : List (Alphabet J S)} (h : Path xs ys) : Path ys xs := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.head step.symm

theorem Path.append {xs ys zs ws : List (Alphabet J S)} (first : Path xs ys)
    (second : Path zs ws) : Path (xs ++ zs) (ys ++ ws) :=
  (first.lift (fun l => l ++ zs) (fun _ _ step => step.append_right zs)).trans
    (second.lift (fun l => ys ++ l) (fun _ _ step => step.append_left ys))

theorem Step.to_congruence {xs ys : List (Alphabet J S)} (h : Step xs ys) :
    congruence J S xs ys := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  have core : congruence J S l r := ConGen.Rel.of (M := FreeMonoid (Alphabet J S)) _ _ atom
  have contextual : congruence J S (pre ++ l ++ post) (pre ++ r ++ post) :=
    (congruence J S).mul ((congruence J S).mul ((congruence J S).refl pre) core)
      ((congruence J S).refl post)
  rcases eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact contextual
  · exact (congruence J S).symm contextual

theorem path_iff_conGen (xs ys : List (Alphabet J S)) :
    Path xs ys ↔ congruence J S xs ys := by
  constructor
  · intro path
    induction path with
    | refl => exact (congruence J S).refl _
    | tail path step ih => exact (congruence J S).trans ih step.to_congruence
  · intro h
    change ConGen.Rel (M := FreeMonoid (Alphabet J S)) Atomic xs ys at h
    induction h with
    | of _ _ atom => exact Relation.ReflTransGen.single atom.step
    | refl _ => exact Relation.ReflTransGen.refl
    | symm _ ih => exact ih.symm
    | trans _ _ ih jh => exact ih.trans jh
    | mul _ _ ih jh => exact ih.append jh

end PartitionPilot.Forcing.ExternalWordRewrite

end

end OAI
