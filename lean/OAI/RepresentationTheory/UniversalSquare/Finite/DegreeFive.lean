import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.ColumnCertificates
import OAI.RepresentationTheory.UniversalSquare.Support.NumericalSupport

namespace OAI

/-! Degree Five. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

def fiveWitness : YoungDiagram := diagramOfCols [3,1,1] (by decide)

lemma fiveWitness_cols : fiveWitness.transpose.rowLens = [3,1,1] :=
  diagramOfCols_cols _ _ (by simp)

lemma fiveWitness_card : fiveWitness.card = 5 :=
  diagramOfCols_card _ _ (by simp)

lemma fiveWitness_self : fiveWitness.transpose = fiveWitness := by
  apply YoungDiagram.ext
  decide

def hookPlacement : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 2 4

def flag5 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(1,1,0),(2,2,0),(3,0,1),(4,0,2)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

def flag41 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(1,1,1),(2,2,0),(3,0,2)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

def flag32 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,2),(0,1,1),(1,0,0),(2,2,0)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

def flag311 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(1,2,0),(2,0,2)] : List (ℕ × ℕ × ℕ))
  then 1 else 0

lemma certificate5 : contractionInteger [3,1,1] [3,1,1] [5]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag5 = 20 := by decide +kernel

lemma certificate41 : contractionInteger [3,1,1] [3,1,1] [4,1]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag41 = 2 := by decide +kernel

lemma certificate32 : contractionInteger [3,1,1] [3,1,1] [3,2]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag32 = -4 := by decide +kernel

lemma certificate311 : contractionInteger [3,1,1] [3,1,1] [3,1,1]
    (Equiv.refl (Fin 5)) (Equiv.swap (2 : Fin 5) 3) (Equiv.swap (1 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 3) flag311 = 4 := by
  decide +kernel

noncomputable section

lemma five_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 5)
    (eb : Equiv.Perm (Fin 5)) (et : Fin 5 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [3,1,1] [3,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  exact kronecker_pos_of_integer_certificate _ _ _ [3,1,1] [3,1,1] rs
    fiveWitness_cols fiveWitness_cols (diagramOfCols_cols _ _ hp)
    (Equiv.refl _) eb et L hc

lemma five_positive5 :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols [5] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply five_positive_certificate [5] (by decide) (by simp) rfl
    hookPlacement (Equiv.refl _) flag5
  intro hz
  have hz' : (20 : ℤ) = 0 := certificate5.symm.trans hz
  norm_num at hz'

lemma five_positive41 :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols [4,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply five_positive_certificate [4,1] (by decide) (by simp) rfl
    hookPlacement (Equiv.refl _) flag41
  intro hz
  have hz' : (2 : ℤ) = 0 := certificate41.symm.trans hz
  norm_num at hz'

lemma five_positive32 :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols [3,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply five_positive_certificate [3,2] (by decide) (by simp) rfl
    hookPlacement (Equiv.refl _) flag32
  intro hz
  have hz' : (-4 : ℤ) = 0 := certificate32.symm.trans hz
  norm_num at hz'

lemma five_positive311 :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) := by
  apply five_positive_certificate [3,1,1] (by decide) (by simp) rfl
    (Equiv.swap 2 3) (Equiv.swap 1 2 * Equiv.swap 1 3) flag311
  intro hz
  have hz' : (4 : ℤ) = 0 := certificate311.symm.trans hz
  norm_num at hz'

lemma five_positive_target_eq {μ ν : YoungDiagram} (hμ : μ.card = 5) (hν : ν.card = 5)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

lemma partitionLists_five : partitionLists 5 5 5 =
    {[5],[4,1],[3,2],[3,1,1],[2,2,1],[2,1,1,1],[1,1,1,1,1]} := by decide

theorem five_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 5) :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_five] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [5] (by decide) h
    subst ν
    exact five_positive5
  · have he := eq_diagramOfCols ν [4,1] (by decide) h
    subst ν
    exact five_positive41
  · have he := eq_diagramOfCols ν [3,2] (by decide) h
    subst ν
    exact five_positive32
  · have he := eq_diagramOfCols ν [3,1,1] (by decide) h
    subst ν
    exact five_positive311
  · have he := eq_diagramOfCols ν [2,2,1] (by decide) h
    have ht : diagramOfCols [2,2,1] (by decide) =
        (diagramOfCols [3,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose fiveWitness fiveWitness_card fiveWitness_self
      _ _ five_positive32
    exact five_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [2,1,1,1] (by decide) h
    have ht : diagramOfCols [2,1,1,1] (by decide) =
        (diagramOfCols [4,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose fiveWitness fiveWitness_card fiveWitness_self
      _ _ five_positive41
    exact five_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [1,1,1,1,1] (by decide) h
    have ht : diagramOfCols [1,1,1,1,1] (by decide) =
        (diagramOfCols [5] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose fiveWitness fiveWitness_card fiveWitness_self
      _ _ five_positive5
    exact five_positive_target_eq hν _ (he.trans ht) hh

universe u

theorem universal_tensor_square_five :
    ∃ (lam : YoungDiagram) (hlam : lam.card = 5),
      (∀ (ν : YoungDiagram) (hν : ν.card = 5),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin 5)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  exact ⟨fiveWitness, fiveWitness_card, five_kronecker_pos,
    irreducibles_of_kronecker_pos _ _ five_kronecker_pos⟩

end
end UniversalTensorSquare
end

end OAI
