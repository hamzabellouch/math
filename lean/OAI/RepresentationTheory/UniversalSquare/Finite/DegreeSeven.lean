import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomainsCore
import OAI.RepresentationTheory.UniversalSquare.Support.NumericalSupport

namespace OAI

/-! Degree Seven. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

def sevenWitness : YoungDiagram := diagramOfCols [4,1,1,1] (by decide)

lemma sevenWitness_cols : sevenWitness.transpose.rowLens = [4,1,1,1] :=
  diagramOfCols_cols _ _ (by simp)

lemma sevenWitness_card : sevenWitness.card = 7 :=
  diagramOfCols_card _ _ (by simp)

lemma sevenWitness_self : sevenWitness.transpose = sevenWitness := by
  apply YoungDiagram.ext
  decide

def sevenPlaceB0 : Equiv.Perm (Fin 7) := Equiv.swap 5 6 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 4)))

def sevenPlaceT0 : Equiv.Perm (Fin 7) := Equiv.swap 1 2 * (Equiv.swap 2 6 * (Equiv.swap 1 0 * (Equiv.swap 0 4)))

def sevenFlag0 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,3),(0,2,2),(0,3,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate0 : contractionInteger [4,1,1,1] [4,1,1,1] [1,1,1,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB0 sevenPlaceT0 sevenFlag0 = -6 := by
  unfold sevenFlag0
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB1 : Equiv.Perm (Fin 7) := Equiv.swap 4 1 * (Equiv.swap 1 5 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))

def sevenPlaceT1 : Equiv.Perm (Fin 7) := Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 5))))

def sevenFlag1 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,2,3),(0,3,0),(1,1,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate1 : contractionInteger [4,1,1,1] [4,1,1,1] [2,1,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB1 sevenPlaceT1 sevenFlag1 = -2 := by
  unfold sevenFlag1
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB2 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 5)))

def sevenPlaceT2 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 0 1)))

def sevenFlag2 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,2),(1,2,1),(1,3,3)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate2 : contractionInteger [4,1,1,1] [4,1,1,1] [2,2,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB2 sevenPlaceT2 sevenFlag2 = 2 := by
  unfold sevenFlag2
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB3 : Equiv.Perm (Fin 7) := Equiv.swap 3 6 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 1 2)))

def sevenPlaceT3 : Equiv.Perm (Fin 7) := Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 5))))

def sevenFlag3 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,3),(0,2,3),(0,3,1),(1,0,2),(2,1,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate3 : contractionInteger [4,1,1,1] [4,1,1,1] [3,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB3 sevenPlaceT3 sevenFlag3 = -10 := by
  unfold sevenFlag3
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB4 : Equiv.Perm (Fin 7) := Equiv.swap 2 0 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))

def sevenPlaceT4 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 0 2 * (Equiv.swap 0 1)))

def sevenFlag4 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,1),(0,1,2),(0,2,0),(0,3,3),(1,0,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate4 : contractionInteger [4,1,1,1] [4,1,1,1] [2,2,2,1]
    (Equiv.refl (Fin 7)) sevenPlaceB4 sevenPlaceT4 sevenFlag4 = 2 := by
  unfold sevenFlag4
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB5 : Equiv.Perm (Fin 7) := Equiv.swap 2 6 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))

def sevenPlaceT5 : Equiv.Perm (Fin 7) := Equiv.swap 4 0 * (Equiv.swap 1 2 * (Equiv.swap 0 5))

def sevenFlag5 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,2,2),(0,3,1),(1,1,3),(1,3,0),(2,0,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate5 : contractionInteger [4,1,1,1] [4,1,1,1] [3,2,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB5 sevenPlaceT5 sevenFlag5 = -2 := by
  unfold sevenFlag5
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB6 : Equiv.Perm (Fin 7) := Equiv.swap 5 3 * (Equiv.swap 3 6 * (Equiv.swap 3 0 * (Equiv.swap 0 4 * (Equiv.swap 0 2))))

def sevenPlaceT6 : Equiv.Perm (Fin 7) := Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 0 5))

def sevenFlag6 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,1,1),(1,0,2),(2,3,0),(3,2,3)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate6 : contractionInteger [4,1,1,1] [4,1,1,1] [4,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB6 sevenPlaceT6 sevenFlag6 = 2 := by
  unfold sevenFlag6
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def sevenPlaceB7 : Equiv.Perm (Fin 7) := Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 6 * (Equiv.swap 0 5)))

def sevenPlaceT7 : Equiv.Perm (Fin 7) := Equiv.swap 4 6 * (Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 1 0 * (Equiv.swap 0 2))))

def sevenFlag7 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,0,3),(1,0,3),(1,2,1),(1,3,2),(2,1,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma sevenCertificate7 : contractionInteger [4,1,1,1] [4,1,1,1] [3,2,2]
    (Equiv.refl (Fin 7)) sevenPlaceB7 sevenPlaceT7 sevenFlag7 = 2 := by
  unfold sevenFlag7
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

noncomputable section

lemma seven_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 7)
    (eb : Equiv.Perm (Fin 7)) (et : Fin 7 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [4,1,1,1] [4,1,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  exact kronecker_pos_of_integer_certificate _ _ _ [4,1,1,1] [4,1,1,1] rs
    sevenWitness_cols sevenWitness_cols (diagramOfCols_cols _ _ hp)
    (Equiv.refl _) eb et L hc

lemma seven_positive0 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [1,1,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [1,1,1,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB0 sevenPlaceT0 sevenFlag0
  intro hz
  have hh : (-6 : ℤ) = 0 := sevenCertificate0.symm.trans hz
  norm_num at hh

lemma seven_positive1 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,1,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB1 sevenPlaceT1 sevenFlag1
  intro hz
  have hh : (-2 : ℤ) = 0 := sevenCertificate1.symm.trans hz
  norm_num at hh

lemma seven_positive2 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,2,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,2,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB2 sevenPlaceT2 sevenFlag2
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate2.symm.trans hz
  norm_num at hh

lemma seven_positive3 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB3 sevenPlaceT3 sevenFlag3
  intro hz
  have hh : (-10 : ℤ) = 0 := sevenCertificate3.symm.trans hz
  norm_num at hh

lemma seven_positive4 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,2,2,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,2,2,1] (by decide) (by simp) rfl
    sevenPlaceB4 sevenPlaceT4 sevenFlag4
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate4.symm.trans hz
  norm_num at hh

lemma seven_positive5 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,2,1,1] (by decide) (by simp) rfl
    sevenPlaceB5 sevenPlaceT5 sevenFlag5
  intro hz
  have hh : (-2 : ℤ) = 0 := sevenCertificate5.symm.trans hz
  norm_num at hh

lemma seven_positive6 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [4,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [4,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB6 sevenPlaceT6 sevenFlag6
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate6.symm.trans hz
  norm_num at hh

lemma seven_positive7 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,2,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,2,2] (by decide) (by simp) rfl
    sevenPlaceB7 sevenPlaceT7 sevenFlag7
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate7.symm.trans hz
  norm_num at hh

lemma seven_positive_target_eq {μ ν : YoungDiagram} (hμ : μ.card = 7) (hν : ν.card = 7)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

lemma partitionLists_seven : partitionLists 7 7 7 =
    {[7],[6,1],[5,2],[5,1,1],[4,3],[4,2,1],[4,1,1,1],[3,3,1],[3,2,2],[3,2,1,1],[3,1,1,1,1],[2,2,2,1],[2,2,1,1,1],[2,1,1,1,1,1],[1,1,1,1,1,1,1]} := by decide

theorem seven_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 7) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_seven] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [7] (by decide) h
    have ht : diagramOfCols [7] (by decide) =
        (diagramOfCols [1,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive0
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,1] (by decide) h
    have ht : diagramOfCols [6,1] (by decide) =
        (diagramOfCols [2,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive1
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,2] (by decide) h
    have ht : diagramOfCols [5,2] (by decide) =
        (diagramOfCols [2,2,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive2
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,1,1] (by decide) h
    have ht : diagramOfCols [5,1,1] (by decide) =
        (diagramOfCols [3,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive3
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,3] (by decide) h
    have ht : diagramOfCols [4,3] (by decide) =
        (diagramOfCols [2,2,2,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive4
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,1] (by decide) h
    have ht : diagramOfCols [4,2,1] (by decide) =
        (diagramOfCols [3,2,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive5
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,1,1,1] (by decide) h
    subst ν
    exact seven_positive6
  · have he := eq_diagramOfCols ν [3,3,1] (by decide) h
    have ht : diagramOfCols [3,3,1] (by decide) =
        (diagramOfCols [3,2,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive7
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [3,2,2] (by decide) h
    subst ν
    exact seven_positive7
  · have he := eq_diagramOfCols ν [3,2,1,1] (by decide) h
    subst ν
    exact seven_positive5
  · have he := eq_diagramOfCols ν [3,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive3
  · have he := eq_diagramOfCols ν [2,2,2,1] (by decide) h
    subst ν
    exact seven_positive4
  · have he := eq_diagramOfCols ν [2,2,1,1,1] (by decide) h
    subst ν
    exact seven_positive2
  · have he := eq_diagramOfCols ν [2,1,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive1
  · have he := eq_diagramOfCols ν [1,1,1,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive0

universe u

theorem universal_tensor_square_seven :
    ∃ (lam : YoungDiagram) (hlam : lam.card = 7),
      (∀ (ν : YoungDiagram) (hν : ν.card = 7),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin 7)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  exact ⟨sevenWitness, sevenWitness_card, seven_kronecker_pos,
    irreducibles_of_kronecker_pos _ _ seven_kronecker_pos⟩

end
end UniversalTensorSquare
end

end OAI
