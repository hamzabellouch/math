import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.EightSplitCertificate

namespace OAI

/-! Degree Eight. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

def eightWitness : YoungDiagram := diagramOfCols [4,2,1,1] (by decide)

lemma eightWitness_cols : eightWitness.transpose.rowLens = [4,2,1,1] :=
  diagramOfCols_cols _ _ (by simp)

lemma eightWitness_card : eightWitness.card = 8 :=
  diagramOfCols_card _ _ (by simp)

lemma eightWitness_self : eightWitness.transpose = eightWitness := by
  apply YoungDiagram.ext
  decide

def eightPlaceB0 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 7 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))

def eightPlaceT0 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 0 1 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))

def eightFlag0 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,0,2),(0,1,1),(0,1,3),(0,2,1),(0,3,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate0 : contractionInteger [4,2,1,1] [4,2,1,1] [1,1,1,1,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB0 eightPlaceT0 eightFlag0 = 6 := by
  unfold eightFlag0
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB1 : Equiv.Perm (Fin 8) := Equiv.swap 5 3 * (Equiv.swap 5 6 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 7 * (Equiv.swap 0 1)))))

def eightPlaceT1 : Equiv.Perm (Fin 8) := Equiv.swap 5 6 * (Equiv.swap 2 4 * (Equiv.swap 0 3))

def eightFlag1 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(0,3,3),(1,2,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate1 : contractionInteger [4,2,1,1] [4,2,1,1] [2,1,1,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB1 eightPlaceT1 eightFlag1 = -1 := by
  unfold eightFlag1
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB2 : Equiv.Perm (Fin 8) := Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 3 5 * (Equiv.swap 2 0 * (Equiv.swap 0 6))))

def eightPlaceT2 : Equiv.Perm (Fin 8) := Equiv.swap 2 5 * (Equiv.swap 5 7 * (Equiv.swap 0 4 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))

def eightFlag2 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,1),(0,1,0),(0,2,3),(0,3,2),(1,0,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate2 : contractionInteger [4,2,1,1] [4,2,1,1] [2,2,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB2 eightPlaceT2 eightFlag2 = -2 := by
  unfold eightFlag2
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB3 : Equiv.Perm (Fin 8) := Equiv.swap 6 1 * (Equiv.swap 3 0 * (Equiv.swap 1 7 * (Equiv.swap 1 2 * (Equiv.swap 0 5))))

def eightPlaceT3 : Equiv.Perm (Fin 8) := Equiv.swap 1 7 * (Equiv.swap 1 6 * (Equiv.swap 1 0 * (Equiv.swap 0 5)))

def eightFlag3 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(0,2,3),(0,3,1),(1,1,0),(2,0,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate3 : contractionInteger [4,2,1,1] [4,2,1,1] [3,1,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB3 eightPlaceT3 eightFlag3 = -1 := by
  unfold eightFlag3
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB4 : Equiv.Perm (Fin 8) := Equiv.swap 4 1 * (Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 1 0 * (Equiv.swap 0 7 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))))

def eightPlaceT4 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 1 3 * (Equiv.swap 1 5 * (Equiv.swap 3 6 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))

def eightFlag4 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(0,1,3),(1,0,1),(1,2,0),(1,3,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate4 : contractionInteger [4,2,1,1] [4,2,1,1] [2,2,2,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB4 eightPlaceT4 eightFlag4 = -2 := by
  unfold eightFlag4
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB5 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 0 * (Equiv.swap 3 6 * (Equiv.swap 0 7 * (Equiv.swap 0 2))))

def eightPlaceT5 : Equiv.Perm (Fin 8) := Equiv.swap 6 1 * (Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))))

def eightFlag5 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,2,3),(0,3,2),(1,0,1),(1,1,0),(2,1,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate5 : contractionInteger [4,2,1,1] [4,2,1,1] [3,2,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB5 eightPlaceT5 eightFlag5 = 2 := by
  unfold eightFlag5
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB6 : Equiv.Perm (Fin 8) := Equiv.swap 1 6 * (Equiv.swap 3 0 * (Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 7))))

def eightPlaceT6 : Equiv.Perm (Fin 8) := Equiv.swap 3 6 * (Equiv.swap 3 5 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 4))))

def eightFlag6 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(1,0,3),(2,2,0),(3,3,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate6 : contractionInteger [4,2,1,1] [4,2,1,1] [4,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB6 eightPlaceT6 eightFlag6 = -3 := by
  unfold eightFlag6
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB7 : Equiv.Perm (Fin 8) := Equiv.swap 6 3 * (Equiv.swap 3 0 * (Equiv.swap 0 7 * (Equiv.swap 0 2)))

def eightPlaceT7 : Equiv.Perm (Fin 8) := Equiv.swap 6 4 * (Equiv.swap 4 3 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 7 * (Equiv.swap 0 1))))))

def eightFlag7 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,3,3),(1,0,2),(1,1,1),(1,2,0)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate7 : contractionInteger [4,2,1,1] [4,2,1,1] [2,2,2,2]
    (Equiv.refl (Fin 8)) eightPlaceB7 eightPlaceT7 eightFlag7 = 2 := by
  unfold eightFlag7
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB8 : Equiv.Perm (Fin 8) := Equiv.swap 0 4 * (Equiv.swap 4 1 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))

def eightPlaceT8 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))

def eightFlag8 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,1,1),(1,0,3),(1,2,0),(1,3,1),(2,1,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate8 : contractionInteger [4,2,1,1] [4,2,1,1] [3,2,2,1]
    (Equiv.refl (Fin 8)) eightPlaceB8 eightPlaceT8 eightFlag8 = -3 := by
  unfold eightFlag8
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB9 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 0 7 * (Equiv.swap 2 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))

def eightPlaceT9 : Equiv.Perm (Fin 8) := Equiv.swap 5 1 * (Equiv.swap 2 3 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))

def eightFlag9 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,1),(0,2,0),(0,3,2),(1,1,0),(2,0,0),(2,0,3)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate9 : contractionInteger [4,2,1,1] [4,2,1,1] [3,3,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB9 eightPlaceT9 eightFlag9 = 3 := by
  unfold eightFlag9
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

def eightPlaceB11 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 4 * (Equiv.swap 4 3 * (Equiv.swap 3 6 * (Equiv.swap 2 5))))

def eightPlaceT11 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 1 * (Equiv.swap 1 2 * (Equiv.swap 2 5 * (Equiv.swap 1 3))))

def eightFlag11 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,1,0),(0,2,3),(1,0,0),(1,3,2),(2,0,1)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate11 : contractionInteger [4,2,1,1] [4,2,1,1] [3,3,2]
    (Equiv.refl (Fin 8)) eightPlaceB11 eightPlaceT11 eightFlag11 = 1 := by
  unfold eightFlag11
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

noncomputable section

lemma eight_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 8)
    (eb : Equiv.Perm (Fin 8)) (et : Fin 8 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [4,2,1,1] [4,2,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  exact kronecker_pos_of_integer_certificate _ _ _ [4,2,1,1] [4,2,1,1] rs
    eightWitness_cols eightWitness_cols (diagramOfCols_cols _ _ hp)
    (Equiv.refl _) eb et L hc

lemma eight_positive0 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [1,1,1,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [1,1,1,1,1,1,1,1] (by decide) (by simp) rfl
    eightPlaceB0 eightPlaceT0 eightFlag0
  intro hz
  have hh : (6 : ℤ) = 0 := eightCertificate0.symm.trans hz
  norm_num at hh

lemma eight_positive1 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [2,1,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [2,1,1,1,1,1,1] (by decide) (by simp) rfl
    eightPlaceB1 eightPlaceT1 eightFlag1
  intro hz
  have hh : (-1 : ℤ) = 0 := eightCertificate1.symm.trans hz
  norm_num at hh

lemma eight_positive2 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [2,2,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [2,2,1,1,1,1] (by decide) (by simp) rfl
    eightPlaceB2 eightPlaceT2 eightFlag2
  intro hz
  have hh : (-2 : ℤ) = 0 := eightCertificate2.symm.trans hz
  norm_num at hh

lemma eight_positive3 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [3,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [3,1,1,1,1,1] (by decide) (by simp) rfl
    eightPlaceB3 eightPlaceT3 eightFlag3
  intro hz
  have hh : (-1 : ℤ) = 0 := eightCertificate3.symm.trans hz
  norm_num at hh

lemma eight_positive4 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [2,2,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [2,2,2,1,1] (by decide) (by simp) rfl
    eightPlaceB4 eightPlaceT4 eightFlag4
  intro hz
  have hh : (-2 : ℤ) = 0 := eightCertificate4.symm.trans hz
  norm_num at hh

lemma eight_positive5 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [3,2,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [3,2,1,1,1] (by decide) (by simp) rfl
    eightPlaceB5 eightPlaceT5 eightFlag5
  intro hz
  have hh : (2 : ℤ) = 0 := eightCertificate5.symm.trans hz
  norm_num at hh

lemma eight_positive6 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [4,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [4,1,1,1,1] (by decide) (by simp) rfl
    eightPlaceB6 eightPlaceT6 eightFlag6
  intro hz
  have hh : (-3 : ℤ) = 0 := eightCertificate6.symm.trans hz
  norm_num at hh

lemma eight_positive7 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [2,2,2,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [2,2,2,2] (by decide) (by simp) rfl
    eightPlaceB7 eightPlaceT7 eightFlag7
  intro hz
  have hh : (2 : ℤ) = 0 := eightCertificate7.symm.trans hz
  norm_num at hh

lemma eight_positive8 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [3,2,2,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [3,2,2,1] (by decide) (by simp) rfl
    eightPlaceB8 eightPlaceT8 eightFlag8
  intro hz
  have hh : (-3 : ℤ) = 0 := eightCertificate8.symm.trans hz
  norm_num at hh

lemma eight_positive9 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [3,3,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [3,3,1,1] (by decide) (by simp) rfl
    eightPlaceB9 eightPlaceT9 eightFlag9
  intro hz
  have hh : (3 : ℤ) = 0 := eightCertificate9.symm.trans hz
  norm_num at hh

lemma eight_positive10 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [4,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [4,2,1,1] (by decide) (by simp) rfl
    eightPlaceB10 eightPlaceT10 eightFlag10
  intro hz
  have hh : (-4 : ℤ) = 0 := eightCertificate10.symm.trans hz
  norm_num at hh

lemma eight_positive11 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [3,3,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [3,3,2] (by decide) (by simp) rfl
    eightPlaceB11 eightPlaceT11 eightFlag11
  intro hz
  have hh : (1 : ℤ) = 0 := eightCertificate11.symm.trans hz
  norm_num at hh

lemma eight_positive_target_eq {μ ν : YoungDiagram} (hμ : μ.card = 8) (hν : ν.card = 8)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

lemma partitionLists_eight : partitionLists 8 8 8 =
    {[8],[7,1],[6,2],[6,1,1],[5,3],[5,2,1],[5,1,1,1],[4,4],[4,3,1],[4,2,2],[4,2,1,1],[4,1,1,1,1],[3,3,2],[3,3,1,1],[3,2,2,1],[3,2,1,1,1],[3,1,1,1,1,1],[2,2,2,2],[2,2,2,1,1],[2,2,1,1,1,1],[2,1,1,1,1,1,1],[1,1,1,1,1,1,1,1]} := by decide

theorem eight_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 8) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_eight] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [8] (by decide) h
    have ht : diagramOfCols [8] (by decide) =
        (diagramOfCols [1,1,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive0
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [7,1] (by decide) h
    have ht : diagramOfCols [7,1] (by decide) =
        (diagramOfCols [2,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive1
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,2] (by decide) h
    have ht : diagramOfCols [6,2] (by decide) =
        (diagramOfCols [2,2,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive2
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,1,1] (by decide) h
    have ht : diagramOfCols [6,1,1] (by decide) =
        (diagramOfCols [3,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive3
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,3] (by decide) h
    have ht : diagramOfCols [5,3] (by decide) =
        (diagramOfCols [2,2,2,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive4
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,2,1] (by decide) h
    have ht : diagramOfCols [5,2,1] (by decide) =
        (diagramOfCols [3,2,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive5
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,1,1,1] (by decide) h
    have ht : diagramOfCols [5,1,1,1] (by decide) =
        (diagramOfCols [4,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive6
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,4] (by decide) h
    have ht : diagramOfCols [4,4] (by decide) =
        (diagramOfCols [2,2,2,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive7
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,3,1] (by decide) h
    have ht : diagramOfCols [4,3,1] (by decide) =
        (diagramOfCols [3,2,2,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive8
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,2] (by decide) h
    have ht : diagramOfCols [4,2,2] (by decide) =
        (diagramOfCols [3,3,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive9
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,1,1] (by decide) h
    subst ν
    exact eight_positive10
  · have he := eq_diagramOfCols ν [4,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive6
  · have he := eq_diagramOfCols ν [3,3,2] (by decide) h
    subst ν
    exact eight_positive11
  · have he := eq_diagramOfCols ν [3,3,1,1] (by decide) h
    subst ν
    exact eight_positive9
  · have he := eq_diagramOfCols ν [3,2,2,1] (by decide) h
    subst ν
    exact eight_positive8
  · have he := eq_diagramOfCols ν [3,2,1,1,1] (by decide) h
    subst ν
    exact eight_positive5
  · have he := eq_diagramOfCols ν [3,1,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive3
  · have he := eq_diagramOfCols ν [2,2,2,2] (by decide) h
    subst ν
    exact eight_positive7
  · have he := eq_diagramOfCols ν [2,2,2,1,1] (by decide) h
    subst ν
    exact eight_positive4
  · have he := eq_diagramOfCols ν [2,2,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive2
  · have he := eq_diagramOfCols ν [2,1,1,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive1
  · have he := eq_diagramOfCols ν [1,1,1,1,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive0

universe u

theorem universal_tensor_square_eight :
    ∃ (lam : YoungDiagram) (hlam : lam.card = 8),
      (∀ (ν : YoungDiagram) (hν : ν.card = 8),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin 8)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  exact ⟨eightWitness, eightWitness_card, eight_kronecker_pos,
    irreducibles_of_kronecker_pos _ _ eight_kronecker_pos⟩

end
end UniversalTensorSquare
end

end OAI
