import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeFive
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeSeven
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeEight
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg0 : RowSquare [1] [1] := by
  exact rowSquare_trivial _ (by decide)

lemma sg1 : RowSquare [1,1] [2] := by
  exact rowSquare_trivial _ (by decide)

lemma sg2 : RowSquare [2] [2] := by
  exact rowSquare_trivial _ (by decide)

lemma sg3 : RowSquare [1,1,1] [3] := by
  exact rowSquare_trivial _ (by decide)

lemma sg4 : RowSquare [2,1] [1,1,1] := by
  have he : rowDiagram [2,1] = (staircase 2) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [2,1]) (rowDiagram [1,1,1])
  have hh : SquareOccurs (staircase 2) (rowDiagram [1,1,1]) :=
    ⟨3,canonicalTableau _ (staircase_card 2),canonicalTableau _ (rowDiagram_card [1,1,1]),
      saxl_kronecker_pos 2 (by decide) _ (rowDiagram_card [1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1])) he) hh

lemma sg5 : RowSquare [2,1] [2,1] := by
  have he : rowDiagram [2,1] = (staircase 2) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [2,1]) (rowDiagram [2,1])
  have hh : SquareOccurs (staircase 2) (rowDiagram [2,1]) :=
    ⟨3,canonicalTableau _ (staircase_card 2),canonicalTableau _ (rowDiagram_card [2,1]),
      saxl_kronecker_pos 2 (by decide) _ (rowDiagram_card [2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1])) he) hh

lemma sg6 : RowSquare [2,1] [3] := by
  exact rowSquare_trivial _ (by decide)

lemma sg7 : RowSquare [3] [3] := by
  exact rowSquare_trivial _ (by decide)

lemma sg8 : RowSquare [1,1,1,1] [4] := by
  exact rowSquare_trivial _ (by decide)

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg11 : RowSquare [2,1,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg12 : RowSquare [2,1,1] [4] := by
  exact rowSquare_trivial _ (by decide)

lemma sg13 : RowSquare [2,2] [1,1,1,1] := by
  exact rowSquare_target_transpose (q := [4]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg14 : RowSquare [2,2] [2,2] := by
  exact rowSquare_even 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg15 : RowSquare [2,2] [4] := by
  exact rowSquare_trivial _ (by decide)

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg19 : RowSquare [3,1] [4] := by
  exact rowSquare_trivial _ (by decide)

lemma sg20 : RowSquare [4] [4] := by
  exact rowSquare_trivial _ (by decide)

lemma sg21 : RowSquare [1,1,1,1,1] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg25 : RowSquare [2,1,1,1] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg26 : RowSquare [2,2,1] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg27 : RowSquare [2,2,1] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg28 : RowSquare [2,2,1] [3,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg29 : RowSquare [2,2,1] [3,2] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg30 : RowSquare [2,2,1] [4,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg31 : RowSquare [2,2,1] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg32 : RowSquare [3,1,1] [1,1,1,1,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [1,1,1,1,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [1,1,1,1,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1]),
      five_kronecker_pos _ (rowDiagram_card [1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1])) he) hh

lemma sg33 : RowSquare [3,1,1] [2,1,1,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [2,1,1,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [2,1,1,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1]),
      five_kronecker_pos _ (rowDiagram_card [2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1])) he) hh

lemma sg34 : RowSquare [3,1,1] [2,2,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [2,2,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [2,2,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [2,2,1]),
      five_kronecker_pos _ (rowDiagram_card [2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1])) he) hh

lemma sg35 : RowSquare [3,1,1] [3,1,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [3,1,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [3,1,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [3,1,1]),
      five_kronecker_pos _ (rowDiagram_card [3,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1])) he) hh

lemma sg36 : RowSquare [3,1,1] [3,2] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [3,2])
  have hh : SquareOccurs fiveWitness (rowDiagram [3,2]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [3,2]),
      five_kronecker_pos _ (rowDiagram_card [3,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2])) he) hh

lemma sg37 : RowSquare [3,1,1] [4,1] := by
  have he : rowDiagram [3,1,1] = fiveWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,1,1]) (rowDiagram [4,1])
  have hh : SquareOccurs fiveWitness (rowDiagram [4,1]) :=
    ⟨5,canonicalTableau _ fiveWitness_card,canonicalTableau _ (rowDiagram_card [4,1]),
      five_kronecker_pos _ (rowDiagram_card [4,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,1])) he) hh

lemma sg38 : RowSquare [3,1,1] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg41 : RowSquare [3,2] [3,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg42 : RowSquare [3,2] [3,2] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg43 : RowSquare [3,2] [4,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg44 : RowSquare [3,2] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg48 : RowSquare [4,1] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg49 : RowSquare [5] [5] := by
  exact rowSquare_trivial _ (by decide)

lemma sg50 : RowSquare [1,1,1,1,1,1] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg54 : RowSquare [2,1,1,1,1] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg55 : RowSquare [2,2,1,1] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg56 : RowSquare [2,2,1,1] [3,1,1,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg57 : RowSquare [2,2,1,1] [3,2,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg58 : RowSquare [2,2,1,1] [4,1,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg59 : RowSquare [2,2,1,1] [4,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg60 : RowSquare [2,2,1,1] [5,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg61 : RowSquare [2,2,1,1] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg62 : RowSquare [2,2,2] [2,2,2] := by
  exact rowSquare_even 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg64 : RowSquare [2,2,2] [4,2] := by
  exact rowSquare_even 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg65 : RowSquare [2,2,2] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg74 : RowSquare [3,2,1] [1,1,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [1,1,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1])) he) hh

lemma sg75 : RowSquare [3,2,1] [2,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1])) he) hh

lemma sg76 : RowSquare [3,2,1] [2,2,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,2,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,2,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,2,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1])) he) hh

lemma sg77 : RowSquare [3,2,1] [2,2,2] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,2,2])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,2,2]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,2,2]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2])) he) hh

lemma sg78 : RowSquare [3,2,1] [3,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [3,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [3,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [3,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [3,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1,1])) he) hh

lemma sg79 : RowSquare [3,2,1] [3,2,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [3,2,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [3,2,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [3,2,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [3,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,1])) he) hh

lemma sg80 : RowSquare [3,2,1] [3,3] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [3,3])
  have hh : SquareOccurs (staircase 3) (rowDiagram [3,3]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [3,3]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [3,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3])) he) hh

lemma sg81 : RowSquare [3,2,1] [4,2] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [4,2])
  have hh : SquareOccurs (staircase 3) (rowDiagram [4,2]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [4,2]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [4,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,2])) he) hh

lemma sg82 : RowSquare [3,2,1] [5,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [5,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [5,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [5,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [5,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,1])) he) hh

lemma sg83 : RowSquare [3,3] [2,2,2] := by
  exact rowSquare_even 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg85 : RowSquare [3,3] [4,2] := by
  exact rowSquare_even 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg86 : RowSquare [3,3] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg96 : RowSquare [4,1,1] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg98 : RowSquare [4,2] [3,1,1,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg99 : RowSquare [4,2] [3,2,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg100 : RowSquare [4,2] [4,1,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg101 : RowSquare [4,2] [4,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg102 : RowSquare [4,2] [5,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg103 : RowSquare [4,2] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg107 : RowSquare [5,1] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg108 : RowSquare [6] [6] := by
  exact rowSquare_trivial _ (by decide)

lemma sg109 : RowSquare [1,1,1,1,1,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg113 : RowSquare [2,1,1,1,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg122 : RowSquare [2,2,1,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg123 : RowSquare [2,2,2,1] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg124 : RowSquare [2,2,2,1] [3,2,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg125 : RowSquare [2,2,2,1] [3,3,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg126 : RowSquare [2,2,2,1] [4,1,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg127 : RowSquare [2,2,2,1] [4,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg128 : RowSquare [2,2,2,1] [4,3] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg129 : RowSquare [2,2,2,1] [5,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg130 : RowSquare [2,2,2,1] [5,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg131 : RowSquare [2,2,2,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg141 : RowSquare [3,1,1,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg178 : RowSquare [4,1,1,1] [1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [1,1,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [1,1,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1])) he) hh

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1])) he) hh

lemma sg180 : RowSquare [4,1,1,1] [2,2,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1])) he) hh

lemma sg181 : RowSquare [4,1,1,1] [2,2,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1])) he) hh

lemma sg182 : RowSquare [4,1,1,1] [3,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [3,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1,1,1])) he) hh

lemma sg183 : RowSquare [4,1,1,1] [3,2,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,2,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,2,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,2,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [3,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,1,1])) he) hh

lemma sg184 : RowSquare [4,1,1,1] [3,2,2] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,2,2])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,2,2]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,2,2]),
      seven_kronecker_pos _ (rowDiagram_card [3,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,2])) he) hh

lemma sg185 : RowSquare [4,1,1,1] [3,3,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,3,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,3,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,3,1]),
      seven_kronecker_pos _ (rowDiagram_card [3,3,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,1])) he) hh

lemma sg186 : RowSquare [4,1,1,1] [4,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [4,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [4,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [4,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [4,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,1,1,1])) he) hh

lemma sg187 : RowSquare [4,1,1,1] [4,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [4,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [4,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [4,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [4,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,2,1])) he) hh

lemma sg188 : RowSquare [4,1,1,1] [4,3] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [4,3])
  have hh : SquareOccurs sevenWitness (rowDiagram [4,3]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [4,3]),
      seven_kronecker_pos _ (rowDiagram_card [4,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,3])) he) hh

lemma sg189 : RowSquare [4,1,1,1] [5,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [5,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [5,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [5,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [5,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,1,1])) he) hh

lemma sg190 : RowSquare [4,1,1,1] [5,2] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [5,2])
  have hh : SquareOccurs sevenWitness (rowDiagram [5,2]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [5,2]),
      seven_kronecker_pos _ (rowDiagram_card [5,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,2])) he) hh

lemma sg191 : RowSquare [4,1,1,1] [6,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [6,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [6,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [6,1]),
      seven_kronecker_pos _ (rowDiagram_card [6,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [6,1])) he) hh

lemma sg192 : RowSquare [4,1,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg206 : RowSquare [4,2,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg208 : RowSquare [4,3] [3,2,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg209 : RowSquare [4,3] [3,2,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg210 : RowSquare [4,3] [3,3,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg211 : RowSquare [4,3] [4,1,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg212 : RowSquare [4,3] [4,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg213 : RowSquare [4,3] [4,3] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg214 : RowSquare [4,3] [5,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg215 : RowSquare [4,3] [5,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg216 : RowSquare [4,3] [6,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg217 : RowSquare [4,3] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg226 : RowSquare [5,1,1] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg234 : RowSquare [7] [7] := by
  exact rowSquare_trivial _ (by decide)

lemma sg235 : RowSquare [1,1,1,1,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

lemma sg238 : RowSquare [2,1,1,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

lemma sg248 : RowSquare [2,2,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

lemma sg249 : RowSquare [2,2,2,1,1] [3,2,2,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg251 : RowSquare [2,2,2,1,1] [3,3,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg253 : RowSquare [2,2,2,1,1] [6,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg256 : RowSquare [2,2,2,2] [4,2,2] := by
  exact rowSquare_even 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg257 : RowSquare [2,2,2,2] [4,4] := by
  exact rowSquare_even 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg259 : RowSquare [2,2,2,2] [6,2] := by
  exact rowSquare_even 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg269 : RowSquare [3,1,1,1,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

lemma sg306 : RowSquare [3,3,2] [1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [8]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg330 : RowSquare [4,2,1,1] [1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [1,1,1,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [1,1,1,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1])) he) hh

lemma sg331 : RowSquare [4,2,1,1] [2,1,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [2,1,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [2,1,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1,1])) he) hh

lemma sg332 : RowSquare [4,2,1,1] [2,2,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [2,2,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [2,2,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [2,2,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [2,2,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1,1])) he) hh

lemma sg333 : RowSquare [4,2,1,1] [2,2,2,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [2,2,2,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [2,2,2,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [2,2,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1,1])) he) hh

lemma sg334 : RowSquare [4,2,1,1] [2,2,2,2] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [2,2,2,2])
  have hh : SquareOccurs eightWitness (rowDiagram [2,2,2,2]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,2]),
      eight_kronecker_pos _ (rowDiagram_card [2,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,2])) he) hh

lemma sg335 : RowSquare [4,2,1,1] [3,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [3,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [3,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [3,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [3,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1,1,1,1])) he) hh

lemma sg336 : RowSquare [4,2,1,1] [3,2,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [3,2,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [3,2,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [3,2,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [3,2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,1,1,1])) he) hh

lemma sg337 : RowSquare [4,2,1,1] [3,2,2,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [3,2,2,1])
  have hh : SquareOccurs eightWitness (rowDiagram [3,2,2,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [3,2,2,1]),
      eight_kronecker_pos _ (rowDiagram_card [3,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,2,1])) he) hh

lemma sg338 : RowSquare [4,2,1,1] [3,3,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [3,3,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [3,3,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [3,3,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [3,3,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,1,1])) he) hh

lemma sg339 : RowSquare [4,2,1,1] [3,3,2] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [3,3,2])
  have hh : SquareOccurs eightWitness (rowDiagram [3,3,2]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [3,3,2]),
      eight_kronecker_pos _ (rowDiagram_card [3,3,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,2])) he) hh

lemma sg340 : RowSquare [4,2,1,1] [4,2,2] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [4,2,2])
  have hh : SquareOccurs eightWitness (rowDiagram [4,2,2]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [4,2,2]),
      eight_kronecker_pos _ (rowDiagram_card [4,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,2,2])) he) hh

lemma sg341 : RowSquare [4,2,1,1] [4,3,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [4,3,1])
  have hh : SquareOccurs eightWitness (rowDiagram [4,3,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [4,3,1]),
      eight_kronecker_pos _ (rowDiagram_card [4,3,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,3,1])) he) hh

lemma sg342 : RowSquare [4,2,1,1] [4,4] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [4,4])
  have hh : SquareOccurs eightWitness (rowDiagram [4,4]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [4,4]),
      eight_kronecker_pos _ (rowDiagram_card [4,4])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,4])) he) hh

lemma sg343 : RowSquare [4,2,1,1] [5,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [5,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [5,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [5,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [5,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,1,1,1])) he) hh

lemma sg344 : RowSquare [4,2,1,1] [5,2,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [5,2,1])
  have hh : SquareOccurs eightWitness (rowDiagram [5,2,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [5,2,1]),
      eight_kronecker_pos _ (rowDiagram_card [5,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,2,1])) he) hh

lemma sg345 : RowSquare [4,2,1,1] [5,3] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [5,3])
  have hh : SquareOccurs eightWitness (rowDiagram [5,3]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [5,3]),
      eight_kronecker_pos _ (rowDiagram_card [5,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,3])) he) hh

lemma sg346 : RowSquare [4,2,1,1] [6,2] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [6,2])
  have hh : SquareOccurs eightWitness (rowDiagram [6,2]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [6,2]),
      eight_kronecker_pos _ (rowDiagram_card [6,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [6,2])) he) hh

lemma sg347 : RowSquare [4,2,1,1] [7,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [7,1])
  have hh : SquareOccurs eightWitness (rowDiagram [7,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [7,1]),
      eight_kronecker_pos _ (rowDiagram_card [7,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [7,1])) he) hh

lemma sg366 : RowSquare [4,4] [4,2,2] := by
  exact rowSquare_even 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg367 : RowSquare [4,4] [4,4] := by
  exact rowSquare_even 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg369 : RowSquare [4,4] [6,2] := by
  exact rowSquare_even 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg401 : RowSquare [5,3] [3,2,2,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg403 : RowSquare [5,3] [3,3,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg404 : RowSquare [5,3] [4,2,1,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg405 : RowSquare [5,3] [4,2,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg406 : RowSquare [5,3] [4,3,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg408 : RowSquare [5,3] [5,1,1,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg409 : RowSquare [5,3] [5,2,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg410 : RowSquare [5,3] [5,3] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg411 : RowSquare [5,3] [6,1,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg412 : RowSquare [5,3] [6,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg421 : RowSquare [6,1,1] [8] := by
  exact rowSquare_trivial _ (by decide)

lemma sg426 : RowSquare [8] [8] := by
  exact rowSquare_trivial _ (by decide)

lemma sg427 : RowSquare [1,1,1,1,1,1,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg431 : RowSquare [2,1,1,1,1,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg445 : RowSquare [2,2,2,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg446 : RowSquare [2,2,2,2,1] [3,3,3] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg454 : RowSquare [3,1,1,1,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg474 : RowSquare [3,2,1,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg509 : RowSquare [3,3,1,1,1] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg516 : RowSquare [3,3,3] [1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [9]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg586 : RowSquare [5,1,1,1,1] [1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [9]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg656 : RowSquare [5,4] [3,2,2,2] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg657 : RowSquare [5,4] [3,3,2,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg658 : RowSquare [5,4] [3,3,3] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg659 : RowSquare [5,4] [4,2,2,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg660 : RowSquare [5,4] [4,3,1,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg661 : RowSquare [5,4] [4,3,2] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg662 : RowSquare [5,4] [4,4,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg663 : RowSquare [5,4] [5,2,1,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg664 : RowSquare [5,4] [5,2,2] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg665 : RowSquare [5,4] [5,3,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg666 : RowSquare [5,4] [5,4] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg667 : RowSquare [5,4] [6,1,1,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg668 : RowSquare [5,4] [6,2,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg669 : RowSquare [5,4] [6,3] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg670 : RowSquare [5,4] [7,2] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg671 : RowSquare [5,4] [8,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg672 : RowSquare [5,4] [9] := by
  exact rowSquare_trivial _ (by decide)

lemma sg718 : RowSquare [1,1,1,1,1,1,1,1,1,1] [10] := by
  exact rowSquare_trivial _ (by decide)

lemma sg720 : RowSquare [2,1,1,1,1,1,1,1,1] [10] := by
  exact rowSquare_trivial _ (by decide)

lemma sg730 : RowSquare [2,2,2,2,1,1] [10] := by
  exact rowSquare_trivial _ (by decide)

lemma sg757 : RowSquare [3,2,2,1,1,1] [10] := by
  exact rowSquare_trivial _ (by decide)

lemma sg789 : RowSquare [3,3,1,1,1,1] [10] := by
  exact rowSquare_trivial _ (by decide)

lemma sg849 : RowSquare [4,3,2,1] [1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [1,1,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1])) he) hh

lemma sg850 : RowSquare [4,3,2,1] [2,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1,1,1,1])) he) hh

lemma sg851 : RowSquare [4,3,2,1] [2,2,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1,1,1,1])) he) hh

lemma sg852 : RowSquare [4,3,2,1] [2,2,2,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,2,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,2,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,2,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,2,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1,1,1,1])) he) hh

lemma sg853 : RowSquare [4,3,2,1] [2,2,2,2,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,2,2,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,2,2,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,2,2,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,2,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,2,1,1])) he) hh

lemma sg854 : RowSquare [4,3,2,1] [2,2,2,2,2] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,2,2,2])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,2,2,2]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,2,2,2]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,2,2])) he) hh

lemma sg855 : RowSquare [4,3,2,1] [3,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,1,1,1,1,1,1,1])) he) hh

lemma sg856 : RowSquare [4,3,2,1] [3,2,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,2,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,2,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,2,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,1,1,1,1,1])) he) hh

lemma sg857 : RowSquare [4,3,2,1] [3,2,2,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,2,2,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,2,2,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,2,2,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,2,2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,2,1,1,1])) he) hh

lemma sg858 : RowSquare [4,3,2,1] [3,2,2,2,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,2,2,2,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,2,2,2,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,2,2,2,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,2,2,1])) he) hh

lemma sg859 : RowSquare [4,3,2,1] [3,3,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,3,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,3,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,3,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,3,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,1,1,1,1])) he) hh

lemma sg860 : RowSquare [4,3,2,1] [3,3,2,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,3,2,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,3,2,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,3,2,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,3,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,2,1,1])) he) hh

lemma sg861 : RowSquare [4,3,2,1] [3,3,2,2] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,3,2,2])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,3,2,2]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,3,2,2]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,3,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,2,2])) he) hh

lemma sg862 : RowSquare [4,3,2,1] [3,3,3,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,3,3,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,3,3,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,3,3,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,3,3,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,3,1])) he) hh

lemma sg863 : RowSquare [4,3,2,1] [4,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,1,1,1,1,1,1])) he) hh

lemma sg864 : RowSquare [4,3,2,1] [4,2,2,2] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,2,2,2])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,2,2,2]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,2,2,2]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,2,2,2])) he) hh

lemma sg865 : RowSquare [4,3,2,1] [4,3,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,3,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,3,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,3,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,3,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,3,1,1,1])) he) hh

lemma sg866 : RowSquare [4,3,2,1] [4,3,2,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,3,2,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,3,2,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,3,2,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,3,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,3,2,1])) he) hh

lemma sg867 : RowSquare [4,3,2,1] [4,3,3] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,3,3])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,3,3]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,3,3]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,3,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,3,3])) he) hh

lemma sg868 : RowSquare [4,3,2,1] [4,4,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,4,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,4,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,4,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,4,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,4,1,1])) he) hh

lemma sg869 : RowSquare [4,3,2,1] [4,4,2] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [4,4,2])
  have hh : SquareOccurs (staircase 4) (rowDiagram [4,4,2]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [4,4,2]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [4,4,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,4,2])) he) hh

lemma sg870 : RowSquare [4,3,2,1] [5,4,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [5,4,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [5,4,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [5,4,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [5,4,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,4,1])) he) hh

lemma sg871 : RowSquare [4,3,2,1] [5,5] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [5,5])
  have hh : SquareOccurs (staircase 4) (rowDiagram [5,5]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [5,5]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [5,5])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,5])) he) hh

lemma sg910 : RowSquare [5,2,1,1,1] [1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [10]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg996 : RowSquare [5,5] [4,4,2] := by
  exact rowSquare_even 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg1075 : RowSquare [6,4] [3,3,3,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1076 : RowSquare [6,4] [4,2,2,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1077 : RowSquare [6,4] [4,3,3] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1078 : RowSquare [6,4] [4,4,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1079 : RowSquare [6,4] [5,2,2,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1080 : RowSquare [6,4] [5,3,1,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1081 : RowSquare [6,4] [5,3,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1082 : RowSquare [6,4] [5,4,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1083 : RowSquare [6,4] [6,2,1,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1084 : RowSquare [6,4] [6,2,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1085 : RowSquare [6,4] [6,3,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1086 : RowSquare [6,4] [6,4] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1087 : RowSquare [6,4] [7,1,1,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1088 : RowSquare [6,4] [7,2,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1089 : RowSquare [6,4] [7,3] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1090 : RowSquare [6,4] [9,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1091 : RowSquare [6,4] [10] := by
  exact rowSquare_trivial _ (by decide)

lemma sg1131 : RowSquare [2,2,2,2,2,1] [3,3,3,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1132 : RowSquare [2,2,2,2,2,1] [4,3,2,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1133 : RowSquare [2,2,2,2,2,1] [4,3,3,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1134 : RowSquare [2,2,2,2,2,1] [4,4,2,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1135 : RowSquare [2,2,2,2,2,1] [4,4,3] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1177 : RowSquare [3,3,1,1,1,1,1] [11] := by
  exact rowSquare_trivial _ (by decide)

lemma sg1180 : RowSquare [3,3,2,1,1,1] [11] := by
  exact rowSquare_trivial _ (by decide)

lemma sg1232 : RowSquare [4,3,3,1] [1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [11]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg1327 : RowSquare [6,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [11]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg1478 : RowSquare [6,5] [3,3,3,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1479 : RowSquare [6,5] [4,3,2,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1480 : RowSquare [6,5] [4,3,3,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1481 : RowSquare [6,5] [4,4,2,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1482 : RowSquare [6,5] [4,4,3] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1483 : RowSquare [6,5] [5,2,2,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1484 : RowSquare [6,5] [5,3,2,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1485 : RowSquare [6,5] [5,3,3] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1486 : RowSquare [6,5] [5,4,1,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1487 : RowSquare [6,5] [5,4,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1488 : RowSquare [6,5] [5,5,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1489 : RowSquare [6,5] [6,2,2,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1490 : RowSquare [6,5] [6,3,1,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1491 : RowSquare [6,5] [6,3,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1492 : RowSquare [6,5] [6,4,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1493 : RowSquare [6,5] [6,5] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1494 : RowSquare [6,5] [7,2,1,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1495 : RowSquare [6,5] [7,2,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1496 : RowSquare [6,5] [7,3,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1497 : RowSquare [6,5] [7,4] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1615 : RowSquare [3,3,2,1,1,1,1] [12] := by
  exact rowSquare_trivial _ (by decide)

lemma sg1650 : RowSquare [4,4,2,2] [1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [12]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg1682 : RowSquare [5,3,2,1,1] [1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [12]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg1734 : RowSquare [5,4,2,1] [12] := by
  exact rowSquare_trivial _ (by decide)

lemma sg1754 : RowSquare [6,2,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [12]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg1871 : RowSquare [6,6] [6,6] := by
  exact rowSquare_even 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg1928 : RowSquare [7,5] [4,3,3,2] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1930 : RowSquare [7,5] [4,4,3,1] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1931 : RowSquare [7,5] [4,4,4] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1932 : RowSquare [7,5] [5,3,3,1] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1933 : RowSquare [7,5] [5,4,2,1] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1934 : RowSquare [7,5] [5,4,3] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1936 : RowSquare [7,5] [5,5,2] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1937 : RowSquare [7,5] [6,2,2,2] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1938 : RowSquare [7,5] [6,3,2,1] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1939 : RowSquare [7,5] [6,3,3] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1940 : RowSquare [7,5] [6,4,1,1] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1941 : RowSquare [7,5] [6,4,2] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1942 : RowSquare [7,5] [6,5,1] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2015 : RowSquare [2,2,2,2,2,2,1] [7,6] := by
  exact rowSquare_short 6 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2016 : RowSquare [2,2,2,2,2,2,1] [8,5] := by
  exact rowSquare_short 6 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2017 : RowSquare [2,2,2,2,2,2,1] [9,4] := by
  exact rowSquare_short 6 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2018 : RowSquare [2,2,2,2,2,2,1] [10,3] := by
  exact rowSquare_short 6 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2019 : RowSquare [2,2,2,2,2,2,1] [11,2] := by
  exact rowSquare_short 6 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2072 : RowSquare [4,3,1,1,1,1,1,1] [13] := by
  exact rowSquare_trivial _ (by decide)

lemma sg2105 : RowSquare [4,4,1,1,1,1,1] [13] := by
  exact rowSquare_trivial _ (by decide)

lemma sg2107 : RowSquare [4,4,3,2] [1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [13]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg2137 : RowSquare [5,3,3,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [13]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg2251 : RowSquare [7,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [13]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg2364 : RowSquare [7,6] [4,4,4,1] := by
  exact rowSquare_short 6 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg2488 : RowSquare [2,2,2,2,2,2,2] [8,6] := by
  exact rowSquare_even 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg2489 : RowSquare [2,2,2,2,2,2,2] [10,4] := by
  exact rowSquare_even 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg2573 : RowSquare [4,4,1,1,1,1,1,1] [14] := by
  exact rowSquare_trivial _ (by decide)

lemma sg2596 : RowSquare [5,4,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [14]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg2626 : RowSquare [6,3,2,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [14]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg2702 : RowSquare [7,2,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [14]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg3106 : RowSquare [8,6] [4,4,4,2] := by
  exact rowSquare_short 6 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg3239 : RowSquare [4,4,2,1,1,1,1,1] [15] := by
  exact rowSquare_trivial _ (by decide)

lemma sg3299 : RowSquare [5,4,3,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])) he) hh

lemma sg3300 : RowSquare [5,4,3,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [2,1,1,1,1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [2,1,1,1,1,1,1,1,1,1,1,1,1,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [2,1,1,1,1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1,1,1,1,1,1,1,1,1])) he) hh

lemma sg3301 : RowSquare [5,4,3,2,1] [2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [2,2,1,1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [2,2,1,1,1,1,1,1,1,1,1,1,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [2,2,1,1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [2,2,1,1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1,1,1,1,1,1,1,1,1])) he) hh

lemma sg3302 : RowSquare [5,4,3,2,1] [2,2,2,2,1,1,1,1,1,1,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [2,2,2,2,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [2,2,2,2,1,1,1,1,1,1,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [2,2,2,2,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [2,2,2,2,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,2,1,1,1,1,1,1,1])) he) hh

lemma sg3303 : RowSquare [5,4,3,2,1] [3,2,2,2,2,2,2] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [3,2,2,2,2,2,2])
  have hh : SquareOccurs (staircase 5) (rowDiagram [3,2,2,2,2,2,2]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [3,2,2,2,2,2,2]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [3,2,2,2,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,2,2,2,2,2])) he) hh

lemma sg3304 : RowSquare [5,4,3,2,1] [3,3,2,2,2,2,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [3,3,2,2,2,2,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [3,3,2,2,2,2,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [3,3,2,2,2,2,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [3,3,2,2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,2,2,2,2,1])) he) hh

lemma sg3305 : RowSquare [5,4,3,2,1] [3,3,3,2,2,2] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [3,3,3,2,2,2])
  have hh : SquareOccurs (staircase 5) (rowDiagram [3,3,3,2,2,2]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [3,3,3,2,2,2]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [3,3,3,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,3,2,2,2])) he) hh

lemma sg3306 : RowSquare [5,4,3,2,1] [4,3,2,2,2,2] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [4,3,2,2,2,2])
  have hh : SquareOccurs (staircase 5) (rowDiagram [4,3,2,2,2,2]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [4,3,2,2,2,2]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [4,3,2,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,3,2,2,2,2])) he) hh

lemma sg3521 : RowSquare [8,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [15]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg3739 : RowSquare [2,2,2,2,2,2,2,1,1] [5,5,5,1] := by
  exact rowSquare_short 7 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg3740 : RowSquare [2,2,2,2,2,2,2,1,1] [6,5,5] := by
  exact rowSquare_short 7 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg3742 : RowSquare [2,2,2,2,2,2,2,1,1] [6,6,3,1] := by
  exact rowSquare_short 7 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg3743 : RowSquare [2,2,2,2,2,2,2,1,1] [6,6,4] := by
  exact rowSquare_short 7 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg3998 : RowSquare [5,5,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [16]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4063 : RowSquare [6,4,2,2,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [16]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4160 : RowSquare [7,3,2,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [16]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4345 : RowSquare [8,2,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [16]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4804 : RowSquare [5,4,4,3,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [17]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4832 : RowSquare [5,5,3,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [17]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4862 : RowSquare [6,4,3,2,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [17]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg4930 : RowSquare [9,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [17]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg5011 : RowSquare [2,2,2,2,2,2,2,2,1,1] [5,5,5,3] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5012 : RowSquare [2,2,2,2,2,2,2,2,1,1] [6,4,4,4] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5013 : RowSquare [2,2,2,2,2,2,2,2,1,1] [6,5,4,3] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5014 : RowSquare [2,2,2,2,2,2,2,2,1,1] [6,5,5,2] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5015 : RowSquare [2,2,2,2,2,2,2,2,1,1] [6,6,4,2] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5016 : RowSquare [2,2,2,2,2,2,2,2,1,1] [6,6,5,1] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5017 : RowSquare [2,2,2,2,2,2,2,2,1,1] [6,6,6] := by
  exact rowSquare_short 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg5672 : RowSquare [6,5,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [18]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg5735 : RowSquare [8,3,2,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [18]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg5757 : RowSquare [9,2,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [18]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg6339 : RowSquare [5,5,4,3,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [19]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg6389 : RowSquare [6,4,4,3,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [19]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg6457 : RowSquare [6,5,3,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [19]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg6502 : RowSquare [10,1,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [19]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg7812 : RowSquare [6,6,2,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [20]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg7998 : RowSquare [9,3,2,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [20]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg8008 : RowSquare [10,2,1,1,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [20]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg8780 : RowSquare [6,6,3,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [21]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg10867 : RowSquare [7,6,2,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [22]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

lemma sg11531 : RowSquare [7,6,3,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_target_transpose (q := [23]) (by decide) (by decide)
    (by decide) (rowSquare_trivial _ (by decide))

end UniversalTensorSquare
end
end

end OAI
