import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB551 : Equiv.Perm (Fin 9) := Equiv.swap 6 2 * (Equiv.swap 4 8 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 5))))))
def sgT551 : Equiv.Perm (Fin 9) := Equiv.swap 3 1 * (Equiv.swap 1 0 * (Equiv.swap 2 7 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 8))))))
def sgFlag551 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(3,0,1),(1,0,2),(2,0,3),(0,1,0),(2,1,0),(0,1,1),(4,2,1),(1,3,0)}
lemma sgCert551 : solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB551 sgT551) sgFlag551 = -3 := by
  decide +kernel

lemma sg551 : RowSquare [4,2,2,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB551 sgT551 sgFlag551
  change solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB551 sgT551) sgFlag551 ≠ 0
  rw [sgCert551]
  norm_num

def sgB552 : Equiv.Perm (Fin 9) := Equiv.swap 0 2 * (Equiv.swap 0 1 * (Equiv.swap 1 7 * (Equiv.swap 2 8 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))))
def sgT552 : Equiv.Perm (Fin 9) := Equiv.swap 1 5 * (Equiv.swap 5 8 * (Equiv.swap 5 4 * (Equiv.swap 4 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgFlag552 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(0,1,1),(4,1,1),(0,1,2),(2,2,0),(3,3,3)}
lemma sgCert552 : solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB552 sgT552) sgFlag552 = -1 := by
  decide +kernel

lemma sg552 : RowSquare [4,2,2,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB552 sgT552 sgFlag552
  change solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB552 sgT552) sgFlag552 ≠ 0
  rw [sgCert552]
  norm_num

def sgB553 : Equiv.Perm (Fin 9) := Equiv.swap 7 0 * (Equiv.swap 4 1 * (Equiv.swap 1 2 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 8)))))
def sgT553 : Equiv.Perm (Fin 9) := Equiv.swap 1 3 * (Equiv.swap 1 7 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 1 6)))))
def sgFlag553 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(0,1,0),(3,1,0),(2,1,3),(1,2,1),(2,3,2)}
lemma sgCert553 : solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB553 sgT553) sgFlag553 = 5 := by
  decide +kernel

lemma sg553 : RowSquare [4,2,2,1] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB553 sgT553 sgFlag553
  change solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB553 sgT553) sgFlag553 ≠ 0
  rw [sgCert553]
  norm_num

def sgB559 : Equiv.Perm (Fin 9) := Equiv.swap 0 4 * (Equiv.swap 5 3 * (Equiv.swap 4 2 * (Equiv.swap 3 8 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 6))))))
def sgT559 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 5 0 * (Equiv.swap 1 8 * (Equiv.swap 1 4 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))
def sgFlag559 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(1,0,2),(1,1,0),(0,1,1),(0,1,3),(2,2,1),(1,3,0)}
lemma sgCert559 : solveCompact 9 (.full [3,2,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [3,2,2,2] (Equiv.refl (Fin 9)) sgB559 sgT559) sgFlag559 = 12 := by
  decide +kernel

lemma sg559 : RowSquare [4,2,2,1] [4,4,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [3,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB559 sgT559 sgFlag559
  change solveCompact 9 (.full [3,2,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [3,2,2,2] (Equiv.refl (Fin 9)) sgB559 sgT559) sgFlag559 ≠ 0
  rw [sgCert559]
  norm_num

def sgB561 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 2 4 * (Equiv.swap 4 0 * (Equiv.swap 1 6 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))))
def sgT561 : Equiv.Perm (Fin 9) := Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 8))))
def sgFlag561 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(0,0,1),(6,0,2),(2,1,0),(7,1,1),(5,1,3),(1,2,1),(3,3,0)}
lemma sgCert561 : solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB561 sgT561) sgFlag561 = 28 := by
  decide +kernel

lemma sg561 : RowSquare [4,3,1,1] [2,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [8,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB561 sgT561 sgFlag561
  change solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB561 sgT561) sgFlag561 ≠ 0
  rw [sgCert561]
  norm_num

def sgB562 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 1 5 * (Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 1 4)))))
def sgT562 : Equiv.Perm (Fin 9) := Equiv.swap 3 0 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 8 * (Equiv.swap 0 7))))
def sgFlag562 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(5,0,1),(1,0,2),(1,1,0),(4,1,0),(3,1,1),(2,2,3),(6,3,0)}
lemma sgCert562 : solveCompact 9 (.full [7,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,2] (Equiv.refl (Fin 9)) sgB562 sgT562) sgFlag562 = 3 := by
  decide +kernel

lemma sg562 : RowSquare [4,3,1,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB562 sgT562 sgFlag562
  change solveCompact 9 (.full [7,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,2] (Equiv.refl (Fin 9)) sgB562 sgT562) sgFlag562 ≠ 0
  rw [sgCert562]
  norm_num

def sgB563 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 5 * (Equiv.swap 5 2 * (Equiv.swap 2 7 * (Equiv.swap 3 0 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))))
def sgT563 : Equiv.Perm (Fin 9) := Equiv.swap 3 6 * (Equiv.swap 6 1 * (Equiv.swap 3 4 * (Equiv.swap 4 7 * (Equiv.swap 3 5 * (Equiv.swap 1 8 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))))
def sgFlag563 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(3,0,3),(0,1,0),(4,1,2),(2,2,1),(5,3,0)}
lemma sgCert563 : solveCompact 9 (.full [6,3]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [6,3] (Equiv.refl (Fin 9)) sgB563 sgT563) sgFlag563 = 9 := by
  decide +kernel

lemma sg563 : RowSquare [4,3,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB563 sgT563 sgFlag563
  change solveCompact 9 (.full [6,3]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [6,3] (Equiv.refl (Fin 9)) sgB563 sgT563) sgFlag563 ≠ 0
  rw [sgCert563]
  norm_num

def sgB564 : Equiv.Perm (Fin 9) := Equiv.swap 5 8 * (Equiv.swap 3 2 * (Equiv.swap 3 0 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 4)))))
def sgT564 : Equiv.Perm (Fin 9) := Equiv.swap 5 1 * (Equiv.swap 3 4 * (Equiv.swap 1 8 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgFlag564 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(3,0,2),(0,0,3),(1,1,0),(2,1,1),(3,2,0),(4,3,0)}
lemma sgCert564 : solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB564 sgT564) sgFlag564 = 7 := by
  decide +kernel

lemma sg564 : RowSquare [4,3,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB564 sgT564 sgFlag564
  change solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB564 sgT564) sgFlag564 ≠ 0
  rw [sgCert564]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB565 : Equiv.Perm (Fin 9) := Equiv.swap 1 0 * (Equiv.swap 0 8 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))
def sgT565 : Equiv.Perm (Fin 9) := Equiv.swap 3 6 * (Equiv.swap 6 5 * (Equiv.swap 5 4 * (Equiv.swap 4 8 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 7)))))))
def sgFlag565 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(3,0,1),(6,1,0),(4,1,2),(0,1,3),(1,2,1),(2,3,1)}
lemma sgCert565 : solveCompact 9 (.full [7,1,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,1,1] (Equiv.refl (Fin 9)) sgB565 sgT565) sgFlag565 = 20 := by
  decide +kernel

lemma sg565 : RowSquare [4,3,1,1] [3,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [7,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB565 sgT565 sgFlag565
  change solveCompact 9 (.full [7,1,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,1,1] (Equiv.refl (Fin 9)) sgB565 sgT565) sgFlag565 ≠ 0
  rw [sgCert565]
  norm_num

def sgB569 : Equiv.Perm (Fin 9) := Equiv.swap 0 3 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 5 * (Equiv.swap 0 7)))))
def sgT569 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * (Equiv.swap 0 2 * (Equiv.swap 1 7 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 5)))))
def sgFlag569 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,0,2),(2,1,0),(4,1,1),(0,1,3),(1,2,1),(3,3,0)}
lemma sgCert569 : solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB569 sgT569) sgFlag569 = 10 := by
  decide +kernel

lemma sg569 : RowSquare [4,3,1,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB569 sgT569 sgFlag569
  change solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB569 sgT569) sgFlag569 ≠ 0
  rw [sgCert569]
  norm_num

def sgB570 : Equiv.Perm (Fin 9) := Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 8))))
def sgT570 : Equiv.Perm (Fin 9) := Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 0 6))))
def sgFlag570 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,1),(3,1,0),(1,1,2),(0,1,3),(0,2,1),(2,3,1)}
lemma sgCert570 : solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB570 sgT570) sgFlag570 = -1 := by
  decide +kernel

lemma sg570 : RowSquare [4,3,1,1] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB570 sgT570 sgFlag570
  change solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB570 sgT570) sgFlag570 ≠ 0
  rw [sgCert570]
  norm_num

def sgB575 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))))
def sgT575 : Equiv.Perm (Fin 9) := Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 0 8 * (Equiv.swap 3 6 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 4))))))
def sgFlag575 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(0,1,0),(0,1,1),(1,2,0),(1,3,3)}
lemma sgCert575 : solveCompact 9 (.full [3,2,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [3,2,2,2] (Equiv.refl (Fin 9)) sgB575 sgT575) sgFlag575 = 2 := by
  decide +kernel

lemma sg575 : RowSquare [4,3,1,1] [4,4,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [3,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB575 sgT575 sgFlag575
  change solveCompact 9 (.full [3,2,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [3,2,2,2] (Equiv.refl (Fin 9)) sgB575 sgT575) sgFlag575 ≠ 0
  rw [sgCert575]
  norm_num

def sgB577 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 0 8 * (Equiv.swap 0 1))))))
def sgT577 : Equiv.Perm (Fin 9) := Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 0 7 * (Equiv.swap 0 1))))
def sgFlag577 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,1),(1,0,2),(2,0,2),(0,1,0),(4,1,1),(5,2,0),(6,2,1)}
lemma sgCert577 : solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB577 sgT577) sgFlag577 = 30 := by
  decide +kernel

lemma sg577 : RowSquare [4,3,2] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB577 sgT577 sgFlag577
  change solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB577 sgT577) sgFlag577 ≠ 0
  rw [sgCert577]
  norm_num

def sgB578 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 6 * (Equiv.swap 0 5))))
def sgT578 : Equiv.Perm (Fin 9) := Equiv.swap 3 5 * (Equiv.swap 5 1 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 0 8 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgFlag578 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(2,0,2),(2,1,1),(3,1,1),(1,1,2),(1,2,0),(3,2,0)}
lemma sgCert578 : solveCompact 9 (.full [5,4]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [5,4] (Equiv.refl (Fin 9)) sgB578 sgT578) sgFlag578 = 11 := by
  decide +kernel

lemma sg578 : RowSquare [4,3,2] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,2,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB578 sgT578 sgFlag578
  change solveCompact 9 (.full [5,4]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [5,4] (Equiv.refl (Fin 9)) sgB578 sgT578) sgFlag578 ≠ 0
  rw [sgCert578]
  norm_num

def sgB579 : Equiv.Perm (Fin 9) := Equiv.swap 6 4 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 3))))))
def sgT579 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))
def sgFlag579 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(1,0,1),(4,0,1),(0,1,0),(1,1,1),(2,1,1),(2,1,2),(3,2,0)}
lemma sgCert579 : solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB579 sgT579) sgFlag579 = 18 := by
  decide +kernel

lemma sg579 : RowSquare [4,4,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB579 sgT579 sgFlag579
  change solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB579 sgT579) sgFlag579 ≠ 0
  rw [sgCert579]
  norm_num

def sgB580 : Equiv.Perm (Fin 9) := Equiv.swap 5 6 * (Equiv.swap 4 0 * (Equiv.swap 0 7 * (Equiv.swap 0 3 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))
def sgT580 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 6 7 * (Equiv.swap 5 0 * (Equiv.swap 0 2 * (Equiv.swap 2 8 * (Equiv.swap 2 3 * (Equiv.swap 0 4))))))
def sgFlag580 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(4,0,2),(2,1,0),(1,1,1),(3,2,0)}
lemma sgCert580 : solveCompact 9 (.full [5,4]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,4] (Equiv.refl (Fin 9)) sgB580 sgT580) sgFlag580 = 6 := by
  decide +kernel

lemma sg580 : RowSquare [4,4,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB580 sgT580 sgFlag580
  change solveCompact 9 (.full [5,4]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,4] (Equiv.refl (Fin 9)) sgB580 sgT580) sgFlag580 ≠ 0
  rw [sgCert580]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB581 : Equiv.Perm (Fin 9) := Equiv.swap 2 7 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))
def sgT581 : Equiv.Perm (Fin 9) := Equiv.swap 0 4 * (Equiv.swap 0 3 * (Equiv.swap 3 7 * (Equiv.swap 4 8 * (Equiv.swap 3 5 * (Equiv.swap 0 1 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))))
def sgFlag581 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(1,0,1),(2,0,1),(4,0,2),(0,1,0),(3,1,0),(0,1,1),(1,2,1)}
lemma sgCert581 : solveCompact 9 (.full [6,2,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,2,1] (Equiv.refl (Fin 9)) sgB581 sgT581) sgFlag581 = 6 := by
  decide +kernel

lemma sg581 : RowSquare [4,4,1] [3,2,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [6,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB581 sgT581 sgFlag581
  change solveCompact 9 (.full [6,2,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,2,1] (Equiv.refl (Fin 9)) sgB581 sgT581) sgFlag581 ≠ 0
  rw [sgCert581]
  norm_num

def sgB582 : Equiv.Perm (Fin 9) := Equiv.swap 2 4 * (Equiv.swap 5 1 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 6))))))
def sgT582 : Equiv.Perm (Fin 9) := Equiv.swap 1 3 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 1 7))))
def sgFlag582 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(3,0,2),(1,1,0),(4,1,0),(1,1,1),(2,1,1),(0,2,0)}
lemma sgCert582 : solveCompact 9 (.full [5,3,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,3,1] (Equiv.refl (Fin 9)) sgB582 sgT582) sgFlag582 = -2 := by
  decide +kernel

lemma sg582 : RowSquare [4,4,1] [3,2,2,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,3,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB582 sgT582 sgFlag582
  change solveCompact 9 (.full [5,3,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,3,1] (Equiv.refl (Fin 9)) sgB582 sgT582) sgFlag582 ≠ 0
  rw [sgCert582]
  norm_num

def sgB583 : Equiv.Perm (Fin 9) := Equiv.swap 4 8 * (Equiv.swap 4 5 * (Equiv.swap 5 0 * (Equiv.swap 4 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))
def sgT583 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))))
def sgFlag583 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(0,0,1),(1,1,0),(1,1,1),(2,1,1),(3,1,2),(0,2,0)}
lemma sgCert583 : solveCompact 9 (.full [5,2,2]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,2,2] (Equiv.refl (Fin 9)) sgB583 sgT583) sgFlag583 = 4 := by
  decide +kernel

lemma sg583 : RowSquare [4,4,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB583 sgT583 sgFlag583
  change solveCompact 9 (.full [5,2,2]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,2,2] (Equiv.refl (Fin 9)) sgB583 sgT583) sgFlag583 ≠ 0
  rw [sgCert583]
  norm_num

def sgB584 : Equiv.Perm (Fin 9) := Equiv.swap 7 5 * (Equiv.swap 5 4 * (Equiv.swap 5 2 * (Equiv.swap 4 8 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgT584 : Equiv.Perm (Fin 9) := Equiv.swap 2 6 * (Equiv.swap 6 1 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 7)))))
def sgFlag584 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(2,1,0),(1,1,1),(0,2,1)}
lemma sgCert584 : solveCompact 9 (.full [3,3,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,3] (Equiv.refl (Fin 9)) sgB584 sgT584) sgFlag584 = -5 := by
  decide +kernel

lemma sg584 : RowSquare [4,4,1] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB584 sgT584 sgFlag584
  change solveCompact 9 (.full [3,3,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,3] (Equiv.refl (Fin 9)) sgB584 sgT584) sgFlag584 ≠ 0
  rw [sgCert584]
  norm_num

def sgB614 : Equiv.Perm (Fin 9) := Equiv.swap 5 3 * (Equiv.swap 5 4 * (Equiv.swap 4 2 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 7))))))
def sgT614 : Equiv.Perm (Fin 9) := Equiv.swap 6 2 * (Equiv.swap 6 7 * (Equiv.swap 4 5 * (Equiv.swap 2 8)))
def sgFlag614 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(6,0,1),(5,0,2),(2,0,3),(1,1,0),(4,1,0),(1,2,0),(3,3,1)}
lemma sgCert614 : solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 = -4 := by
  decide +kernel

lemma sg614 : RowSquare [5,2,1,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB614 sgT614 sgFlag614
  change solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 ≠ 0
  rw [sgCert614]
  norm_num

def sgB615 : Equiv.Perm (Fin 9) := Equiv.swap 0 5 * (Equiv.swap 0 7 * (Equiv.swap 5 8 * (Equiv.swap 0 6 * (Equiv.swap 2 4 * (Equiv.swap 0 3)))))
def sgT615 : Equiv.Perm (Fin 9) := Equiv.swap 3 4 * (Equiv.swap 4 1 * (Equiv.swap 4 5 * (Equiv.swap 3 0 * (Equiv.swap 1 8 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))
def sgFlag615 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(4,0,1),(5,0,2),(1,0,3),(1,1,0),(2,1,1),(2,2,0),(0,3,0)}
lemma sgCert615 : solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB615 sgT615) sgFlag615 = 13 := by
  decide +kernel

lemma sg615 : RowSquare [5,2,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB615 sgT615 sgFlag615
  change solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB615 sgT615) sgFlag615 ≠ 0
  rw [sgCert615]
  norm_num

def sgB616 : Equiv.Perm (Fin 9) := Equiv.swap 2 7 * (Equiv.swap 5 8 * (Equiv.swap 2 1 * (Equiv.swap 2 4 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 3))))))
def sgT616 : Equiv.Perm (Fin 9) := Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 0 8 * (Equiv.swap 2 7 * (Equiv.swap 0 3 * (Equiv.swap 0 1)))))
def sgFlag616 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(0,0,1),(2,0,2),(1,0,3),(1,1,0),(3,1,0),(2,2,0),(3,3,0)}
lemma sgCert616 : solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB616 sgT616) sgFlag616 = 12 := by
  decide +kernel

lemma sg616 : RowSquare [5,2,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB616 sgT616 sgFlag616
  change solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB616 sgT616) sgFlag616 ≠ 0
  rw [sgCert616]
  norm_num

def sgB621 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 1 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 5)))))
def sgT621 : Equiv.Perm (Fin 9) := Equiv.swap 5 4 * (Equiv.swap 5 6 * (Equiv.swap 4 7 * (Equiv.swap 3 0 * (Equiv.swap 0 8 * (Equiv.swap 0 2 * (Equiv.swap 0 1))))))
def sgFlag621 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(0,0,1),(1,0,1),(3,0,3),(1,1,0),(2,1,0),(1,2,0),(0,3,2)}
lemma sgCert621 : solveCompact 9 (.full [5,2,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,2,2] (Equiv.refl (Fin 9)) sgB621 sgT621) sgFlag621 = -1 := by
  decide +kernel

lemma sg621 : RowSquare [5,2,1,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB621 sgT621 sgFlag621
  change solveCompact 9 (.full [5,2,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,2,2] (Equiv.refl (Fin 9)) sgB621 sgT621) sgFlag621 ≠ 0
  rw [sgCert621]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB636 : Equiv.Perm (Fin 9) := Equiv.swap 5 1 * (Equiv.swap 5 7 * (Equiv.swap 5 6 * (Equiv.swap 1 0 * (Equiv.swap 0 8 * (Equiv.swap 1 4 * (Equiv.swap 0 2))))))
def sgT636 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 8)))))
def sgFlag636 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,1),(2,0,2),(0,1,0),(4,1,1),(1,2,0),(5,2,0)}
lemma sgCert636 : solveCompact 9 (.full [6,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB636 sgT636) sgFlag636 = -6 := by
  decide +kernel

lemma sg636 : RowSquare [5,2,2] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB636 sgT636 sgFlag636
  change solveCompact 9 (.full [6,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB636 sgT636) sgFlag636 ≠ 0
  rw [sgCert636]
  norm_num

def sgB637 : Equiv.Perm (Fin 9) := Equiv.swap 4 2 * (Equiv.swap 5 7 * (Equiv.swap 4 1 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 8)))))
def sgT637 : Equiv.Perm (Fin 9) := Equiv.swap 3 0 * (Equiv.swap 0 8 * (Equiv.swap 3 7 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 0 6)))))
def sgFlag637 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(3,0,1),(0,0,2),(3,0,2),(1,1,0),(0,1,1),(2,2,0)}
lemma sgCert637 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB637 sgT637) sgFlag637 = 24 := by
  decide +kernel

lemma sg637 : RowSquare [5,2,2] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB637 sgT637 sgFlag637
  change solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB637 sgT637) sgFlag637 ≠ 0
  rw [sgCert637]
  norm_num

def sgB640 : Equiv.Perm (Fin 9) := Equiv.swap 5 8 * (Equiv.swap 5 3 * (Equiv.swap 5 1 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))))))
def sgT640 : Equiv.Perm (Fin 9) := Equiv.swap 6 0 * (Equiv.swap 5 7 * (Equiv.swap 0 8 * (Equiv.swap 2 3 * (Equiv.swap 0 4))))
def sgFlag640 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,2),(1,1,0),(0,2,1),(3,2,1)}
lemma sgCert640 : solveCompact 9 (.full [4,3,2]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [4,3,2] (Equiv.refl (Fin 9)) sgB640 sgT640) sgFlag640 = -1 := by
  decide +kernel

lemma sg640 : RowSquare [5,2,2] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB640 sgT640 sgFlag640
  change solveCompact 9 (.full [4,3,2]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [4,3,2] (Equiv.refl (Fin 9)) sgB640 sgT640) sgFlag640 ≠ 0
  rw [sgCert640]
  norm_num

def sgB641 : Equiv.Perm (Fin 9) := Equiv.swap 4 1 * (Equiv.swap 1 8 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 1 5)))))
def sgT641 : Equiv.Perm (Fin 9) := Equiv.swap 5 2 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgFlag641 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,1,2),(0,2,0),(2,2,0)}
lemma sgCert641 : solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB641 sgT641) sgFlag641 = 4 := by
  decide +kernel

lemma sg641 : RowSquare [5,2,2] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB641 sgT641 sgFlag641
  change solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB641 sgT641) sgFlag641 ≠ 0
  rw [sgCert641]
  norm_num

def sgB759 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 0 * (Equiv.swap 4 1 * (Equiv.swap 0 7 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))))
def sgT759 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 6 2 * (Equiv.swap 2 8 * (Equiv.swap 4 7 * (Equiv.swap 2 5))))
def sgFlag759 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(4,0,0),(4,0,1),(0,0,2),(1,1,0),(1,1,1),(2,1,1),(0,2,0)}
lemma sgCert759 : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB759 sgT759) sgFlag759 = -9 := by
  decide +kernel

lemma sg759 : RowSquare [3,2,2,2,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,2,2,2,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB759 sgT759 sgFlag759
  change solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB759 sgT759) sgFlag759 ≠ 0
  rw [sgCert759]
  norm_num

def sgB765 : Equiv.Perm (Fin 10) := Equiv.swap 2 1 * (Equiv.swap 2 7 * (Equiv.swap 5 9 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 8)))))))
def sgT765 : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * (Equiv.swap 0 3 * (Equiv.swap 4 6 * (Equiv.swap 3 9 * (Equiv.swap 0 5 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgFlag765 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(4,0,1),(0,0,2),(0,1,0),(1,1,0),(3,2,0),(5,2,1)}
lemma sgCert765 : solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB765 sgT765) sgFlag765 = 2 := by
  decide +kernel

lemma sg765 : RowSquare [3,3,1,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB765 sgT765 sgFlag765
  change solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB765 sgT765) sgFlag765 ≠ 0
  rw [sgCert765]
  norm_num

def sgB767 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 6 1 * (Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 0 9 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgT767 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 9 * (Equiv.swap 2 6 * (Equiv.swap 2 4 * (Equiv.swap 2 0 * (Equiv.swap 0 3)))))
def sgFlag767 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,1),(3,0,2),(1,1,0),(2,1,1),(0,2,0),(1,2,0)}
lemma sgCert767 : solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB767 sgT767) sgFlag767 = 10 := by
  decide +kernel

lemma sg767 : RowSquare [3,3,1,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB767 sgT767 sgFlag767
  change solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB767 sgT767) sgFlag767 ≠ 0
  rw [sgCert767]
  norm_num

def sgB768 : Equiv.Perm (Fin 10) := Equiv.swap 4 6 * (Equiv.swap 6 2 * (Equiv.swap 6 7 * (Equiv.swap 2 0 * (Equiv.swap 4 1 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 9))))))))
def sgT768 : Equiv.Perm (Fin 10) := Equiv.swap 8 6 * (Equiv.swap 6 9 * (Equiv.swap 0 7 * (Equiv.swap 0 4 * (Equiv.swap 1 2 * (Equiv.swap 0 3)))))
def sgFlag768 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(1,0,1),(0,0,2),(2,1,0),(0,1,1),(1,2,0)}
lemma sgCert768 : solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB768 sgT768) sgFlag768 = -16 := by
  decide +kernel

lemma sg768 : RowSquare [3,3,1,1,1,1] [3,3,3,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB768 sgT768 sgFlag768
  change solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB768 sgT768) sgFlag768 ≠ 0
  rw [sgCert768]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB790 : Equiv.Perm (Fin 10) := Equiv.swap 3 6 * (Equiv.swap 6 4 * (Equiv.swap 5 0 * (Equiv.swap 4 2 * (Equiv.swap 3 7 * (Equiv.swap 2 8 * (Equiv.swap 0 9))))))
def sgT790 : Equiv.Perm (Fin 10) := Equiv.swap 4 3 * (Equiv.swap 4 1 * (Equiv.swap 5 7 * (Equiv.swap 4 6 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 9)))))))
def sgFlag790 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(1,0,1),(2,0,1),(4,0,2),(5,1,0),(1,1,1),(6,1,2),(0,2,0)}
lemma sgCert790 : solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB790 sgT790) sgFlag790 = 24 := by
  decide +kernel

lemma sg790 : RowSquare [3,3,2,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB790 sgT790 sgFlag790
  change solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB790 sgT790) sgFlag790 ≠ 0
  rw [sgCert790]
  norm_num

def sgB791 : Equiv.Perm (Fin 10) := Equiv.swap 3 0 * (Equiv.swap 0 9 * (Equiv.swap 3 1 * (Equiv.swap 0 7 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgT791 : Equiv.Perm (Fin 10) := Equiv.swap 3 2 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))
def sgFlag791 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(2,0,1),(5,0,1),(4,0,2),(1,1,0),(2,1,0),(0,1,1),(1,2,0),(0,2,2)}
lemma sgCert791 : solveCompact 10 (.full [6,4]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB791 sgT791) sgFlag791 = 33 := by
  decide +kernel

lemma sg791 : RowSquare [3,3,2,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB791 sgT791 sgFlag791
  change solveCompact 10 (.full [6,4]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB791 sgT791) sgFlag791 ≠ 0
  rw [sgCert791]
  norm_num

def sgB792 : Equiv.Perm (Fin 10) := Equiv.swap 3 8 * (Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 4 5 * (Equiv.swap 3 7 * (Equiv.swap 0 9 * (Equiv.swap 0 2))))))
def sgT792 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 6 5 * (Equiv.swap 5 0 * (Equiv.swap 3 4 * (Equiv.swap 0 8 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgFlag792 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(4,0,1),(2,0,2),(4,1,0),(2,1,1),(3,1,2),(0,2,0),(3,2,0)}
lemma sgCert792 : solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB792 sgT792) sgFlag792 = -14 := by
  decide +kernel

lemma sg792 : RowSquare [3,3,2,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB792 sgT792 sgFlag792
  change solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB792 sgT792) sgFlag792 ≠ 0
  rw [sgCert792]
  norm_num

def sgB796 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 3 * (Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 1 9 * (Equiv.swap 0 8))))))
def sgT796 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 6 4 * (Equiv.swap 5 2 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 7 * (Equiv.swap 0 8 * (Equiv.swap 0 1)))))))
def sgFlag796 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(4,0,2),(0,1,1),(3,1,1),(4,1,2),(2,2,0)}
lemma sgCert796 : solveCompact 10 (.full [5,5]) (.full [3,3,2,2]) (.full [3,3,2,2])
    (certificateEdges [3,3,2,2] [3,3,2,2] [5,5] (Equiv.refl (Fin 10)) sgB796 sgT796) sgFlag796 = 15 := by
  decide +kernel

lemma sg796 : RowSquare [3,3,2,2] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,2]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB796 sgT796 sgFlag796
  change solveCompact 10 (.full [5,5]) (.full [3,3,2,2]) (.full [3,3,2,2])
    (certificateEdges [3,3,2,2] [3,3,2,2] [5,5] (Equiv.refl (Fin 10)) sgB796 sgT796) sgFlag796 ≠ 0
  rw [sgCert796]
  norm_num

def sgB808 : Equiv.Perm (Fin 10) := Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))))
def sgT808 : Equiv.Perm (Fin 10) := Equiv.swap 5 3 * (Equiv.swap 5 7 * (Equiv.swap 3 8 * (Equiv.swap 3 1 * (Equiv.swap 2 6 * (Equiv.swap 1 4)))))
def sgFlag808 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(2,0,1),(5,0,1),(2,0,2),(3,0,3),(1,1,0),(4,1,0),(0,2,0),(1,3,0)}
lemma sgCert808 : solveCompact 10 (.full [6,4]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB808 sgT808) sgFlag808 = 216 := by
  decide +kernel

lemma sg808 : RowSquare [4,2,1,1,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB808 sgT808 sgFlag808
  change solveCompact 10 (.full [6,4]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB808 sgT808) sgFlag808 ≠ 0
  rw [sgCert808]
  norm_num

def sgB809 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 5 9 * (Equiv.swap 2 7 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgT809 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 6 0 * (Equiv.swap 5 1 * (Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 1 4 * (Equiv.swap 0 7)))))))
def sgFlag809 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(4,0,0),(0,0,1),(1,0,2),(2,0,3),(1,1,0),(4,1,0),(3,2,0),(2,3,0)}
lemma sgCert809 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB809 sgT809) sgFlag809 = -40 := by
  decide +kernel

lemma sg809 : RowSquare [4,2,1,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB809 sgT809 sgFlag809
  change solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB809 sgT809) sgFlag809 ≠ 0
  rw [sgCert809]
  norm_num

def sgB814 : Equiv.Perm (Fin 10) := Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))
def sgT814 : Equiv.Perm (Fin 10) := Equiv.swap 0 4 * (Equiv.swap 4 7 * (Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 0 6))))
def sgFlag814 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(1,0,2),(4,0,3),(3,1,0),(1,1,1),(2,2,0),(5,3,0)}
lemma sgCert814 : solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB814 sgT814) sgFlag814 = -6 := by
  decide +kernel

lemma sg814 : RowSquare [4,2,1,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB814 sgT814 sgFlag814
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB814 sgT814) sgFlag814 ≠ 0
  rw [sgCert814]
  norm_num

def sgB816 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 0 9 * (Equiv.swap 0 1))))))
def sgT816 : Equiv.Perm (Fin 10) := Equiv.swap 7 8 * (Equiv.swap 3 1 * (Equiv.swap 1 9 * (Equiv.swap 3 5 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgFlag816 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(2,0,1),(0,0,2),(1,0,3),(0,1,0),(1,1,0),(2,2,0),(1,3,1)}
lemma sgCert816 : solveCompact 10 (.full [4,4,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB816 sgT816) sgFlag816 = 4 := by
  decide +kernel

lemma sg816 : RowSquare [4,2,1,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB816 sgT816 sgFlag816
  change solveCompact 10 (.full [4,4,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB816 sgT816) sgFlag816 ≠ 0
  rw [sgCert816]
  norm_num

end UniversalTensorSquare
end
end

end OAI
