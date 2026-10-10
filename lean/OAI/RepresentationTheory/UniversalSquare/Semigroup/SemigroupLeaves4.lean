import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Semigroup Leaves 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB826 : Equiv.Perm (Fin 10) := Equiv.swap 7 5 * (Equiv.swap 5 4 * (Equiv.swap 4 1 * (Equiv.swap 3 8 * (Equiv.swap 1 9 * (Equiv.swap 1 0 * (Equiv.swap 0 2))))))
def sgT826 : Equiv.Perm (Fin 10) := Equiv.swap 3 6 * (Equiv.swap 6 0 * (Equiv.swap 0 4 * (Equiv.swap 4 8 * (Equiv.swap 3 7 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 0 5)))))))
def sgFlag826 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(5,0,2),(3,0,3),(1,1,0),(4,1,0),(6,1,1),(1,2,0),(7,3,0)}
lemma sgCert826 : solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB826 sgT826) sgFlag826 = 24 := by
  decide +kernel

lemma sg826 : RowSquare [4,2,2,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB826 sgT826 sgFlag826
  change solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB826 sgT826) sgFlag826 ≠ 0
  rw [sgCert826]
  norm_num

def sgB827 : Equiv.Perm (Fin 10) := Equiv.swap 8 1 * (Equiv.swap 1 5 * (Equiv.swap 5 3 * (Equiv.swap 5 6 * (Equiv.swap 1 0 * (Equiv.swap 3 9 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))))
def sgT827 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 3 9 * (Equiv.swap 3 5 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))
def sgFlag827 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(6,0,3),(2,1,0),(3,1,1),(4,1,2),(2,2,0),(5,3,0)}
lemma sgCert827 : solveCompact 10 (.full [7,3]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB827 sgT827) sgFlag827 = -8 := by
  decide +kernel

lemma sg827 : RowSquare [4,2,2,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB827 sgT827 sgFlag827
  change solveCompact 10 (.full [7,3]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB827 sgT827) sgFlag827 ≠ 0
  rw [sgCert827]
  norm_num

def sgB828 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 6 2 * (Equiv.swap 5 0 * (Equiv.swap 1 7 * (Equiv.swap 1 4 * (Equiv.swap 2 9 * (Equiv.swap 1 3 * (Equiv.swap 0 8)))))))
def sgT828 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 0 4 * (Equiv.swap 4 1 * (Equiv.swap 3 8 * (Equiv.swap 2 5 * (Equiv.swap 1 9 * (Equiv.swap 0 6))))))
def sgFlag828 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(4,0,2),(2,1,0),(3,1,1),(3,1,3),(5,2,0),(2,3,0)}
lemma sgCert828 : solveCompact 10 (.full [6,4]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB828 sgT828) sgFlag828 = 5 := by
  decide +kernel

lemma sg828 : RowSquare [4,2,2,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB828 sgT828 sgFlag828
  change solveCompact 10 (.full [6,4]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB828 sgT828) sgFlag828 ≠ 0
  rw [sgCert828]
  norm_num

def sgB829 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 9 * (Equiv.swap 0 1))))
def sgT829 : Equiv.Perm (Fin 10) := Equiv.swap 5 3 * (Equiv.swap 0 1 * (Equiv.swap 5 7 * (Equiv.swap 3 9 * (Equiv.swap 3 4 * (Equiv.swap 0 6 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))))
def sgFlag829 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(4,0,2),(1,0,3),(3,1,0),(2,1,1),(1,2,0),(4,3,0)}
lemma sgCert829 : solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB829 sgT829) sgFlag829 = 10 := by
  decide +kernel

lemma sg829 : RowSquare [4,2,2,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB829 sgT829 sgFlag829
  change solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB829 sgT829) sgFlag829 ≠ 0
  rw [sgCert829]
  norm_num

def sgB832 : Equiv.Perm (Fin 10) := Equiv.swap 4 5 * (Equiv.swap 5 2 * (Equiv.swap 4 6 * (Equiv.swap 3 8 * (Equiv.swap 2 0 * (Equiv.swap 0 9 * (Equiv.swap 0 1))))))
def sgT832 : Equiv.Perm (Fin 10) := Equiv.swap 2 7 * (Equiv.swap 7 3 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 4 6 * (Equiv.swap 3 1 * (Equiv.swap 2 5 * (Equiv.swap 1 9 * (Equiv.swap 0 8))))))))
def sgFlag832 : Finset (ℕ × ℕ × ℕ) := {(6,0,0),(0,0,1),(1,0,1),(0,0,3),(2,1,0),(2,1,1),(3,1,1),(4,1,2),(5,2,0),(1,3,0)}
lemma sgCert832 : solveCompact 10 (.full [7,3]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,3] (Equiv.refl (Fin 10)) sgB832 sgT832) sgFlag832 = 36 := by
  decide +kernel

lemma sg832 : RowSquare [4,2,2,2] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB832 sgT832 sgFlag832
  change solveCompact 10 (.full [7,3]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,3] (Equiv.refl (Fin 10)) sgB832 sgT832) sgFlag832 ≠ 0
  rw [sgCert832]
  norm_num

def sgB833 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 2 7 * (Equiv.swap 4 8 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 0 1)))))
def sgT833 : Equiv.Perm (Fin 10) := Equiv.swap 6 3 * (Equiv.swap 6 1 * (Equiv.swap 5 9 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 7)))))))
def sgFlag833 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(0,0,2),(0,1,0),(3,1,0),(5,1,1),(3,1,3),(4,2,0),(2,3,1)}
lemma sgCert833 : solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB833 sgT833) sgFlag833 = 6 := by
  decide +kernel

lemma sg833 : RowSquare [4,2,2,2] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB833 sgT833 sgFlag833
  change solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB833 sgT833) sgFlag833 ≠ 0
  rw [sgCert833]
  norm_num

def sgB834 : Equiv.Perm (Fin 10) := Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 5 9 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 8)))))))
def sgT834 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 4 2 * (Equiv.swap 2 9 * (Equiv.swap 4 0 * (Equiv.swap 2 5 * (Equiv.swap 0 6)))))
def sgFlag834 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(3,0,1),(0,0,2),(1,1,0),(4,1,1),(2,1,3),(0,2,1),(3,3,0)}
lemma sgCert834 : solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB834 sgT834) sgFlag834 = 32 := by
  decide +kernel

lemma sg834 : RowSquare [4,2,2,2] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB834 sgT834 sgFlag834
  change solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB834 sgT834) sgFlag834 ≠ 0
  rw [sgCert834]
  norm_num

def sgB835 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 5 0 * (Equiv.swap 5 6 * (Equiv.swap 1 4 * (Equiv.swap 2 8 * (Equiv.swap 1 3 * (Equiv.swap 0 7))))))
def sgT835 : Equiv.Perm (Fin 10) := Equiv.swap 2 6 * (Equiv.swap 6 4 * (Equiv.swap 2 1 * (Equiv.swap 4 9 * (Equiv.swap 2 5 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))))
def sgFlag835 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(0,0,1),(3,0,1),(1,1,0),(6,1,1),(2,1,2),(7,1,3),(0,2,0),(5,3,0)}
lemma sgCert835 : solveCompact 10 (.full [8,1,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [8,1,1] (Equiv.refl (Fin 10)) sgB835 sgT835) sgFlag835 = -112 := by
  decide +kernel

lemma sg835 : RowSquare [4,2,2,2] [3,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [8,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB835 sgT835 sgFlag835
  change solveCompact 10 (.full [8,1,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [8,1,1] (Equiv.refl (Fin 10)) sgB835 sgT835) sgFlag835 ≠ 0
  rw [sgCert835]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB836 : Equiv.Perm (Fin 10) := Equiv.swap 4 7 * (Equiv.swap 3 0 * (Equiv.swap 4 6 * (Equiv.swap 3 1 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 8))))))
def sgT836 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 7 0 * (Equiv.swap 5 6 * (Equiv.swap 2 9 * (Equiv.swap 0 8 * (Equiv.swap 2 4 * (Equiv.swap 0 3 * (Equiv.swap 0 1)))))))
def sgFlag836 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(5,0,1),(2,0,3),(0,1,0),(1,1,1),(3,1,2),(4,2,1),(0,3,1)}
lemma sgCert836 : solveCompact 10 (.full [6,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,2,2] (Equiv.refl (Fin 10)) sgB836 sgT836) sgFlag836 = -8 := by
  decide +kernel

lemma sg836 : RowSquare [4,2,2,2] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB836 sgT836 sgFlag836
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,2,2] (Equiv.refl (Fin 10)) sgB836 sgT836) sgFlag836 ≠ 0
  rw [sgCert836]
  norm_num

def sgB837 : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * (Equiv.swap 0 7 * (Equiv.swap 0 6 * (Equiv.swap 0 2 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgT837 : Equiv.Perm (Fin 10) := Equiv.swap 0 5 * (Equiv.swap 5 3 * (Equiv.swap 5 2 * (Equiv.swap 0 1 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 4)))))))
def sgFlag837 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,1),(1,0,2),(2,1,0),(3,1,0),(1,1,1),(2,2,3),(0,3,1)}
lemma sgCert837 : solveCompact 10 (.full [4,4,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,4,2] (Equiv.refl (Fin 10)) sgB837 sgT837) sgFlag837 = -6 := by
  decide +kernel

lemma sg837 : RowSquare [4,2,2,2] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB837 sgT837 sgFlag837
  change solveCompact 10 (.full [4,4,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,4,2] (Equiv.refl (Fin 10)) sgB837 sgT837) sgFlag837 ≠ 0
  rw [sgCert837]
  norm_num

def sgB838 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 1 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 1 9)))))
def sgT838 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 7 1 * (Equiv.swap 6 4 * (Equiv.swap 1 8 * (Equiv.swap 4 0 * (Equiv.swap 0 9 * (Equiv.swap 1 5 * (Equiv.swap 0 2)))))))
def sgFlag838 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(6,0,1),(7,0,2),(1,0,3),(5,1,0),(0,1,1),(1,2,0),(4,2,2),(3,3,0)}
lemma sgCert838 : solveCompact 10 (.full [8,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB838 sgT838) sgFlag838 = -16 := by
  decide +kernel

lemma sg838 : RowSquare [4,3,1,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB838 sgT838 sgFlag838
  change solveCompact 10 (.full [8,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB838 sgT838) sgFlag838 ≠ 0
  rw [sgCert838]
  norm_num

def sgB839 : Equiv.Perm (Fin 10) := Equiv.swap 6 9 * (Equiv.swap 6 0 * (Equiv.swap 1 8 * (Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 7)))))))
def sgT839 : Equiv.Perm (Fin 10) := Equiv.swap 1 3 * (Equiv.swap 3 8 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))
def sgFlag839 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(1,0,3),(3,1,0),(5,1,2),(2,2,0),(6,2,0),(4,3,1)}
lemma sgCert839 : solveCompact 10 (.full [7,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB839 sgT839) sgFlag839 = -3 := by
  decide +kernel

lemma sg839 : RowSquare [4,3,1,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB839 sgT839 sgFlag839
  change solveCompact 10 (.full [7,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB839 sgT839) sgFlag839 ≠ 0
  rw [sgCert839]
  norm_num

def sgB840 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 2 3 * (Equiv.swap 2 7 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 3 5 * (Equiv.swap 2 0 * (Equiv.swap 0 4)))))))
def sgT840 : Equiv.Perm (Fin 10) := Equiv.swap 6 9 * (Equiv.swap 6 2 * (Equiv.swap 4 0 * (Equiv.swap 0 7 * (Equiv.swap 2 8 * (Equiv.swap 0 3)))))
def sgFlag840 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,2),(4,0,3),(5,1,0),(1,1,1),(2,2,0),(1,3,1)}
lemma sgCert840 : solveCompact 10 (.full [6,4]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB840 sgT840) sgFlag840 = -2 := by
  decide +kernel

lemma sg840 : RowSquare [4,3,1,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB840 sgT840 sgFlag840
  change solveCompact 10 (.full [6,4]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB840 sgT840) sgFlag840 ≠ 0
  rw [sgCert840]
  norm_num

def sgB841 : Equiv.Perm (Fin 10) := Equiv.swap 6 1 * (Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 4 5 * (Equiv.swap 0 7 * (Equiv.swap 0 3 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))))
def sgT841 : Equiv.Perm (Fin 10) := Equiv.swap 5 4 * (Equiv.swap 5 2 * (Equiv.swap 5 1 * (Equiv.swap 4 9 * (Equiv.swap 2 7 * (Equiv.swap 1 6 * (Equiv.swap 0 3))))))
def sgFlag841 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(3,0,2),(1,1,0),(2,2,0),(2,2,3),(0,3,0)}
lemma sgCert841 : solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB841 sgT841) sgFlag841 = -2 := by
  decide +kernel

lemma sg841 : RowSquare [4,3,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB841 sgT841 sgFlag841
  change solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB841 sgT841) sgFlag841 ≠ 0
  rw [sgCert841]
  norm_num

def sgB846 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 5 9 * (Equiv.swap 5 7 * (Equiv.swap 1 8 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))))
def sgT846 : Equiv.Perm (Fin 10) := Equiv.swap 1 0 * (Equiv.swap 1 8 * (Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 9)))))))
def sgFlag846 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(0,0,1),(1,0,1),(1,0,2),(1,1,0),(4,1,0),(5,2,2),(0,2,3),(2,3,0)}
lemma sgCert846 : solveCompact 10 (.full [6,2,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB846 sgT846) sgFlag846 = 4 := by
  decide +kernel

lemma sg846 : RowSquare [4,3,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB846 sgT846 sgFlag846
  change solveCompact 10 (.full [6,2,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB846 sgT846) sgFlag846 ≠ 0
  rw [sgCert846]
  norm_num

def sgB847 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 5 * (Equiv.swap 5 4 * (Equiv.swap 4 9 * (Equiv.swap 1 7 * (Equiv.swap 1 3 * (Equiv.swap 0 6))))))
def sgT847 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 9 * (Equiv.swap 2 4 * (Equiv.swap 5 3 * (Equiv.swap 4 8 * (Equiv.swap 3 7 * (Equiv.swap 2 6))))))
def sgFlag847 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(2,0,1),(0,0,2),(3,1,0),(1,1,3),(0,2,1),(2,2,2),(0,3,0)}
lemma sgCert847 : solveCompact 10 (.full [4,3,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB847 sgT847) sgFlag847 = 1 := by
  decide +kernel

lemma sg847 : RowSquare [4,3,1,1,1] [3,3,3,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [4,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB847 sgT847 sgFlag847
  change solveCompact 10 (.full [4,3,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB847 sgT847) sgFlag847 ≠ 0
  rw [sgCert847]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB873 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 6 4 * (Equiv.swap 4 7 * (Equiv.swap 4 0 * (Equiv.swap 0 5 * (Equiv.swap 1 8 * (Equiv.swap 0 2))))))
def sgT873 : Equiv.Perm (Fin 10) := Equiv.swap 6 1 * (Equiv.swap 2 0 * (Equiv.swap 4 8 * (Equiv.swap 1 9 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7))))))
def sgFlag873 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(1,0,1),(6,0,1),(7,0,2),(0,1,0),(2,1,0),(3,1,2),(4,2,0),(0,2,1),(5,2,2)}
lemma sgCert873 : solveCompact 10 (.full [8,2]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,2] (Equiv.refl (Fin 10)) sgB873 sgT873) sgFlag873 = -120 := by
  decide +kernel

lemma sg873 : RowSquare [4,3,3] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB873 sgT873 sgFlag873
  change solveCompact 10 (.full [8,2]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,2] (Equiv.refl (Fin 10)) sgB873 sgT873) sgFlag873 ≠ 0
  rw [sgCert873]
  norm_num

def sgB874 : Equiv.Perm (Fin 10) := Equiv.swap 0 3 * (Equiv.swap 0 8 * (Equiv.swap 0 7 * (Equiv.swap 3 9 * (Equiv.swap 2 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))))
def sgT874 : Equiv.Perm (Fin 10) := Equiv.swap 3 9 * (Equiv.swap 0 8 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 0 6)))))
def sgFlag874 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(6,0,1),(1,0,2),(1,1,1),(5,1,1),(2,1,2),(0,2,0),(4,2,2)}
lemma sgCert874 : solveCompact 10 (.full [7,3]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [7,3] (Equiv.refl (Fin 10)) sgB874 sgT874) sgFlag874 = 45 := by
  decide +kernel

lemma sg874 : RowSquare [4,3,3] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB874 sgT874 sgFlag874
  change solveCompact 10 (.full [7,3]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [7,3] (Equiv.refl (Fin 10)) sgB874 sgT874) sgFlag874 ≠ 0
  rw [sgCert874]
  norm_num

def sgB875 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 6 2 * (Equiv.swap 6 7 * (Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 8 * (Equiv.swap 0 9 * (Equiv.swap 0 1))))))))
def sgT875 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 5 * (Equiv.swap 4 7 * (Equiv.swap 5 8 * (Equiv.swap 4 0 * (Equiv.swap 0 1 * (Equiv.swap 0 3 * (Equiv.swap 1 6 * (Equiv.swap 0 2))))))))
def sgFlag875 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(1,0,1),(2,0,1),(0,1,0),(5,1,2),(2,2,1),(3,2,2)}
lemma sgCert875 : solveCompact 10 (.full [6,4]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [6,4] (Equiv.refl (Fin 10)) sgB875 sgT875) sgFlag875 = -21 := by
  decide +kernel

lemma sg875 : RowSquare [4,3,3] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB875 sgT875 sgFlag875
  change solveCompact 10 (.full [6,4]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [6,4] (Equiv.refl (Fin 10)) sgB875 sgT875) sgFlag875 ≠ 0
  rw [sgCert875]
  norm_num

def sgB876 : Equiv.Perm (Fin 10) := Equiv.swap 4 7 * (Equiv.swap 7 6 * (Equiv.swap 6 2 * (Equiv.swap 4 8 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 0 5 * (Equiv.swap 0 1))))))))
def sgT876 : Equiv.Perm (Fin 10) := Equiv.swap 7 8 * (Equiv.swap 3 4 * (Equiv.swap 4 9 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 5)))))
def sgFlag876 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(3,0,1),(6,0,2),(0,1,0),(5,1,2),(1,2,0),(7,2,1),(4,2,2)}
lemma sgCert876 : solveCompact 10 (.full [8,1,1]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,1,1] (Equiv.refl (Fin 10)) sgB876 sgT876) sgFlag876 = 60 := by
  decide +kernel

lemma sg876 : RowSquare [4,3,3] [3,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [8,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB876 sgT876 sgFlag876
  change solveCompact 10 (.full [8,1,1]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,1,1] (Equiv.refl (Fin 10)) sgB876 sgT876) sgFlag876 ≠ 0
  rw [sgCert876]
  norm_num

def sgB877 : Equiv.Perm (Fin 10) := Equiv.swap 7 9 * (Equiv.swap 7 8 * (Equiv.swap 0 4 * (Equiv.swap 1 6 * (Equiv.swap 1 2 * (Equiv.swap 0 3)))))
def sgT877 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 3 1 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 9)))))
def sgFlag877 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(1,0,1),(0,0,3),(3,1,0),(0,1,1),(4,1,1),(2,1,2),(6,2,0),(2,3,0)}
lemma sgCert877 : solveCompact 10 (.full [7,3]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,3] (Equiv.refl (Fin 10)) sgB877 sgT877) sgFlag877 = 72 := by
  decide +kernel

lemma sg877 : RowSquare [4,4,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB877 sgT877 sgFlag877
  change solveCompact 10 (.full [7,3]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,3] (Equiv.refl (Fin 10)) sgB877 sgT877) sgFlag877 ≠ 0
  rw [sgCert877]
  norm_num

def sgB878 : Equiv.Perm (Fin 10) := Equiv.swap 3 9 * (Equiv.swap 5 7 * (Equiv.swap 1 8 * (Equiv.swap 3 6 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 4))))))
def sgT878 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 6 0 * (Equiv.swap 5 3 * (Equiv.swap 0 1 * (Equiv.swap 3 7 * (Equiv.swap 1 8 * (Equiv.swap 0 4))))))
def sgFlag878 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(0,0,1),(3,1,1),(2,1,2),(5,1,3),(2,2,0),(1,3,0)}
lemma sgCert878 : solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB878 sgT878) sgFlag878 = 24 := by
  decide +kernel

lemma sg878 : RowSquare [4,4,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB878 sgT878 sgFlag878
  change solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB878 sgT878) sgFlag878 ≠ 0
  rw [sgCert878]
  norm_num

def sgB879 : Equiv.Perm (Fin 10) := Equiv.swap 7 8 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 1 9 * (Equiv.swap 0 5)))))
def sgT879 : Equiv.Perm (Fin 10) := Equiv.swap 1 7 * (Equiv.swap 7 4 * (Equiv.swap 4 9 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 8 * (Equiv.swap 0 2))))))
def sgFlag879 : Finset (ℕ × ℕ × ℕ) := {(2,0,1),(0,0,2),(3,0,3),(4,1,0),(1,1,1),(3,1,1),(0,2,0),(1,3,0)}
lemma sgCert879 : solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB879 sgT879) sgFlag879 = -8 := by
  decide +kernel

lemma sg879 : RowSquare [4,4,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB879 sgT879 sgFlag879
  change solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB879 sgT879) sgFlag879 ≠ 0
  rw [sgCert879]
  norm_num

def sgB880 : Equiv.Perm (Fin 10) := Equiv.swap 6 2 * (Equiv.swap 5 0 * (Equiv.swap 2 1 * (Equiv.swap 0 7 * (Equiv.swap 2 4 * (Equiv.swap 1 9 * (Equiv.swap 0 3))))))
def sgT880 : Equiv.Perm (Fin 10) := Equiv.swap 8 2 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 5)))))))
def sgFlag880 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,1),(6,0,2),(5,0,3),(0,1,0),(0,1,1),(1,1,1),(4,2,0),(7,3,1)}
lemma sgCert880 : solveCompact 10 (.full [8,1,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [8,1,1] (Equiv.refl (Fin 10)) sgB880 sgT880) sgFlag880 = -112 := by
  decide +kernel

lemma sg880 : RowSquare [4,4,1,1] [3,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [8,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB880 sgT880 sgFlag880
  change solveCompact 10 (.full [8,1,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [8,1,1] (Equiv.refl (Fin 10)) sgB880 sgT880) sgFlag880 ≠ 0
  rw [sgCert880]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB881 : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * (Equiv.swap 1 8 * (Equiv.swap 1 6 * (Equiv.swap 1 5 * (Equiv.swap 2 9 * (Equiv.swap 1 3 * (Equiv.swap 0 7))))))
def sgT881 : Equiv.Perm (Fin 10) := Equiv.swap 4 0 * (Equiv.swap 3 7 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))
def sgFlag881 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(1,0,1),(6,0,1),(0,1,0),(1,1,0),(3,1,2),(5,1,3),(2,2,1),(0,3,1)}
lemma sgCert881 : solveCompact 10 (.full [7,2,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,2,1] (Equiv.refl (Fin 10)) sgB881 sgT881) sgFlag881 = -4 := by
  decide +kernel

lemma sg881 : RowSquare [4,4,1,1] [3,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [7,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB881 sgT881 sgFlag881
  change solveCompact 10 (.full [7,2,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,2,1] (Equiv.refl (Fin 10)) sgB881 sgT881) sgFlag881 ≠ 0
  rw [sgCert881]
  norm_num

def sgB884 : Equiv.Perm (Fin 10) := Equiv.swap 6 2 * (Equiv.swap 2 0 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 7)))))
def sgT884 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 1 * (Equiv.swap 3 0 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 5)))))
def sgFlag884 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(5,0,1),(2,0,2),(1,1,0),(3,1,0),(4,1,1),(0,2,3),(0,3,1)}
lemma sgCert884 : solveCompact 10 (.full [6,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,2,2] (Equiv.refl (Fin 10)) sgB884 sgT884) sgFlag884 = 6 := by
  decide +kernel

lemma sg884 : RowSquare [4,4,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB884 sgT884 sgFlag884
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,2,2] (Equiv.refl (Fin 10)) sgB884 sgT884) sgFlag884 ≠ 0
  rw [sgCert884]
  norm_num

def sgB885 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 6 0 * (Equiv.swap 4 2 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 8))))))
def sgT885 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 3 7 * (Equiv.swap 2 1 * (Equiv.swap 1 4))))
def sgFlag885 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,2),(1,1,0),(1,1,1),(3,1,1),(4,1,3),(1,2,1),(2,3,1)}
lemma sgCert885 : solveCompact 10 (.full [5,3,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,3,2] (Equiv.refl (Fin 10)) sgB885 sgT885) sgFlag885 = -1 := by
  decide +kernel

lemma sg885 : RowSquare [4,4,1,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB885 sgT885 sgFlag885
  change solveCompact 10 (.full [5,3,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,3,2] (Equiv.refl (Fin 10)) sgB885 sgT885) sgFlag885 ≠ 0
  rw [sgCert885]
  norm_num

def sgB886 : Equiv.Perm (Fin 10) := Equiv.swap 2 0 * (Equiv.swap 0 9 * (Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 0 6))))
def sgT886 : Equiv.Perm (Fin 10) := Equiv.swap 8 7 * (Equiv.swap 7 3 * (Equiv.swap 3 0 * (Equiv.swap 3 5 * (Equiv.swap 3 1 * (Equiv.swap 1 4 * (Equiv.swap 0 9))))))
def sgFlag886 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,1),(3,1,0),(0,1,1),(0,1,2),(2,2,1),(1,3,3)}
lemma sgCert886 : solveCompact 10 (.full [4,4,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,4,2] (Equiv.refl (Fin 10)) sgB886 sgT886) sgFlag886 = -1 := by
  decide +kernel

lemma sg886 : RowSquare [4,4,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB886 sgT886 sgFlag886
  change solveCompact 10 (.full [4,4,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,4,2] (Equiv.refl (Fin 10)) sgB886 sgT886) sgFlag886 ≠ 0
  rw [sgCert886]
  norm_num

def sgB887 : Equiv.Perm (Fin 10) := Equiv.swap 6 1 * (Equiv.swap 6 4 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 2 8 * (Equiv.swap 1 9)))))
def sgT887 : Equiv.Perm (Fin 10) := Equiv.swap 0 3 * (Equiv.swap 3 1 * (Equiv.swap 0 8 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 1 9 * (Equiv.swap 0 4))))))
def sgFlag887 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,2),(0,0,3),(0,1,0),(1,1,1),(1,2,0),(2,3,1)}
lemma sgCert887 : solveCompact 10 (.full [4,2,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,2,2,2] (Equiv.refl (Fin 10)) sgB887 sgT887) sgFlag887 = 1 := by
  decide +kernel

lemma sg887 : RowSquare [4,4,1,1] [4,4,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [4,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB887 sgT887 sgFlag887
  change solveCompact 10 (.full [4,2,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,2,2,2] (Equiv.refl (Fin 10)) sgB887 sgT887) sgFlag887 ≠ 0
  rw [sgCert887]
  norm_num

def sgB889 : Equiv.Perm (Fin 10) := Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 9 * (Equiv.swap 4 5 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 1 0 * (Equiv.swap 0 8)))))))
def sgT889 : Equiv.Perm (Fin 10) := Equiv.swap 2 0 * (Equiv.swap 0 9 * (Equiv.swap 4 5 * (Equiv.swap 0 6 * (Equiv.swap 2 8 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))))
def sgFlag889 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(7,0,2),(0,0,3),(4,0,4),(3,1,0),(0,2,0),(6,3,0),(5,4,0)}
lemma sgCert889 : solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB889 sgT889) sgFlag889 = 1152 := by
  decide +kernel

lemma sg889 : RowSquare [5,1,1,1,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB889 sgT889 sgFlag889
  change solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB889 sgT889) sgFlag889 ≠ 0
  rw [sgCert889]
  norm_num

def sgB890 : Equiv.Perm (Fin 10) := Equiv.swap 1 2 * (Equiv.swap 5 3 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 2 9 * (Equiv.swap 1 6 * (Equiv.swap 0 7))))))
def sgT890 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 8)))))
def sgFlag890 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(4,0,1),(0,0,2),(3,0,3),(2,0,4),(1,1,0),(2,2,0),(6,3,0),(5,4,0)}
lemma sgCert890 : solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB890 sgT890) sgFlag890 = -48 := by
  decide +kernel

lemma sg890 : RowSquare [5,1,1,1,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB890 sgT890 sgFlag890
  change solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB890 sgT890) sgFlag890 ≠ 0
  rw [sgCert890]
  norm_num

def sgB891 : Equiv.Perm (Fin 10) := Equiv.swap 4 6 * (Equiv.swap 6 3 * (Equiv.swap 4 8 * (Equiv.swap 3 9 * (Equiv.swap 1 5 * (Equiv.swap 0 2)))))
def sgT891 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 1 3 * (Equiv.swap 1 4 * (Equiv.swap 4 7 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 8)))))))
def sgFlag891 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(4,0,1),(2,0,2),(0,0,3),(1,0,4),(5,1,0),(0,2,0),(2,3,0),(1,4,0)}
lemma sgCert891 : solveCompact 10 (.full [6,4]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB891 sgT891) sgFlag891 = 144 := by
  decide +kernel

lemma sg891 : RowSquare [5,1,1,1,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB891 sgT891 sgFlag891
  change solveCompact 10 (.full [6,4]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB891 sgT891) sgFlag891 ≠ 0
  rw [sgCert891]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB892 : Equiv.Perm (Fin 10) := Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 4 * (Equiv.swap 4 9 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))))
def sgT892 : Equiv.Perm (Fin 10) := Equiv.swap 8 1 * (Equiv.swap 1 4 * (Equiv.swap 5 7 * (Equiv.swap 4 2 * (Equiv.swap 1 6 * (Equiv.swap 2 9 * (Equiv.swap 1 3))))))
def sgFlag892 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(3,0,2),(4,0,3),(2,0,4),(3,1,0),(4,2,0),(1,3,0),(2,4,0)}
lemma sgCert892 : solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB892 sgT892) sgFlag892 = 1440 := by
  decide +kernel

lemma sg892 : RowSquare [5,1,1,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB892 sgT892 sgFlag892
  change solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB892 sgT892) sgFlag892 ≠ 0
  rw [sgCert892]
  norm_num

def sgB897 : Equiv.Perm (Fin 10) := Equiv.swap 5 4 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 4 9 * (Equiv.swap 0 1 * (Equiv.swap 2 8 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))))
def sgT897 : Equiv.Perm (Fin 10) := Equiv.swap 6 7 * (Equiv.swap 5 9 * (Equiv.swap 4 1 * (Equiv.swap 1 8 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 3))))))
def sgFlag897 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(5,0,0),(0,0,2),(3,0,3),(4,0,4),(2,1,0),(0,2,0),(0,3,1),(1,4,0)}
lemma sgCert897 : solveCompact 10 (.full [6,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB897 sgT897) sgFlag897 = 12 := by
  decide +kernel

lemma sg897 : RowSquare [5,1,1,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB897 sgT897 sgFlag897
  change solveCompact 10 (.full [6,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB897 sgT897) sgFlag897 ≠ 0
  rw [sgCert897]
  norm_num

def sgB898 : Equiv.Perm (Fin 10) := Equiv.swap 2 6 * (Equiv.swap 6 0 * (Equiv.swap 0 9 * (Equiv.swap 1 5 * (Equiv.swap 2 7 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))))
def sgT898 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 5 7 * (Equiv.swap 5 2 * (Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 3))))))
def sgFlag898 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(2,0,1),(1,0,2),(3,0,4),(1,1,3),(0,2,0),(1,3,0),(4,4,0)}
lemma sgCert898 : solveCompact 10 (.full [5,3,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB898 sgT898) sgFlag898 = -36 := by
  decide +kernel

lemma sg898 : RowSquare [5,1,1,1,1,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB898 sgT898 sgFlag898
  change solveCompact 10 (.full [5,3,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB898 sgT898) sgFlag898 ≠ 0
  rw [sgCert898]
  norm_num

def sgB899 : Equiv.Perm (Fin 10) := Equiv.swap 1 5 * (Equiv.swap 1 0 * (Equiv.swap 1 3 * (Equiv.swap 5 4 * (Equiv.swap 4 2 * (Equiv.swap 3 7 * (Equiv.swap 2 9 * (Equiv.swap 1 6 * (Equiv.swap 0 8))))))))
def sgT899 : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * (Equiv.swap 2 9 * (Equiv.swap 4 1 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 1 8 * (Equiv.swap 0 7))))))
def sgFlag899 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(3,0,0),(0,0,1),(1,0,3),(3,0,4),(0,1,0),(2,2,0),(1,3,0),(1,4,2)}
lemma sgCert899 : solveCompact 10 (.full [4,4,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB899 sgT899) sgFlag899 = 36 := by
  decide +kernel

lemma sg899 : RowSquare [5,1,1,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB899 sgT899 sgFlag899
  change solveCompact 10 (.full [4,4,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB899 sgT899) sgFlag899 ≠ 0
  rw [sgCert899]
  norm_num

def sgB902 : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * (Equiv.swap 0 7 * (Equiv.swap 0 6 * (Equiv.swap 4 2 * (Equiv.swap 2 9 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))))
def sgT902 : Equiv.Perm (Fin 10) := Equiv.swap 2 8 * (Equiv.swap 5 7 * (Equiv.swap 4 9 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))))
def sgFlag902 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(1,0,1),(0,0,4),(3,1,0),(0,2,3),(0,3,0),(1,4,2)}
lemma sgCert902 : solveCompact 10 (.full [4,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,2,2,2] (Equiv.refl (Fin 10)) sgB902 sgT902) sgFlag902 = 8 := by
  decide +kernel

lemma sg902 : RowSquare [5,1,1,1,1,1] [4,4,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [4,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB902 sgT902 sgFlag902
  change solveCompact 10 (.full [4,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,2,2,2] (Equiv.refl (Fin 10)) sgB902 sgT902) sgFlag902 ≠ 0
  rw [sgCert902]
  norm_num

def sgB903 : Equiv.Perm (Fin 10) := Equiv.swap 3 9 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgT903 : Equiv.Perm (Fin 10) := Equiv.swap 3 2 * (Equiv.swap 3 1 * (Equiv.swap 3 7 * (Equiv.swap 2 9 * (Equiv.swap 3 6 * (Equiv.swap 2 5 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgFlag903 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(1,0,1),(0,0,3),(0,1,0),(2,2,0),(0,3,4),(0,4,2)}
lemma sgCert903 : solveCompact 10 (.full [3,3,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB903 sgT903) sgFlag903 = 4 := by
  decide +kernel

lemma sg903 : RowSquare [5,1,1,1,1,1] [4,4,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [3,3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB903 sgT903 sgFlag903
  change solveCompact 10 (.full [3,3,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB903 sgT903) sgFlag903 ≠ 0
  rw [sgCert903]
  norm_num

def sgB909 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 5 8 * (Equiv.swap 1 9 * (Equiv.swap 1 4 * (Equiv.swap 0 7))))
def sgT909 : Equiv.Perm (Fin 10) := Equiv.swap 4 5 * (Equiv.swap 4 7 * (Equiv.swap 5 1 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 1 8))))))
def sgFlag909 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(0,1,4),(1,2,2),(0,3,3),(0,4,0)}
lemma sgCert909 : solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB909 sgT909) sgFlag909 = 6 := by
  decide +kernel

lemma sg909 : RowSquare [5,1,1,1,1,1] [5,5] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [2,2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB909 sgT909 sgFlag909
  change solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB909 sgT909) sgFlag909 ≠ 0
  rw [sgCert909]
  norm_num

def sgB915 : Equiv.Perm (Fin 10) := Equiv.swap 1 4 * (Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 3 5 * (Equiv.swap 2 8 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgT915 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 5 3 * (Equiv.swap 5 1 * (Equiv.swap 5 4 * (Equiv.swap 4 6 * (Equiv.swap 3 0 * (Equiv.swap 1 7 * (Equiv.swap 1 2 * (Equiv.swap 0 8))))))))
def sgFlag915 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(3,0,1),(4,0,2),(2,1,0),(1,1,4),(2,2,0),(0,3,0),(1,4,3)}
lemma sgCert915 : solveCompact 10 (.full [5,5]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB915 sgT915) sgFlag915 = -6 := by
  decide +kernel

lemma sg915 : RowSquare [5,2,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB915 sgT915 sgFlag915
  change solveCompact 10 (.full [5,5]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB915 sgT915) sgFlag915 ≠ 0
  rw [sgCert915]
  norm_num

end UniversalTensorSquare
end
end

end OAI
