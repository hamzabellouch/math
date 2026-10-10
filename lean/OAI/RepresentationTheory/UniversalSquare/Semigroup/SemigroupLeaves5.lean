import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB922 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 9 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))))
def sgT922 : Equiv.Perm (Fin 10) := Equiv.swap 5 0 * (Equiv.swap 4 2 * (Equiv.swap 5 7 * (Equiv.swap 4 6 * (Equiv.swap 0 1 * (Equiv.swap 2 9 * (Equiv.swap 1 8 * (Equiv.swap 0 3)))))))
def sgFlag922 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,1),(0,0,3),(0,1,0),(2,1,0),(1,2,4),(1,3,2),(2,4,0)}
lemma sgCert922 : solveCompact 10 (.full [4,4,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB922 sgT922) sgFlag922 = 4 := by
  decide +kernel

lemma sg922 : RowSquare [5,2,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB922 sgT922 sgFlag922
  change solveCompact 10 (.full [4,4,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB922 sgT922) sgFlag922 ≠ 0
  rw [sgCert922]
  norm_num

def sgB932 : Equiv.Perm (Fin 10) := Equiv.swap 3 7 * (Equiv.swap 7 1 * (Equiv.swap 3 2 * (Equiv.swap 3 6 * (Equiv.swap 1 9 * (Equiv.swap 3 5 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))))))
def sgT932 : Equiv.Perm (Fin 10) := Equiv.swap 4 6 * (Equiv.swap 6 0 * (Equiv.swap 6 1 * (Equiv.swap 1 7 * (Equiv.swap 4 8 * (Equiv.swap 0 2 * (Equiv.swap 2 9 * (Equiv.swap 1 5 * (Equiv.swap 0 3))))))))
def sgFlag932 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,0,1),(1,0,3),(1,1,2),(2,1,4),(1,2,0),(2,3,0),(0,4,0)}
lemma sgCert932 : solveCompact 10 (.full [3,3,2,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB932 sgT932) sgFlag932 = 1 := by
  decide +kernel

lemma sg932 : RowSquare [5,2,1,1,1] [4,4,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [3,3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB932 sgT932 sgFlag932
  change solveCompact 10 (.full [3,3,2,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB932 sgT932) sgFlag932 ≠ 0
  rw [sgCert932]
  norm_num

def sgB939 : Equiv.Perm (Fin 10) := Equiv.swap 1 7 * (Equiv.swap 7 3 * (Equiv.swap 3 9 * (Equiv.swap 1 0 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 8))))))))
def sgT939 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 1 7 * (Equiv.swap 0 9 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))
def sgFlag939 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(1,0,3),(0,1,0),(0,2,1),(1,3,4),(1,4,2)}
lemma sgCert939 : solveCompact 10 (.full [2,2,2,2,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB939 sgT939) sgFlag939 = 2 := by
  decide +kernel

lemma sg939 : RowSquare [5,2,1,1,1] [5,5] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [2,2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB939 sgT939 sgFlag939
  change solveCompact 10 (.full [2,2,2,2,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB939 sgT939) sgFlag939 ≠ 0
  rw [sgCert939]
  norm_num

def sgB940 : Equiv.Perm (Fin 10) := Equiv.swap 6 4 * (Equiv.swap 2 9 * (Equiv.swap 4 8 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 3)))))
def sgT940 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 2 3 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 3 5 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 9)))))))
def sgFlag940 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(6,0,0),(2,0,1),(0,0,2),(7,0,2),(0,1,0),(4,1,3),(3,2,0),(1,2,1),(5,3,0)}
lemma sgCert940 : solveCompact 10 (.full [8,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB940 sgT940) sgFlag940 = 8 := by
  decide +kernel

lemma sg940 : RowSquare [5,2,2,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB940 sgT940 sgFlag940
  change solveCompact 10 (.full [8,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB940 sgT940) sgFlag940 ≠ 0
  rw [sgCert940]
  norm_num

def sgB941 : Equiv.Perm (Fin 10) := Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 1 9 * (Equiv.swap 0 7))))
def sgT941 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 5 9 * (Equiv.swap 5 6 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 2 4)))))
def sgFlag941 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(5,0,1),(3,0,2),(0,0,3),(1,1,0),(6,1,1),(2,2,0),(4,2,2),(2,3,0)}
lemma sgCert941 : solveCompact 10 (.full [7,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB941 sgT941) sgFlag941 = 18 := by
  decide +kernel

lemma sg941 : RowSquare [5,2,2,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB941 sgT941 sgFlag941
  change solveCompact 10 (.full [7,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB941 sgT941) sgFlag941 ≠ 0
  rw [sgCert941]
  norm_num

def sgB942 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 5 0 * (Equiv.swap 1 8 * (Equiv.swap 2 7 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))
def sgT942 : Equiv.Perm (Fin 10) := Equiv.swap 4 5 * (Equiv.swap 5 9 * (Equiv.swap 4 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 8)))))
def sgFlag942 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(1,0,2),(2,0,2),(3,1,0),(2,1,3),(3,2,0),(5,2,1),(1,3,0)}
lemma sgCert942 : solveCompact 10 (.full [6,4]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB942 sgT942) sgFlag942 = 2 := by
  decide +kernel

lemma sg942 : RowSquare [5,2,2,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB942 sgT942 sgFlag942
  change solveCompact 10 (.full [6,4]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB942 sgT942) sgFlag942 ≠ 0
  rw [sgCert942]
  norm_num

def sgB943 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 9 * (Equiv.swap 2 8 * (Equiv.swap 5 3 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))))
def sgT943 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 6 3 * (Equiv.swap 3 2 * (Equiv.swap 3 0 * (Equiv.swap 2 8 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))))
def sgFlag943 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(4,0,2),(4,1,0),(2,1,3),(3,2,0),(0,3,1)}
lemma sgCert943 : solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB943 sgT943) sgFlag943 = 6 := by
  decide +kernel

lemma sg943 : RowSquare [5,2,2,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB943 sgT943 sgFlag943
  change solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB943 sgT943) sgFlag943 ≠ 0
  rw [sgCert943]
  norm_num

def sgB948 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 8 * (Equiv.swap 5 3 * (Equiv.swap 4 0 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))))
def sgT948 : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * (Equiv.swap 0 3 * (Equiv.swap 3 8 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 6))))))
def sgFlag948 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,1),(0,0,2),(1,1,0),(5,1,3),(3,2,0),(1,2,1),(4,3,2)}
lemma sgCert948 : solveCompact 10 (.full [6,2,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB948 sgT948) sgFlag948 = -4 := by
  decide +kernel

lemma sg948 : RowSquare [5,2,2,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB948 sgT948 sgFlag948
  change solveCompact 10 (.full [6,2,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB948 sgT948) sgFlag948 ≠ 0
  rw [sgCert948]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB949 : Equiv.Perm (Fin 10) := Equiv.swap 7 5 * (Equiv.swap 5 9 * (Equiv.swap 5 6 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))
def sgT949 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 5 * (Equiv.swap 0 1 * (Equiv.swap 5 3 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 6))))))))
def sgFlag949 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,0,1),(2,0,2),(2,1,0),(3,1,2),(1,2,0),(4,3,3)}
lemma sgCert949 : solveCompact 10 (.full [5,3,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB949 sgT949) sgFlag949 = 4 := by
  decide +kernel

lemma sg949 : RowSquare [5,2,2,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB949 sgT949 sgFlag949
  change solveCompact 10 (.full [5,3,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB949 sgT949) sgFlag949 ≠ 0
  rw [sgCert949]
  norm_num

def sgB950 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 4 9 * (Equiv.swap 3 6 * (Equiv.swap 0 2 * (Equiv.swap 0 1))))
def sgT950 : Equiv.Perm (Fin 10) := Equiv.swap 5 6 * (Equiv.swap 1 7 * (Equiv.swap 3 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))
def sgFlag950 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(0,0,1),(3,0,1),(2,1,0),(0,1,2),(2,2,0),(1,2,3),(0,3,2)}
lemma sgCert950 : solveCompact 10 (.full [4,4,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB950 sgT950) sgFlag950 = 2 := by
  decide +kernel

lemma sg950 : RowSquare [5,2,2,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB950 sgT950 sgFlag950
  change solveCompact 10 (.full [4,4,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB950 sgT950) sgFlag950 ≠ 0
  rw [sgCert950]
  norm_num

def sgB951 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 5 3 * (Equiv.swap 2 8 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 9 * (Equiv.swap 0 4))))))
def sgT951 : Equiv.Perm (Fin 10) := Equiv.swap 0 7 * (Equiv.swap 7 9 * (Equiv.swap 0 1 * (Equiv.swap 0 6 * (Equiv.swap 0 5 * (Equiv.swap 1 8 * (Equiv.swap 0 3))))))
def sgFlag951 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(0,0,1),(2,0,2),(1,1,0),(2,1,3),(2,2,0),(1,2,2),(1,3,1)}
lemma sgCert951 : solveCompact 10 (.full [4,3,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB951 sgT951) sgFlag951 = 4 := by
  decide +kernel

lemma sg951 : RowSquare [5,2,2,1] [3,3,3,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [4,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB951 sgT951 sgFlag951
  change solveCompact 10 (.full [4,3,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB951 sgT951) sgFlag951 ≠ 0
  rw [sgCert951]
  norm_num

def sgB958 : Equiv.Perm (Fin 10) := Equiv.swap 3 0 * (Equiv.swap 3 7 * (Equiv.swap 0 9 * (Equiv.swap 3 6 * (Equiv.swap 0 4 * (Equiv.swap 1 8 * (Equiv.swap 0 2))))))
def sgT958 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 5 4 * (Equiv.swap 6 8 * (Equiv.swap 5 7 * (Equiv.swap 4 9 * (Equiv.swap 0 3)))))
def sgFlag958 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(5,0,1),(3,0,2),(6,0,3),(1,1,0),(4,1,0),(7,1,1),(2,2,0),(0,3,0)}
lemma sgCert958 : solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB958 sgT958) sgFlag958 = -112 := by
  decide +kernel

lemma sg958 : RowSquare [5,3,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB958 sgT958 sgFlag958
  change solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB958 sgT958) sgFlag958 ≠ 0
  rw [sgCert958]
  norm_num

def sgB959 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 2 6 * (Equiv.swap 4 3 * (Equiv.swap 3 8 * (Equiv.swap 2 0 * (Equiv.swap 0 5 * (Equiv.swap 0 1))))))
def sgT959 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 2 * (Equiv.swap 3 6 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 0 7)))))))
def sgFlag959 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(3,0,2),(5,0,3),(2,1,0),(6,1,0),(2,1,1),(1,2,0),(4,3,0)}
lemma sgCert959 : solveCompact 10 (.full [7,3]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB959 sgT959) sgFlag959 = -4 := by
  decide +kernel

lemma sg959 : RowSquare [5,3,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB959 sgT959 sgFlag959
  change solveCompact 10 (.full [7,3]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB959 sgT959) sgFlag959 ≠ 0
  rw [sgCert959]
  norm_num

def sgB960 : Equiv.Perm (Fin 10) := Equiv.swap 8 7 * (Equiv.swap 7 1 * (Equiv.swap 1 9 * (Equiv.swap 3 4 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))
def sgT960 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 3 5 * (Equiv.swap 5 8 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 0 6 * (Equiv.swap 0 1))))))
def sgFlag960 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(5,0,0),(3,0,1),(1,0,2),(4,0,3),(0,1,0),(2,1,1),(3,2,0),(0,3,0)}
lemma sgCert960 : solveCompact 10 (.full [6,4]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB960 sgT960) sgFlag960 = 4 := by
  decide +kernel

lemma sg960 : RowSquare [5,3,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB960 sgT960 sgFlag960
  change solveCompact 10 (.full [6,4]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB960 sgT960) sgFlag960 ≠ 0
  rw [sgCert960]
  norm_num

def sgB961 : Equiv.Perm (Fin 10) := Equiv.swap 5 3 * (Equiv.swap 5 4 * (Equiv.swap 4 1 * (Equiv.swap 3 8 * (Equiv.swap 1 6 * (Equiv.swap 0 9)))))
def sgT961 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 5 6 * (Equiv.swap 0 1 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))))
def sgFlag961 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(4,0,1),(0,0,3),(1,1,0),(2,1,0),(2,1,1),(4,2,2),(1,3,0)}
lemma sgCert961 : solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB961 sgT961) sgFlag961 = 4 := by
  decide +kernel

lemma sg961 : RowSquare [5,3,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB961 sgT961 sgFlag961
  change solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB961 sgT961) sgFlag961 ≠ 0
  rw [sgCert961]
  norm_num

def sgB964 : Equiv.Perm (Fin 10) := Equiv.swap 0 4 * (Equiv.swap 5 9 * (Equiv.swap 4 2 * (Equiv.swap 2 8 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))
def sgT964 : Equiv.Perm (Fin 10) := Equiv.swap 0 6 * (Equiv.swap 6 5 * (Equiv.swap 6 1 * (Equiv.swap 5 2 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 8))))))
def sgFlag964 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(4,0,2),(2,1,0),(5,1,1),(1,1,3),(1,2,0),(3,3,1)}
lemma sgCert964 : solveCompact 10 (.full [6,2,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB964 sgT964) sgFlag964 = 6 := by
  decide +kernel

lemma sg964 : RowSquare [5,3,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB964 sgT964 sgFlag964
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB964 sgT964) sgFlag964 ≠ 0
  rw [sgCert964]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB975 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 5 2 * (Equiv.swap 4 1 * (Equiv.swap 2 7 * (Equiv.swap 2 3 * (Equiv.swap 1 6)))))
def sgT975 : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * (Equiv.swap 5 8 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 1 9 * (Equiv.swap 0 2)))))
def sgFlag975 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(4,0,0),(0,0,1),(6,0,1),(5,0,2),(1,1,0),(2,1,0),(3,1,1),(0,2,0),(1,2,2)}
lemma sgCert975 : solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB975 sgT975) sgFlag975 = 6 := by
  decide +kernel

lemma sg975 : RowSquare [5,3,2] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB975 sgT975 sgFlag975
  change solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB975 sgT975) sgFlag975 ≠ 0
  rw [sgCert975]
  norm_num

def sgB976 : Equiv.Perm (Fin 10) := Equiv.swap 7 1 * (Equiv.swap 5 9 * (Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgT976 : Equiv.Perm (Fin 10) := Equiv.swap 8 7 * (Equiv.swap 7 1 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 4 9 * (Equiv.swap 1 0 * (Equiv.swap 2 6 * (Equiv.swap 1 3 * (Equiv.swap 0 5))))))))
def sgFlag976 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(1,0,1),(5,0,1),(2,0,2),(3,1,0),(1,1,1),(0,2,0),(2,2,2)}
lemma sgCert976 : solveCompact 10 (.full [6,4]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB976 sgT976) sgFlag976 = 4 := by
  decide +kernel

lemma sg976 : RowSquare [5,3,2] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB976 sgT976 sgFlag976
  change solveCompact 10 (.full [6,4]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB976 sgT976) sgFlag976 ≠ 0
  rw [sgCert976]
  norm_num

def sgB977 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 7 1 * (Equiv.swap 6 9 * (Equiv.swap 1 0 * (Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 0 8 * (Equiv.swap 1 4 * (Equiv.swap 0 2))))))))
def sgT977 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 3 9 * (Equiv.swap 0 4 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 8 * (Equiv.swap 0 5 * (Equiv.swap 0 1)))))))
def sgFlag977 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(2,0,1),(1,0,2),(2,1,0),(0,1,1),(3,1,1),(3,2,0),(4,2,0)}
lemma sgCert977 : solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB977 sgT977) sgFlag977 = 40 := by
  decide +kernel

lemma sg977 : RowSquare [5,3,2] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB977 sgT977 sgFlag977
  change solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB977 sgT977) sgFlag977 ≠ 0
  rw [sgCert977]
  norm_num

def sgB982 : Equiv.Perm (Fin 10) := Equiv.swap 1 8 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 5 * (Equiv.swap 1 7 * (Equiv.swap 0 9)))))))
def sgT982 : Equiv.Perm (Fin 10) := Equiv.swap 1 7 * (Equiv.swap 7 9 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))
def sgFlag982 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(1,0,2),(3,1,0),(1,1,1),(2,1,1),(2,2,0)}
lemma sgCert982 : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 = 99 := by
  decide +kernel

lemma sg982 : RowSquare [5,4,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,2,2,2,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB982 sgT982 sgFlag982
  change solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 ≠ 0
  rw [sgCert982]
  norm_num

def sgB998 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 4 * (Equiv.swap 4 9 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 7)))))
def sgT998 : Equiv.Perm (Fin 10) := Equiv.swap 8 9 * (Equiv.swap 3 7 * (Equiv.swap 3 6 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))))
def sgFlag998 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(7,0,0),(3,0,1),(0,0,2),(1,0,3),(5,0,4),(4,1,0),(0,2,0),(2,3,0),(6,4,0)}
lemma sgCert998 : solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB998 sgT998) sgFlag998 = -288 := by
  decide +kernel

lemma sg998 : RowSquare [6,1,1,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB998 sgT998 sgFlag998
  change solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB998 sgT998) sgFlag998 ≠ 0
  rw [sgCert998]
  norm_num

def sgB999 : Equiv.Perm (Fin 10) := Equiv.swap 6 3 * (Equiv.swap 2 1 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 2 5 * (Equiv.swap 1 7 * (Equiv.swap 0 9))))))
def sgT999 : Equiv.Perm (Fin 10) := Equiv.swap 5 6 * (Equiv.swap 6 1 * (Equiv.swap 5 7 * (Equiv.swap 2 4 * (Equiv.swap 1 8))))
def sgFlag999 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(0,0,1),(6,0,2),(1,0,3),(2,0,4),(1,1,0),(4,2,0),(3,3,0),(2,4,0)}
lemma sgCert999 : solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB999 sgT999) sgFlag999 = -48 := by
  decide +kernel

lemma sg999 : RowSquare [6,1,1,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB999 sgT999 sgFlag999
  change solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB999 sgT999) sgFlag999 ≠ 0
  rw [sgCert999]
  norm_num

def sgB1000 : Equiv.Perm (Fin 10) := Equiv.swap 0 5 * (Equiv.swap 1 3 * (Equiv.swap 5 9 * (Equiv.swap 1 6 * (Equiv.swap 3 8 * (Equiv.swap 1 4 * (Equiv.swap 0 7))))))
def sgT1000 : Equiv.Perm (Fin 10) := Equiv.swap 7 5 * (Equiv.swap 0 2 * (Equiv.swap 5 4 * (Equiv.swap 4 9 * (Equiv.swap 0 6 * (Equiv.swap 2 8 * (Equiv.swap 0 3 * (Equiv.swap 0 1)))))))
def sgFlag1000 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,3),(5,0,5),(3,1,4),(2,2,2),(0,3,0),(3,4,0),(4,5,0)}
lemma sgCert1000 : solveCompact 10 (.full [6,4]) (.full [6,1,1,1,1]) (.full [6,1,1,1,1])
    (certificateEdges [6,1,1,1,1] [6,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1000 sgT1000) sgFlag1000 = 72 := by
  decide +kernel

lemma sg1000 : RowSquare [6,1,1,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [6,1,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1000 sgT1000 sgFlag1000
  change solveCompact 10 (.full [6,4]) (.full [6,1,1,1,1]) (.full [6,1,1,1,1])
    (certificateEdges [6,1,1,1,1] [6,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1000 sgT1000) sgFlag1000 ≠ 0
  rw [sgCert1000]
  norm_num

def sgB1001 : Equiv.Perm (Fin 10) := Equiv.swap 8 2 * (Equiv.swap 2 4 * (Equiv.swap 4 9 * (Equiv.swap 3 6 * (Equiv.swap 2 5 * (Equiv.swap 0 1)))))
def sgT1001 : Equiv.Perm (Fin 10) := Equiv.swap 4 3 * (Equiv.swap 6 7 * (Equiv.swap 3 9 * (Equiv.swap 4 8 * (Equiv.swap 3 1 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 5)))))))
def sgFlag1001 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(0,0,1),(3,0,2),(2,0,3),(4,0,4),(2,1,0),(0,2,0),(1,3,0),(3,4,0)}
lemma sgCert1001 : solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1001 sgT1001) sgFlag1001 = 240 := by
  decide +kernel

lemma sg1001 : RowSquare [6,1,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1001 sgT1001 sgFlag1001
  change solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1001 sgT1001) sgFlag1001 ≠ 0
  rw [sgCert1001]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB1006 : Equiv.Perm (Fin 10) := Equiv.swap 0 6 * (Equiv.swap 6 1 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 5 * (Equiv.swap 1 9 * (Equiv.swap 0 8)))))))
def sgT1006 : Equiv.Perm (Fin 10) := Equiv.swap 1 0 * (Equiv.swap 1 8 * (Equiv.swap 1 7 * (Equiv.swap 1 4 * (Equiv.swap 4 6 * (Equiv.swap 0 9 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))))))
def sgFlag1006 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(1,0,1),(0,0,2),(4,0,3),(5,1,0),(3,2,0),(1,3,4),(0,4,0)}
lemma sgCert1006 : solveCompact 10 (.full [6,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1006 sgT1006) sgFlag1006 = -12 := by
  decide +kernel

lemma sg1006 : RowSquare [6,1,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1006 sgT1006 sgFlag1006
  change solveCompact 10 (.full [6,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1006 sgT1006) sgFlag1006 ≠ 0
  rw [sgCert1006]
  norm_num

def sgB1007 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 5 3 * (Equiv.swap 4 9 * (Equiv.swap 3 7 * (Equiv.swap 2 8))))
def sgT1007 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 4 9 * (Equiv.swap 4 1 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgFlag1007 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(2,0,2),(0,0,3),(3,0,4),(0,1,1),(0,2,0),(2,3,0),(1,4,0)}
lemma sgCert1007 : solveCompact 10 (.full [5,3,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB1007 sgT1007) sgFlag1007 = 20 := by
  decide +kernel

lemma sg1007 : RowSquare [6,1,1,1,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1007 sgT1007 sgFlag1007
  change solveCompact 10 (.full [5,3,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB1007 sgT1007) sgFlag1007 ≠ 0
  rw [sgCert1007]
  norm_num

def sgB1008 : Equiv.Perm (Fin 10) := Equiv.swap 1 2 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))
def sgT1008 : Equiv.Perm (Fin 10) := Equiv.swap 0 4 * (Equiv.swap 6 9 * (Equiv.swap 0 3 * (Equiv.swap 4 8 * (Equiv.swap 3 1 * (Equiv.swap 1 7 * (Equiv.swap 1 2 * (Equiv.swap 0 5)))))))
def sgFlag1008 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,0),(2,0,1),(0,0,2),(1,0,3),(2,1,0),(3,2,0),(1,3,4),(0,4,0)}
lemma sgCert1008 : solveCompact 10 (.full [4,4,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB1008 sgT1008) sgFlag1008 = 4 := by
  decide +kernel

lemma sg1008 : RowSquare [6,1,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1008 sgT1008 sgFlag1008
  change solveCompact 10 (.full [4,4,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB1008 sgT1008) sgFlag1008 ≠ 0
  rw [sgCert1008]
  norm_num

def sgB1015 : Equiv.Perm (Fin 10) := Equiv.swap 6 0 * (Equiv.swap 5 1 * (Equiv.swap 4 8 * (Equiv.swap 1 9 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))
def sgT1015 : Equiv.Perm (Fin 10) := Equiv.swap 7 9 * (Equiv.swap 7 0 * (Equiv.swap 0 8 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 0 5)))))
def sgFlag1015 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,0),(0,0,1),(1,0,4),(1,1,3),(0,2,2),(0,3,0),(2,4,0)}
lemma sgCert1015 : solveCompact 10 (.full [4,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,2,2,2] (Equiv.refl (Fin 10)) sgB1015 sgT1015) sgFlag1015 = 4 := by
  decide +kernel

lemma sg1015 : RowSquare [6,1,1,1,1] [4,4,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [4,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1015 sgT1015 sgFlag1015
  change solveCompact 10 (.full [4,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,2,2,2] (Equiv.refl (Fin 10)) sgB1015 sgT1015) sgFlag1015 ≠ 0
  rw [sgCert1015]
  norm_num

def sgB1016 : Equiv.Perm (Fin 10) := Equiv.swap 3 2 * (Equiv.swap 3 5 * (Equiv.swap 5 0 * (Equiv.swap 2 9 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 0 8))))))
def sgT1016 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 6 3 * (Equiv.swap 5 0 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 0 8)))))))
def sgFlag1016 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,2),(1,0,3),(1,1,1),(1,2,4),(1,3,0),(2,4,0)}
lemma sgCert1016 : solveCompact 10 (.full [3,3,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB1016 sgT1016) sgFlag1016 = 2 := by
  decide +kernel

lemma sg1016 : RowSquare [6,1,1,1,1] [4,4,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [3,3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1016 sgT1016 sgFlag1016
  change solveCompact 10 (.full [3,3,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB1016 sgT1016) sgFlag1016 ≠ 0
  rw [sgCert1016]
  norm_num

def sgB1023 : Equiv.Perm (Fin 10) := Equiv.swap 7 1 * (Equiv.swap 7 0 * (Equiv.swap 0 8 * (Equiv.swap 1 9 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgT1023 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 3 4 * (Equiv.swap 2 7))))
def sgFlag1023 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(1,1,4),(1,2,2),(0,3,3),(1,4,0)}
lemma sgCert1023 : solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB1023 sgT1023) sgFlag1023 = -6 := by
  decide +kernel

lemma sg1023 : RowSquare [6,1,1,1,1] [5,5] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [2,2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1023 sgT1023 sgFlag1023
  change solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB1023 sgT1023) sgFlag1023 ≠ 0
  rw [sgCert1023]
  norm_num

def sgB1032 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6 * (Equiv.swap 2 9 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))))
def sgT1032 : Equiv.Perm (Fin 10) := Equiv.swap 1 3 * (Equiv.swap 3 9 * (Equiv.swap 5 8 * (Equiv.swap 3 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgFlag1032 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(3,0,1),(5,0,1),(3,0,2),(0,0,3),(1,1,0),(2,1,0),(2,2,0),(0,3,0)}
lemma sgCert1032 : solveCompact 10 (.full [6,4]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1032 sgT1032) sgFlag1032 = 16 := by
  decide +kernel

lemma sg1032 : RowSquare [6,2,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1032 sgT1032 sgFlag1032
  change solveCompact 10 (.full [6,4]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1032 sgT1032) sgFlag1032 ≠ 0
  rw [sgCert1032]
  norm_num

def sgB1033 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 1 7 * (Equiv.swap 5 9 * (Equiv.swap 1 2 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 3))))))
def sgT1033 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 4 9 * (Equiv.swap 2 8 * (Equiv.swap 4 6 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 0 * (Equiv.swap 0 3)))))))
def sgFlag1033 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(4,0,0),(1,0,1),(4,0,1),(1,0,2),(3,0,3),(0,1,0),(3,1,0),(0,2,0),(2,3,0)}
lemma sgCert1033 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1033 sgT1033) sgFlag1033 = -12 := by
  decide +kernel

lemma sg1033 : RowSquare [6,2,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1033 sgT1033 sgFlag1033
  change solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1033 sgT1033) sgFlag1033 ≠ 0
  rw [sgCert1033]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB1038 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 5 7 * (Equiv.swap 3 9 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))))
def sgT1038 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 0 8 * (Equiv.swap 2 7 * (Equiv.swap 4 1 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 9 * (Equiv.swap 0 6)))))))
def sgFlag1038 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(0,0,1),(4,0,2),(0,0,3),(1,1,0),(3,2,1),(5,3,0)}
lemma sgCert1038 : solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1038 sgT1038) sgFlag1038 = -2 := by
  decide +kernel

lemma sg1038 : RowSquare [6,2,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1038 sgT1038 sgFlag1038
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1038 sgT1038) sgFlag1038 ≠ 0
  rw [sgCert1038]
  norm_num

def sgB1040 : Equiv.Perm (Fin 10) := Equiv.swap 8 1 * (Equiv.swap 1 5 * (Equiv.swap 5 9 * (Equiv.swap 1 7 * (Equiv.swap 0 6 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))))
def sgT1040 : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * (Equiv.swap 5 8 * (Equiv.swap 5 2 * (Equiv.swap 4 7 * (Equiv.swap 1 9 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))))
def sgFlag1040 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(1,0,1),(2,0,2),(2,1,0),(3,1,3),(0,2,0),(1,3,0)}
lemma sgCert1040 : solveCompact 10 (.full [4,4,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB1040 sgT1040) sgFlag1040 = 1 := by
  decide +kernel

lemma sg1040 : RowSquare [6,2,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1040 sgT1040 sgFlag1040
  change solveCompact 10 (.full [4,4,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB1040 sgT1040) sgFlag1040 ≠ 0
  rw [sgCert1040]
  norm_num

def sgB1063 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 2 1 * (Equiv.swap 2 6 * (Equiv.swap 4 3 * (Equiv.swap 3 9 * (Equiv.swap 2 5 * (Equiv.swap 1 8))))))
def sgT1063 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 3 9 * (Equiv.swap 4 8 * (Equiv.swap 3 0 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgFlag1063 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(3,0,1),(4,0,2),(0,1,0),(5,2,0),(2,2,2)}
lemma sgCert1063 : solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1063 sgT1063) sgFlag1063 = -16 := by
  decide +kernel

lemma sg1063 : RowSquare [6,2,2] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1063 sgT1063 sgFlag1063
  change solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1063 sgT1063) sgFlag1063 ≠ 0
  rw [sgCert1063]
  norm_num

def sgB1064 : Equiv.Perm (Fin 10) := Equiv.swap 5 7 * (Equiv.swap 7 9 * (Equiv.swap 5 8 * (Equiv.swap 0 4 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgT1064 : Equiv.Perm (Fin 10) := Equiv.swap 7 9 * (Equiv.swap 5 8 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 0 3))))
def sgFlag1064 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(0,0,1),(3,0,2),(1,1,0),(2,1,0),(0,2,0),(2,2,2)}
lemma sgCert1064 : solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB1064 sgT1064) sgFlag1064 = -1 := by
  decide +kernel

lemma sg1064 : RowSquare [6,2,2] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1064 sgT1064 sgFlag1064
  change solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB1064 sgT1064) sgFlag1064 ≠ 0
  rw [sgCert1064]
  norm_num

def sgB1065 : Equiv.Perm (Fin 10) := Equiv.swap 3 4 * (Equiv.swap 3 0 * (Equiv.swap 5 9 * (Equiv.swap 4 1 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 8 * (Equiv.swap 0 7)))))))
def sgT1065 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 2 8 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))))
def sgFlag1065 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(3,0,0),(1,0,1),(2,0,2),(0,1,0),(0,1,1),(1,2,0)}
lemma sgCert1065 : solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB1065 sgT1065) sgFlag1065 = -4 := by
  decide +kernel

lemma sg1065 : RowSquare [6,2,2] [3,3,3,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1065 sgT1065 sgFlag1065
  change solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB1065 sgT1065) sgFlag1065 ≠ 0
  rw [sgCert1065]
  norm_num

end UniversalTensorSquare
end
end

end OAI
