import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains

namespace OAI

/-! Small Contracts 11 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def smallB11_12 : Equiv.Perm (Fin 11) := Equiv.swap 4 2 * (Equiv.swap 2 10 * (Equiv.swap 4 9 * (Equiv.swap 5 3 * (Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 8))))))))
def smallT11_12 : Equiv.Perm (Fin 11) := Equiv.swap 6 8 * (Equiv.swap 8 1 * (Equiv.swap 1 0 * (Equiv.swap 6 9 * (Equiv.swap 1 7 * (Equiv.swap 2 4 * (Equiv.swap 1 3 * (Equiv.swap 0 10)))))))
def smallFlag11_12 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(1,1,0),(3,1,2),(0,1,3),(0,2,0),(0,2,2),(0,3,0)}
lemma smallCert11_12 : solveCompact 11 (.full [4,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_12 smallT11_12) smallFlag11_12 = -8 := by
  decide +kernel

lemma smallSupport11_12 : RowSquare [4,3,3,1] [8,1,1,1] := by
  apply rowSquare_compact (n := 11) (cs := [4,3,3,1]) (ts := [4,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_12 smallT11_12 smallFlag11_12
  change solveCompact 11 (.full [4,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_12 smallT11_12) smallFlag11_12 ≠ 0
  rw [smallCert11_12]
  norm_num

def smallB11_13 : Equiv.Perm (Fin 11) := Equiv.swap 5 10 * (Equiv.swap 5 9 * (Equiv.swap 3 4 * (Equiv.swap 5 8 * (Equiv.swap 4 7 * (Equiv.swap 3 1 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))))
def smallT11_13 : Equiv.Perm (Fin 11) := Equiv.swap 8 5 * (Equiv.swap 5 10 * (Equiv.swap 6 1 * (Equiv.swap 5 3 * (Equiv.swap 1 0 * (Equiv.swap 3 7 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 0 9))))))))
def smallFlag11_13 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(0,0,2),(1,0,3),(0,1,1),(2,1,2),(0,2,0),(1,2,0),(1,3,1)}
lemma smallCert11_13 : solveCompact 11 (.full [3,3,3,2]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,3,2] (Equiv.refl (Fin 11)) smallB11_13 smallT11_13) smallFlag11_13 = 18 := by
  decide +kernel

lemma smallSupport11_13 : RowSquare [4,3,3,1] [4,4,3] := by
  apply rowSquare_compact (n := 11) (cs := [4,3,3,1]) (ts := [3,3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_13 smallT11_13 smallFlag11_13
  change solveCompact 11 (.full [3,3,3,2]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,3,2] (Equiv.refl (Fin 11)) smallB11_13 smallT11_13) smallFlag11_13 ≠ 0
  rw [smallCert11_13]
  norm_num

def smallB11_14 : Equiv.Perm (Fin 11) := Equiv.swap 8 5 * (Equiv.swap 8 6 * (Equiv.swap 5 3 * (Equiv.swap 6 9 * (Equiv.swap 5 7 * (Equiv.swap 3 0 * (Equiv.swap 3 4 * (Equiv.swap 0 10)))))))
def smallT11_14 : Equiv.Perm (Fin 11) := Equiv.swap 9 5 * (Equiv.swap 0 2 * (Equiv.swap 5 10 * (Equiv.swap 2 8 * (Equiv.swap 2 3 * (Equiv.swap 0 7)))))
def smallFlag11_14 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,3),(0,1,0),(1,1,1),(0,1,2),(2,2,1),(0,2,2),(2,3,0)}
lemma smallCert11_14 : solveCompact 11 (.full [3,3,3,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,3,1,1] (Equiv.refl (Fin 11)) smallB11_14 smallT11_14) smallFlag11_14 = 7 := by
  decide +kernel

lemma smallSupport11_14 : RowSquare [4,3,3,1] [5,3,3] := by
  apply rowSquare_compact (n := 11) (cs := [4,3,3,1]) (ts := [3,3,3,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_14 smallT11_14 smallFlag11_14
  change solveCompact 11 (.full [3,3,3,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,3,1,1] (Equiv.refl (Fin 11)) smallB11_14 smallT11_14) smallFlag11_14 ≠ 0
  rw [smallCert11_14]
  norm_num

def smallB11_15 : Equiv.Perm (Fin 11) := Equiv.swap 3 7 * (Equiv.swap 7 2 * (Equiv.swap 7 8 * (Equiv.swap 3 9 * (Equiv.swap 3 5 * (Equiv.swap 2 10 * (Equiv.swap 0 6))))))
def smallT11_15 : Equiv.Perm (Fin 11) := Equiv.swap 0 10 * (Equiv.swap 0 8 * (Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 1 9 * (Equiv.swap 0 3)))))))
def smallFlag11_15 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(0,0,2),(0,0,3),(1,1,1),(0,1,2),(1,2,0),(2,3,1)}
lemma smallCert11_15 : solveCompact 11 (.full [3,3,2,2,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,2,2,1] (Equiv.refl (Fin 11)) smallB11_15 smallT11_15) smallFlag11_15 = 2 := by
  decide +kernel

lemma smallSupport11_15 : RowSquare [4,3,3,1] [5,4,2] := by
  apply rowSquare_compact (n := 11) (cs := [4,3,3,1]) (ts := [3,3,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_15 smallT11_15 smallFlag11_15
  change solveCompact 11 (.full [3,3,2,2,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,2,2,1] (Equiv.refl (Fin 11)) smallB11_15 smallT11_15) smallFlag11_15 ≠ 0
  rw [smallCert11_15]
  norm_num

end UniversalTensorSquare
end
end

end OAI
