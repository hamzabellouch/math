import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains

namespace OAI

/-! Small Contracts 13 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def smallB13_4 : Equiv.Perm (Fin 13) := Equiv.swap 5 10 * (Equiv.swap 1 3 * (Equiv.swap 5 9 * (Equiv.swap 5 2 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 11)))))))
def smallT13_4 : Equiv.Perm (Fin 13) := Equiv.swap 8 6 * (Equiv.swap 8 7 * (Equiv.swap 8 1 * (Equiv.swap 7 5 * (Equiv.swap 6 2 * (Equiv.swap 5 11 * (Equiv.swap 4 9 * (Equiv.swap 2 12 * (Equiv.swap 1 0 * (Equiv.swap 0 10)))))))))
def smallFlag13_4 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(3,1,1),(0,1,2),(4,1,2),(0,1,3),(2,2,1),(0,2,2),(3,3,0),(0,3,3)}
lemma smallCert13_4 : solveCompact 13 (.full [5,4,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,4,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_4 smallT13_4) smallFlag13_4 = -13 := by
  decide +kernel

lemma smallSupport13_4 : RowSquare [4,4,3,2] [6,2,2,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [5,4,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_4 smallT13_4 smallFlag13_4
  change solveCompact 13 (.full [5,4,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,4,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_4 smallT13_4) smallFlag13_4 ≠ 0
  rw [smallCert13_4]
  norm_num

def smallB13_5 : Equiv.Perm (Fin 13) := Equiv.swap 10 0 * (Equiv.swap 0 11 * (Equiv.swap 0 2 * (Equiv.swap 5 9 * (Equiv.swap 5 6 * (Equiv.swap 2 8 * (Equiv.swap 1 12 * (Equiv.swap 2 4 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))))))
def smallT13_5 : Equiv.Perm (Fin 13) := Equiv.swap 10 4 * (Equiv.swap 10 2 * (Equiv.swap 7 6 * (Equiv.swap 6 9 * (Equiv.swap 4 12 * (Equiv.swap 4 0 * (Equiv.swap 0 1 * (Equiv.swap 2 11 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))))))
def smallFlag13_5 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,2),(3,0,3),(2,1,1),(0,1,2),(0,1,3),(0,2,0),(2,2,0),(1,2,1),(1,3,1),(1,3,2)}
lemma smallCert13_5 : solveCompact 13 (.full [5,3,3,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,3,1,1] (Equiv.refl (Fin 13)) smallB13_5 smallT13_5) smallFlag13_5 = 3 := by
  decide +kernel

lemma smallSupport13_5 : RowSquare [4,4,3,2] [5,3,3,1,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [5,3,3,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_5 smallT13_5 smallFlag13_5
  change solveCompact 13 (.full [5,3,3,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,3,1,1] (Equiv.refl (Fin 13)) smallB13_5 smallT13_5) smallFlag13_5 ≠ 0
  rw [smallCert13_5]
  norm_num

def smallB13_6 : Equiv.Perm (Fin 13) := Equiv.swap 6 4 * (Equiv.swap 6 1 * (Equiv.swap 7 10 * (Equiv.swap 7 0 * (Equiv.swap 6 2 * (Equiv.swap 4 12 * (Equiv.swap 4 5 * (Equiv.swap 2 9 * (Equiv.swap 1 11 * (Equiv.swap 0 8)))))))))
def smallT13_6 : Equiv.Perm (Fin 13) := Equiv.swap 10 11 * (Equiv.swap 7 0 * (Equiv.swap 7 3 * (Equiv.swap 0 2 * (Equiv.swap 2 9 * (Equiv.swap 3 8 * (Equiv.swap 2 4 * (Equiv.swap 0 5)))))))
def smallFlag13_6 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(0,0,2),(1,1,0),(2,1,1),(0,1,2),(4,2,1),(1,2,2),(1,2,3),(3,3,0),(0,3,3)}
lemma smallCert13_6 : solveCompact 13 (.full [5,3,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,2,2,1] (Equiv.refl (Fin 13)) smallB13_6 smallT13_6) smallFlag13_6 = 1 := by
  decide +kernel

lemma smallSupport13_6 : RowSquare [4,4,3,2] [5,4,2,1,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [5,3,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_6 smallT13_6 smallFlag13_6
  change solveCompact 13 (.full [5,3,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,2,2,1] (Equiv.refl (Fin 13)) smallB13_6 smallT13_6) smallFlag13_6 ≠ 0
  rw [smallCert13_6]
  norm_num

def smallB13_7 : Equiv.Perm (Fin 13) := Equiv.swap 10 1 * (Equiv.swap 10 7 * (Equiv.swap 7 8 * (Equiv.swap 8 6 * (Equiv.swap 7 2 * (Equiv.swap 6 5 * (Equiv.swap 5 11 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 0 * (Equiv.swap 0 12))))))))))
def smallT13_7 : Equiv.Perm (Fin 13) := Equiv.swap 6 9 * (Equiv.swap 9 3 * (Equiv.swap 8 7 * (Equiv.swap 7 11 * (Equiv.swap 6 10 * (Equiv.swap 3 2 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 2 12))))))))
def smallFlag13_7 : Finset (ℕ × ℕ × ℕ) := {(0,0,1),(2,0,2),(0,0,3),(1,1,0),(2,1,0),(3,1,0),(1,1,2),(0,2,1),(1,2,3),(4,3,0),(0,3,2)}
lemma smallCert13_7 : solveCompact 13 (.full [5,3,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_7 smallT13_7) smallFlag13_7 = 2 := by
  decide +kernel

lemma smallSupport13_7 : RowSquare [4,4,3,2] [6,3,2,1,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [5,3,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_7 smallT13_7 smallFlag13_7
  change solveCompact 13 (.full [5,3,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_7 smallT13_7) smallFlag13_7 ≠ 0
  rw [smallCert13_7]
  norm_num

end UniversalTensorSquare
end
end

end OAI
