import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains

namespace OAI

/-! Small Contracts 13 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def smallB13_20 : Equiv.Perm (Fin 13) := Equiv.swap 9 7 * (Equiv.swap 9 5 * (Equiv.swap 5 10 * (Equiv.swap 7 3 * (Equiv.swap 5 0 * (Equiv.swap 3 12 * (Equiv.swap 2 4 * (Equiv.swap 0 8)))))))
def smallT13_20 : Equiv.Perm (Fin 13) := Equiv.swap 6 9 * (Equiv.swap 9 11 * (Equiv.swap 6 2 * (Equiv.swap 5 8 * (Equiv.swap 4 12 * (Equiv.swap 2 10 * (Equiv.swap 2 3 * (Equiv.swap 1 7)))))))
def smallFlag13_20 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,2),(1,1,0),(0,1,1),(3,2,0),(2,2,2),(0,2,3),(1,3,1),(1,3,3)}
lemma smallCert13_20 : solveCompact 13 (.full [4,3,2,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,2] (Equiv.refl (Fin 13)) smallB13_20 smallT13_20) smallFlag13_20 = 144 := by
  decide +kernel

lemma smallSupport13_20 : RowSquare [4,4,3,2] [5,5,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [4,3,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_20 smallT13_20 smallFlag13_20
  change solveCompact 13 (.full [4,3,2,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,2] (Equiv.refl (Fin 13)) smallB13_20 smallT13_20) smallFlag13_20 ≠ 0
  rw [smallCert13_20]
  norm_num

def smallB13_21 : Equiv.Perm (Fin 13) := Equiv.swap 4 9 * (Equiv.swap 9 7 * (Equiv.swap 7 6 * (Equiv.swap 6 1 * (Equiv.swap 5 3 * (Equiv.swap 4 2 * (Equiv.swap 3 12 * (Equiv.swap 2 10 * (Equiv.swap 1 11))))))))
def smallT13_21 : Equiv.Perm (Fin 13) := Equiv.swap 6 7 * (Equiv.swap 7 8 * (Equiv.swap 7 2 * (Equiv.swap 8 12 * (Equiv.swap 7 0 * (Equiv.swap 6 1 * (Equiv.swap 1 11 * (Equiv.swap 2 10 * (Equiv.swap 0 9 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))))))))
def smallFlag13_21 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(1,0,2),(1,1,0),(2,1,1),(0,1,3),(2,1,3),(1,2,1),(0,2,2),(0,3,1),(0,3,2)}
lemma smallCert13_21 : solveCompact 13 (.full [4,3,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_21 smallT13_21) smallFlag13_21 = -24 := by
  decide +kernel

lemma smallSupport13_21 : RowSquare [4,4,3,2] [6,4,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [4,3,2,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_21 smallT13_21 smallFlag13_21
  change solveCompact 13 (.full [4,3,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_21 smallT13_21) smallFlag13_21 ≠ 0
  rw [smallCert13_21]
  norm_num

def smallB13_22 : Equiv.Perm (Fin 13) := Equiv.swap 7 8 * (Equiv.swap 6 3 * (Equiv.swap 0 9 * (Equiv.swap 4 12 * (Equiv.swap 3 10 * (Equiv.swap 0 5 * (Equiv.swap 1 11 * (Equiv.swap 0 2)))))))
def smallT13_22 : Equiv.Perm (Fin 13) := Equiv.swap 11 2 * (Equiv.swap 2 12 * (Equiv.swap 3 4 * (Equiv.swap 6 5 * (Equiv.swap 5 8 * (Equiv.swap 4 10 * (Equiv.swap 3 1 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 9)))))))))
def smallFlag13_22 : Finset (ℕ × ℕ × ℕ) := {(0,0,1),(2,0,1),(0,0,2),(2,0,3),(0,1,0),(1,1,1),(0,2,1),(3,2,2),(1,2,3),(0,3,0),(1,3,2)}
lemma smallCert13_22 : solveCompact 13 (.full [4,3,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_22 smallT13_22) smallFlag13_22 = 11 := by
  decide +kernel

lemma smallSupport13_22 : RowSquare [4,4,3,2] [7,3,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [4,3,2,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_22 smallT13_22 smallFlag13_22
  change solveCompact 13 (.full [4,3,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_22 smallT13_22) smallFlag13_22 ≠ 0
  rw [smallCert13_22]
  norm_num

def smallB13_23 : Equiv.Perm (Fin 13) := Equiv.swap 7 12 * (Equiv.swap 2 11 * (Equiv.swap 7 10 * (Equiv.swap 7 5 * (Equiv.swap 5 1 * (Equiv.swap 5 3 * (Equiv.swap 1 8 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 1 4 * (Equiv.swap 0 6))))))))))
def smallT13_23 : Equiv.Perm (Fin 13) := Equiv.swap 2 11 * (Equiv.swap 2 8 * (Equiv.swap 8 4 * (Equiv.swap 1 6 * (Equiv.swap 6 12 * (Equiv.swap 4 10 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 7 * (Equiv.swap 0 9)))))))))
def smallFlag13_23 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,2),(2,0,2),(0,1,0),(1,1,3),(0,2,1),(3,2,1),(0,3,0),(2,3,1)}
lemma smallCert13_23 : solveCompact 13 (.full [4,3,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_23 smallT13_23) smallFlag13_23 = 8 := by
  decide +kernel

lemma smallSupport13_23 : RowSquare [4,4,3,2] [8,2,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [4,3,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_23 smallT13_23 smallFlag13_23
  change solveCompact 13 (.full [4,3,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_23 smallT13_23) smallFlag13_23 ≠ 0
  rw [smallCert13_23]
  norm_num

end UniversalTensorSquare
end
end

end OAI
