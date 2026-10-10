import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains

namespace OAI

/-! Small Contracts 13 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def smallB13_36 : Equiv.Perm (Fin 13) := Equiv.swap 7 6 * (Equiv.swap 7 3 * (Equiv.swap 1 11 * (Equiv.swap 7 9 * (Equiv.swap 6 5 * (Equiv.swap 5 2 * (Equiv.swap 3 10 * (Equiv.swap 2 12 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))))
def smallT13_36 : Equiv.Perm (Fin 13) := Equiv.swap 2 9 * (Equiv.swap 9 11 * (Equiv.swap 8 12 * (Equiv.swap 2 10 * (Equiv.swap 3 1 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))))
def smallFlag13_36 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(0,1,0),(0,1,2),(0,1,3),(1,1,3),(1,2,1),(0,2,2),(0,3,1),(1,3,2)}
lemma smallCert13_36 : solveCompact 13 (.full [3,2,2,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_36 smallT13_36) smallFlag13_36 = -7 := by
  decide +kernel

lemma smallSupport13_36 : RowSquare [4,4,3,2] [8,4,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [3,2,2,2,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_36 smallT13_36 smallFlag13_36
  change solveCompact 13 (.full [3,2,2,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_36 smallT13_36) smallFlag13_36 ≠ 0
  rw [smallCert13_36]
  norm_num

def smallB13_37 : Equiv.Perm (Fin 13) := Equiv.swap 10 8 * (Equiv.swap 10 7 * (Equiv.swap 7 4 * (Equiv.swap 8 12 * (Equiv.swap 7 1 * (Equiv.swap 4 11 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 9 * (Equiv.swap 0 5)))))))))
def smallT13_37 : Equiv.Perm (Fin 13) := Equiv.swap 1 10 * (Equiv.swap 10 7 * (Equiv.swap 7 5 * (Equiv.swap 7 4 * (Equiv.swap 5 0 * (Equiv.swap 5 6 * (Equiv.swap 4 8 * (Equiv.swap 0 12 * (Equiv.swap 1 11 * (Equiv.swap 1 2 * (Equiv.swap 0 3))))))))))
def smallFlag13_37 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(0,1,0),(2,1,1),(1,1,2),(0,2,2),(0,2,3),(0,3,0),(1,3,1)}
lemma smallCert13_37 : solveCompact 13 (.full [3,2,2,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_37 smallT13_37) smallFlag13_37 = -4 := by
  decide +kernel

lemma smallSupport13_37 : RowSquare [4,4,3,2] [9,3,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [3,2,2,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_37 smallT13_37 smallFlag13_37
  change solveCompact 13 (.full [3,2,2,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_37 smallT13_37) smallFlag13_37 ≠ 0
  rw [smallCert13_37]
  norm_num

def smallB13_38 : Equiv.Perm (Fin 13) := Equiv.swap 3 6 * (Equiv.swap 3 1 * (Equiv.swap 1 2 * (Equiv.swap 6 12 * (Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 3 10 * (Equiv.swap 2 11 * (Equiv.swap 1 9 * (Equiv.swap 0 8)))))))))
def smallT13_38 : Equiv.Perm (Fin 13) := Equiv.swap 1 2 * (Equiv.swap 1 10 * (Equiv.swap 4 12 * (Equiv.swap 4 8 * (Equiv.swap 4 5 * (Equiv.swap 2 11 * (Equiv.swap 2 3 * (Equiv.swap 1 9)))))))
def smallFlag13_38 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,0,2),(0,1,1),(0,1,2),(1,1,3),(0,2,0),(2,2,1),(0,3,2),(0,3,3)}
lemma smallCert13_38 : solveCompact 13 (.full [3,2,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_38 smallT13_38) smallFlag13_38 = -12 := by
  decide +kernel

lemma smallSupport13_38 : RowSquare [4,4,3,2] [10,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [3,2,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_38 smallT13_38 smallFlag13_38
  change solveCompact 13 (.full [3,2,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_38 smallT13_38) smallFlag13_38 ≠ 0
  rw [smallCert13_38]
  norm_num

def smallB13_39 : Equiv.Perm (Fin 13) := Equiv.swap 0 12 * (Equiv.swap 7 5 * (Equiv.swap 7 3 * (Equiv.swap 5 4 * (Equiv.swap 4 10 * (Equiv.swap 3 9 * (Equiv.swap 0 11 * (Equiv.swap 0 1)))))))
def smallT13_39 : Equiv.Perm (Fin 13) := Equiv.swap 10 4 * (Equiv.swap 10 3 * (Equiv.swap 3 2 * (Equiv.swap 2 11 * (Equiv.swap 2 8 * (Equiv.swap 3 9 * (Equiv.swap 4 1 * (Equiv.swap 3 5 * (Equiv.swap 2 7 * (Equiv.swap 1 12)))))))))
def smallFlag13_39 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,0,2),(0,1,0),(2,1,1),(0,2,2),(0,2,3),(0,3,1),(0,3,3)}
lemma smallCert13_39 : solveCompact 13 (.full [3,1,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,1,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_39 smallT13_39) smallFlag13_39 = 14 := by
  decide +kernel

lemma smallSupport13_39 : RowSquare [4,4,3,2] [11,1,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [3,1,1,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_39 smallT13_39 smallFlag13_39
  change solveCompact 13 (.full [3,1,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,1,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_39 smallT13_39) smallFlag13_39 ≠ 0
  rw [smallCert13_39]
  norm_num

end UniversalTensorSquare
end
end

end OAI
