import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB314 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))
def sgT314 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 5)))))
def sgFlag314 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,1),(2,0,2),(0,0,3),(2,1,0),(0,2,0),(4,3,0)}
lemma sgCert314 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB314 sgT314) sgFlag314 = 20 := by
  decide +kernel

lemma sg314 : RowSquare [4,1,1,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB314 sgT314 sgFlag314
  change solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB314 sgT314) sgFlag314 ≠ 0
  rw [sgCert314]
  norm_num

def sgB315 : Equiv.Perm (Fin 8) := Equiv.swap 5 2 * (Equiv.swap 5 6 * (Equiv.swap 2 1 * (Equiv.swap 2 4 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))
def sgT315 : Equiv.Perm (Fin 8) := Equiv.swap 3 7 * (Equiv.swap 3 5 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 0 6))))
def sgFlag315 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,1),(0,0,2),(2,0,3),(1,1,0),(0,2,0),(2,3,0)}
lemma sgCert315 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB315 sgT315) sgFlag315 = 24 := by
  decide +kernel

lemma sg315 : RowSquare [4,1,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB315 sgT315 sgFlag315
  change solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB315 sgT315) sgFlag315 ≠ 0
  rw [sgCert315]
  norm_num

def sgB319 : Equiv.Perm (Fin 8) := Equiv.swap 1 4 * (Equiv.swap 1 0 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))))
def sgT319 : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 0 6))))
def sgFlag319 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(0,0,1),(1,0,3),(1,1,2),(0,2,0),(3,3,0)}
lemma sgCert319 : solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB319 sgT319) sgFlag319 = -2 := by
  decide +kernel

lemma sg319 : RowSquare [4,1,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB319 sgT319 sgFlag319
  change solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB319 sgT319) sgFlag319 ≠ 0
  rw [sgCert319]
  norm_num

def sgB320 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 0 6)))
def sgT320 : Equiv.Perm (Fin 8) := Equiv.swap 3 4 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 0 1))))
def sgFlag320 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,2),(0,0,3),(0,1,1),(2,2,0),(0,3,0)}
lemma sgCert320 : solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB320 sgT320) sgFlag320 = 4 := by
  decide +kernel

lemma sg320 : RowSquare [4,1,1,1,1] [3,3,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB320 sgT320 sgFlag320
  change solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB320 sgT320) sgFlag320 ≠ 0
  rw [sgCert320]
  norm_num

def sgB324 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 2 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))
def sgT324 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 1 7 * (Equiv.swap 0 5)))))
def sgFlag324 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,2),(1,1,0),(0,2,1),(1,3,3)}
lemma sgCert324 : solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB324 sgT324) sgFlag324 = 4 := by
  decide +kernel

lemma sg324 : RowSquare [4,1,1,1,1] [4,4] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB324 sgT324 sgFlag324
  change solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB324 sgT324) sgFlag324 ≠ 0
  rw [sgCert324]
  norm_num

def sgB348 : Equiv.Perm (Fin 8) := Equiv.swap 5 3 * (Equiv.swap 5 6 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 0 * (Equiv.swap 0 7)))))
def sgT348 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 0 1 * (Equiv.swap 0 4 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))
def sgFlag348 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(4,0,1),(2,0,2),(5,1,1),(1,1,2),(0,2,0)}
lemma sgCert348 : solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB348 sgT348) sgFlag348 = 6 := by
  decide +kernel

lemma sg348 : RowSquare [4,2,2] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB348 sgT348 sgFlag348
  change solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB348 sgT348) sgFlag348 ≠ 0
  rw [sgCert348]
  norm_num

def sgB349 : Equiv.Perm (Fin 8) := Equiv.swap 2 6 * (Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 1 0 * (Equiv.swap 0 5))))
def sgT349 : Equiv.Perm (Fin 8) := Equiv.swap 5 3 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgFlag349 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,1),(0,0,2),(1,0,2),(2,1,0),(0,2,0),(3,2,1)}
lemma sgCert349 : solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB349 sgT349) sgFlag349 = -6 := by
  decide +kernel

lemma sg349 : RowSquare [4,2,2] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB349 sgT349 sgFlag349
  change solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB349 sgT349) sgFlag349 ≠ 0
  rw [sgCert349]
  norm_num

def sgB350 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 6 * (Equiv.swap 2 3 * (Equiv.swap 0 1)))
def sgT350 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 4 7 * (Equiv.swap 1 5 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 6))))))
def sgFlag350 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(1,0,2),(3,1,0),(0,2,0),(0,2,2)}
lemma sgCert350 : solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB350 sgT350) sgFlag350 = -5 := by
  decide +kernel

lemma sg350 : RowSquare [4,2,2] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB350 sgT350 sgFlag350
  change solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB350 sgT350) sgFlag350 ≠ 0
  rw [sgCert350]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB352 : Equiv.Perm (Fin 8) := Equiv.swap 4 0 * (Equiv.swap 3 1 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgT352 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 0 1 * (Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 0 4))))
def sgFlag352 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(1,1,0),(0,1,2),(3,2,0),(2,2,2)}
lemma sgCert352 : solveCompact 8 (.full [4,2,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB352 sgT352) sgFlag352 = 4 := by
  decide +kernel

lemma sg352 : RowSquare [4,2,2] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB352 sgT352 sgFlag352
  change solveCompact 8 (.full [4,2,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB352 sgT352) sgFlag352 ≠ 0
  rw [sgCert352]
  norm_num

def sgB353 : Equiv.Perm (Fin 8) := Equiv.swap 3 6 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))
def sgT353 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 1 6 * (Equiv.swap 2 5 * (Equiv.swap 1 3)))
def sgFlag353 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,2),(1,1,0),(0,1,1),(2,2,0),(2,2,1)}
lemma sgCert353 : solveCompact 8 (.full [3,3,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB353 sgT353) sgFlag353 = 1 := by
  decide +kernel

lemma sg353 : RowSquare [4,2,2] [3,3,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB353 sgT353 sgFlag353
  change solveCompact 8 (.full [3,3,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB353 sgT353) sgFlag353 ≠ 0
  rw [sgCert353]
  norm_num

def sgB356 : Equiv.Perm (Fin 8) := Equiv.swap 4 2 * (Equiv.swap 4 5 * (Equiv.swap 0 1 * (Equiv.swap 2 7 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgT356 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 1 5))))
def sgFlag356 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(0,1,0),(3,1,0),(5,1,1),(4,2,0)}
lemma sgCert356 : solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB356 sgT356) sgFlag356 = 12 := by
  decide +kernel

lemma sg356 : RowSquare [4,3,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB356 sgT356 sgFlag356
  change solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB356 sgT356) sgFlag356 ≠ 0
  rw [sgCert356]
  norm_num

def sgB357 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))))
def sgT357 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 6 * (Equiv.swap 0 5 * (Equiv.swap 0 2 * (Equiv.swap 0 1))))))
def sgFlag357 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,1),(4,0,1),(1,0,2),(2,1,0),(0,1,1),(0,2,0)}
lemma sgCert357 : solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB357 sgT357) sgFlag357 = -4 := by
  decide +kernel

lemma sg357 : RowSquare [4,3,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB357 sgT357 sgFlag357
  change solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB357 sgT357) sgFlag357 ≠ 0
  rw [sgCert357]
  norm_num

def sgB358 : Equiv.Perm (Fin 8) := Equiv.swap 2 4 * (Equiv.swap 4 6 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 5))))
def sgT358 : Equiv.Perm (Fin 8) := Equiv.swap 6 7 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 5)))
def sgFlag358 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(3,1,0),(0,1,1),(3,1,2),(0,2,0)}
lemma sgCert358 : solveCompact 8 (.full [4,4]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [4,4] (Equiv.refl (Fin 8)) sgB358 sgT358) sgFlag358 = -2 := by
  decide +kernel

lemma sg358 : RowSquare [4,3,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB358 sgT358 sgFlag358
  change solveCompact 8 (.full [4,4]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [4,4] (Equiv.refl (Fin 8)) sgB358 sgT358) sgFlag358 ≠ 0
  rw [sgCert358]
  norm_num

def sgB371 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))))
def sgT371 : Equiv.Perm (Fin 8) := Equiv.swap 3 1 * (Equiv.swap 4 7 * (Equiv.swap 3 5 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 6)))))
def sgFlag371 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,1),(3,0,2),(0,0,3),(2,1,0),(0,2,0),(5,3,0)}
lemma sgCert371 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB371 sgT371) sgFlag371 = 24 := by
  decide +kernel

lemma sg371 : RowSquare [5,1,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB371 sgT371 sgFlag371
  change solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB371 sgT371) sgFlag371 ≠ 0
  rw [sgCert371]
  norm_num

def sgB372 : Equiv.Perm (Fin 8) := Equiv.swap 5 6 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))
def sgT372 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4)))
def sgFlag372 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,1),(3,0,2),(1,0,3),(4,1,0),(0,2,0),(2,3,0)}
lemma sgCert372 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB372 sgT372) sgFlag372 = 20 := by
  decide +kernel

lemma sg372 : RowSquare [5,1,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB372 sgT372 sgFlag372
  change solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB372 sgT372) sgFlag372 ≠ 0
  rw [sgCert372]
  norm_num

def sgB373 : Equiv.Perm (Fin 8) := Equiv.swap 6 2 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 3))))
def sgT373 : Equiv.Perm (Fin 8) := Equiv.swap 0 6 * (Equiv.swap 0 5 * (Equiv.swap 3 7 * (Equiv.swap 0 4 * (Equiv.swap 0 2))))
def sgFlag373 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(3,0,0),(1,0,1),(0,0,2),(2,0,3),(1,1,0),(0,2,0),(3,3,0)}
lemma sgCert373 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 = 24 := by
  decide +kernel

lemma sg373 : RowSquare [5,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB373 sgT373 sgFlag373
  change solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 ≠ 0
  rw [sgCert373]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB377 : Equiv.Perm (Fin 8) := Equiv.swap 1 4 * (Equiv.swap 4 2 * (Equiv.swap 4 5 * (Equiv.swap 2 7 * (Equiv.swap 2 3 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgT377 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))
def sgFlag377 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,1),(1,0,2),(0,1,0),(1,2,3),(3,3,0)}
lemma sgCert377 : solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB377 sgT377) sgFlag377 = -4 := by
  decide +kernel

lemma sg377 : RowSquare [5,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB377 sgT377 sgFlag377
  change solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB377 sgT377) sgFlag377 ≠ 0
  rw [sgCert377]
  norm_num

def sgB378 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 4))))
def sgT378 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 3 1 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgFlag378 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(2,0,2),(1,1,0),(2,2,0),(1,3,3)}
lemma sgCert378 : solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB378 sgT378) sgFlag378 = 4 := by
  decide +kernel

lemma sg378 : RowSquare [5,1,1,1] [3,3,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB378 sgT378 sgFlag378
  change solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB378 sgT378) sgFlag378 ≠ 0
  rw [sgCert378]
  norm_num

def sgB383 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 1 * (Equiv.swap 1 6 * (Equiv.swap 1 2 * (Equiv.swap 0 5))))))
def sgT383 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 0 2 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))))
def sgFlag383 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,3),(1,1,2),(1,2,0),(1,3,1)}
lemma sgCert383 : solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB383 sgT383) sgFlag383 = 2 := by
  decide +kernel

lemma sg383 : RowSquare [5,1,1,1] [4,4] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB383 sgT383 sgFlag383
  change solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB383 sgT383) sgFlag383 ≠ 0
  rw [sgCert383]
  norm_num

def sgB390 : Equiv.Perm (Fin 8) := Equiv.swap 3 1 * (Equiv.swap 4 0 * (Equiv.swap 3 5 * (Equiv.swap 0 6 * (Equiv.swap 1 7 * (Equiv.swap 0 2)))))
def sgT390 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))
def sgFlag390 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,1),(2,0,2),(1,1,0),(2,2,0)}
lemma sgCert390 : solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB390 sgT390) sgFlag390 = 7 := by
  decide +kernel

lemma sg390 : RowSquare [5,2,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB390 sgT390 sgFlag390
  change solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB390 sgT390) sgFlag390 ≠ 0
  rw [sgCert390]
  norm_num

def sgB394 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 0 6 * (Equiv.swap 0 2))))
def sgT394 : Equiv.Perm (Fin 8) := Equiv.swap 6 5 * (Equiv.swap 5 2 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 3))))
def sgFlag394 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,1),(3,0,2),(0,1,0),(1,1,1),(1,2,0)}
lemma sgCert394 : solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB394 sgT394) sgFlag394 = 4 := by
  decide +kernel

lemma sg394 : RowSquare [5,2,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB394 sgT394 sgFlag394
  change solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB394 sgT394) sgFlag394 ≠ 0
  rw [sgCert394]
  norm_num

def sgB480 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 2 0 * (Equiv.swap 3 5 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgT480 : Equiv.Perm (Fin 9) := Equiv.swap 1 5 * (Equiv.swap 5 2 * (Equiv.swap 1 7 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))))
def sgFlag480 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(2,0,1),(1,1,0),(4,1,1),(3,1,2),(0,2,1)}
lemma sgCert480 : solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB480 sgT480) sgFlag480 = 45 := by
  decide +kernel

lemma sg480 : RowSquare [3,2,2,2] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB480 sgT480 sgFlag480
  change solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB480 sgT480) sgFlag480 ≠ 0
  rw [sgCert480]
  norm_num

def sgB481 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * (Equiv.swap 1 7 * (Equiv.swap 1 4 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 6)))))
def sgT481 : Equiv.Perm (Fin 9) := Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 5)))))
def sgFlag481 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(1,1,0),(3,1,1),(1,1,2),(4,2,0)}
lemma sgCert481 : solveCompact 9 (.full [5,4]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,4] (Equiv.refl (Fin 9)) sgB481 sgT481) sgFlag481 = -12 := by
  decide +kernel

lemma sg481 : RowSquare [3,2,2,2] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB481 sgT481 sgFlag481
  change solveCompact 9 (.full [5,4]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,4] (Equiv.refl (Fin 9)) sgB481 sgT481) sgFlag481 ≠ 0
  rw [sgCert481]
  norm_num

def sgB482 : Equiv.Perm (Fin 9) := Equiv.swap 4 2 * (Equiv.swap 4 7 * (Equiv.swap 2 8 * (Equiv.swap 4 6 * (Equiv.swap 2 5 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))))
def sgT482 : Equiv.Perm (Fin 9) := Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))
def sgFlag482 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(2,0,2),(0,1,0),(4,1,0),(1,1,1),(2,1,1),(1,2,0)}
lemma sgCert482 : solveCompact 9 (.full [5,3,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,3,1] (Equiv.refl (Fin 9)) sgB482 sgT482) sgFlag482 = 4 := by
  decide +kernel

lemma sg482 : RowSquare [3,2,2,2] [3,2,2,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,3,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB482 sgT482 sgFlag482
  change solveCompact 9 (.full [5,3,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,3,1] (Equiv.refl (Fin 9)) sgB482 sgT482) sgFlag482 ≠ 0
  rw [sgCert482]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB483 : Equiv.Perm (Fin 9) := Equiv.swap 7 8 * (Equiv.swap 3 5 * (Equiv.swap 3 1 * (Equiv.swap 1 4 * (Equiv.swap 0 2))))
def sgT483 : Equiv.Perm (Fin 9) := Equiv.swap 6 0 * (Equiv.swap 6 3 * (Equiv.swap 3 1 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 7 * (Equiv.swap 0 8))))))
def sgFlag483 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(1,0,2),(1,1,0),(0,1,1),(3,1,1),(4,2,0)}
lemma sgCert483 : solveCompact 9 (.full [5,2,2]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,2,2] (Equiv.refl (Fin 9)) sgB483 sgT483) sgFlag483 = -2 := by
  decide +kernel

lemma sg483 : RowSquare [3,2,2,2] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB483 sgT483 sgFlag483
  change solveCompact 9 (.full [5,2,2]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,2,2] (Equiv.refl (Fin 9)) sgB483 sgT483) sgFlag483 ≠ 0
  rw [sgCert483]
  norm_num

def sgB484 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 6 2 * (Equiv.swap 5 8 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 0 7 * (Equiv.swap 0 1))))))
def sgT484 : Equiv.Perm (Fin 9) := Equiv.swap 1 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))
def sgFlag484 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,1,0),(1,1,1),(0,1,2),(2,2,1)}
lemma sgCert484 : solveCompact 9 (.full [3,3,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,3] (Equiv.refl (Fin 9)) sgB484 sgT484) sgFlag484 = 1 := by
  decide +kernel

lemma sg484 : RowSquare [3,2,2,2] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB484 sgT484 sgFlag484
  change solveCompact 9 (.full [3,3,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,3] (Equiv.refl (Fin 9)) sgB484 sgT484) sgFlag484 ≠ 0
  rw [sgCert484]
  norm_num

def sgB487 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 5 8 * (Equiv.swap 1 4 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))
def sgT487 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 2 1 * (Equiv.swap 5 8 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 3))))))
def sgFlag487 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(1,1,0),(1,1,1),(2,1,2),(0,2,0)}
lemma sgCert487 : solveCompact 9 (.full [3,3,2,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,2,1] (Equiv.refl (Fin 9)) sgB487 sgT487) sgFlag487 = 2 := by
  decide +kernel

lemma sg487 : RowSquare [3,2,2,2] [4,3,2] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [3,3,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB487 sgT487 sgFlag487
  change solveCompact 9 (.full [3,3,2,1]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,2,1] (Equiv.refl (Fin 9)) sgB487 sgT487) sgFlag487 ≠ 0
  rw [sgCert487]
  norm_num

def sgB489 : Equiv.Perm (Fin 9) := Equiv.swap 7 0 * (Equiv.swap 0 4 * (Equiv.swap 0 6 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 0 5))))))
def sgT489 : Equiv.Perm (Fin 9) := Equiv.swap 1 4 * (Equiv.swap 4 8 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 7))))
def sgFlag489 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(3,0,1),(0,0,2),(5,1,0),(1,1,1),(2,2,0)}
lemma sgCert489 : solveCompact 9 (.full [6,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB489 sgT489) sgFlag489 = 9 := by
  decide +kernel

lemma sg489 : RowSquare [3,3,1,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB489 sgT489 sgFlag489
  change solveCompact 9 (.full [6,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB489 sgT489) sgFlag489 ≠ 0
  rw [sgCert489]
  norm_num

def sgB490 : Equiv.Perm (Fin 9) := Equiv.swap 2 8 * (Equiv.swap 0 1 * (Equiv.swap 3 5 * (Equiv.swap 2 7 * (Equiv.swap 1 6 * (Equiv.swap 0 4)))))
def sgT490 : Equiv.Perm (Fin 9) := Equiv.swap 7 1 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))
def sgFlag490 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(4,0,0),(1,0,1),(2,0,2),(3,1,0),(3,1,1),(0,2,0)}
lemma sgCert490 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 = 2 := by
  decide +kernel

lemma sg490 : RowSquare [3,3,1,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB490 sgT490 sgFlag490
  change solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 ≠ 0
  rw [sgCert490]
  norm_num

def sgB495 : Equiv.Perm (Fin 9) := Equiv.swap 2 0 * (Equiv.swap 3 5 * (Equiv.swap 2 7 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))
def sgT495 : Equiv.Perm (Fin 9) := Equiv.swap 6 8 * (Equiv.swap 6 3 * (Equiv.swap 3 4 * (Equiv.swap 4 7 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 5))))))
def sgFlag495 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,2),(0,1,1),(1,1,1),(0,2,0)}
lemma sgCert495 : solveCompact 9 (.full [4,3,2]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [4,3,2] (Equiv.refl (Fin 9)) sgB495 sgT495) sgFlag495 = 1 := by
  decide +kernel

lemma sg495 : RowSquare [3,3,1,1,1] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB495 sgT495 sgFlag495
  change solveCompact 9 (.full [4,3,2]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [4,3,2] (Equiv.refl (Fin 9)) sgB495 sgT495) sgFlag495 ≠ 0
  rw [sgCert495]
  norm_num

def sgB496 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 5 8 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgT496 : Equiv.Perm (Fin 9) := Equiv.swap 5 7 * (Equiv.swap 3 1 * (Equiv.swap 2 4 * (Equiv.swap 1 8)))
def sgFlag496 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(0,0,2),(2,1,1),(1,2,0)}
lemma sgCert496 : solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB496 sgT496) sgFlag496 = -1 := by
  decide +kernel

lemma sg496 : RowSquare [3,3,1,1,1] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB496 sgT496 sgFlag496
  change solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB496 sgT496) sgFlag496 ≠ 0
  rw [sgCert496]
  norm_num

def sgB511 : Equiv.Perm (Fin 9) := Equiv.swap 3 6 * (Equiv.swap 6 2 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 1 5)))))
def sgT511 : Equiv.Perm (Fin 9) := Equiv.swap 5 4 * (Equiv.swap 4 0 * (Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 0 3))))
def sgFlag511 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,1),(6,0,2),(5,1,0),(0,1,1),(1,1,2),(0,2,0),(4,2,1)}
lemma sgCert511 : solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB511 sgT511) sgFlag511 = 120 := by
  decide +kernel

lemma sg511 : RowSquare [3,3,2,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB511 sgT511 sgFlag511
  change solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB511 sgT511) sgFlag511 ≠ 0
  rw [sgCert511]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB513 : Equiv.Perm (Fin 9) := Equiv.swap 1 8 * (Equiv.swap 1 6 * (Equiv.swap 4 7 * (Equiv.swap 1 5 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))
def sgT513 : Equiv.Perm (Fin 9) := Equiv.swap 3 0 * (Equiv.swap 0 2 * (Equiv.swap 3 7 * (Equiv.swap 3 1 * (Equiv.swap 2 8 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))))
def sgFlag513 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,1),(0,0,2),(4,1,0),(0,1,1),(2,2,0),(1,2,2)}
lemma sgCert513 : solveCompact 9 (.full [5,2,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB513 sgT513) sgFlag513 = 4 := by
  decide +kernel

lemma sg513 : RowSquare [3,3,2,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,2,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB513 sgT513 sgFlag513
  change solveCompact 9 (.full [5,2,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB513 sgT513) sgFlag513 ≠ 0
  rw [sgCert513]
  norm_num

def sgB535 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 5 1 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))
def sgT535 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 1 * (Equiv.swap 2 7 * (Equiv.swap 1 4 * (Equiv.swap 0 6))))
def sgFlag535 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(0,0,1),(6,0,2),(2,0,3),(4,1,0),(5,1,1),(0,2,0),(1,3,0)}
lemma sgCert535 : solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB535 sgT535) sgFlag535 = 4 := by
  decide +kernel

lemma sg535 : RowSquare [4,2,1,1,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB535 sgT535 sgFlag535
  change solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB535 sgT535) sgFlag535 ≠ 0
  rw [sgCert535]
  norm_num

def sgB536 : Equiv.Perm (Fin 9) := Equiv.swap 6 3 * (Equiv.swap 0 8 * (Equiv.swap 0 5 * (Equiv.swap 3 1 * (Equiv.swap 0 4 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgT536 : Equiv.Perm (Fin 9) := Equiv.swap 1 4 * (Equiv.swap 4 0 * (Equiv.swap 0 8 * (Equiv.swap 0 3 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))
def sgFlag536 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,2),(4,0,3),(0,1,0),(5,1,0),(3,2,0),(2,3,1)}
lemma sgCert536 : solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB536 sgT536) sgFlag536 = 10 := by
  decide +kernel

lemma sg536 : RowSquare [4,2,1,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB536 sgT536 sgFlag536
  change solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB536 sgT536) sgFlag536 ≠ 0
  rw [sgCert536]
  norm_num

def sgB537 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 1 8 * (Equiv.swap 0 6))))))
def sgT537 : Equiv.Perm (Fin 9) := Equiv.swap 6 7 * (Equiv.swap 1 8 * (Equiv.swap 0 2))
def sgFlag537 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(4,0,1),(1,0,2),(0,1,0),(3,1,0),(0,2,0),(3,3,3)}
lemma sgCert537 : solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB537 sgT537) sgFlag537 = 3 := by
  decide +kernel

lemma sg537 : RowSquare [4,2,1,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB537 sgT537 sgFlag537
  change solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB537 sgT537) sgFlag537 ≠ 0
  rw [sgCert537]
  norm_num

def sgB541 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 2 7 * (Equiv.swap 5 0 * (Equiv.swap 2 6 * (Equiv.swap 2 4 * (Equiv.swap 1 3 * (Equiv.swap 0 8))))))
def sgT541 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 0 * (Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))
def sgFlag541 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(3,0,2),(0,1,0),(0,1,3),(2,2,0),(4,3,1)}
lemma sgCert541 : solveCompact 9 (.full [5,2,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,2,2] (Equiv.refl (Fin 9)) sgB541 sgT541) sgFlag541 = 1 := by
  decide +kernel

lemma sg541 : RowSquare [4,2,1,1,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB541 sgT541 sgFlag541
  change solveCompact 9 (.full [5,2,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,2,2] (Equiv.refl (Fin 9)) sgB541 sgT541) sgFlag541 ≠ 0
  rw [sgCert541]
  norm_num

def sgB548 : Equiv.Perm (Fin 9) := Equiv.swap 3 2 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))
def sgT548 : Equiv.Perm (Fin 9) := Equiv.swap 1 5 * (Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 1 2 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 7))))))
def sgFlag548 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(7,0,0),(2,0,1),(1,0,3),(4,1,0),(6,1,1),(5,1,2),(0,2,1),(3,3,0)}
lemma sgCert548 : solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB548 sgT548) sgFlag548 = 56 := by
  decide +kernel

lemma sg548 : RowSquare [4,2,2,1] [2,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [8,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB548 sgT548 sgFlag548
  change solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB548 sgT548) sgFlag548 ≠ 0
  rw [sgCert548]
  norm_num

def sgB549 : Equiv.Perm (Fin 9) := Equiv.swap 0 8 * (Equiv.swap 3 2 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 7))))))
def sgT549 : Equiv.Perm (Fin 9) := Equiv.swap 4 1 * (Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 8)))
def sgFlag549 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(6,0,3),(0,1,0),(5,1,0),(4,1,2),(0,2,1),(3,3,0)}
lemma sgCert549 : solveCompact 9 (.full [7,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,2] (Equiv.refl (Fin 9)) sgB549 sgT549) sgFlag549 = -8 := by
  decide +kernel

lemma sg549 : RowSquare [4,2,2,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB549 sgT549 sgFlag549
  change solveCompact 9 (.full [7,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,2] (Equiv.refl (Fin 9)) sgB549 sgT549) sgFlag549 ≠ 0
  rw [sgCert549]
  norm_num

def sgB550 : Equiv.Perm (Fin 9) := Equiv.swap 1 4 * (Equiv.swap 4 8 * (Equiv.swap 4 6 * (Equiv.swap 4 2 * (Equiv.swap 1 0 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))))
def sgT550 : Equiv.Perm (Fin 9) := Equiv.swap 5 6 * (Equiv.swap 3 7 * (Equiv.swap 0 2))
def sgFlag550 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(2,0,1),(4,0,2),(0,1,0),(3,1,0),(1,1,3),(0,2,1),(1,3,0)}
lemma sgCert550 : solveCompact 9 (.full [6,3]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [6,3] (Equiv.refl (Fin 9)) sgB550 sgT550) sgFlag550 = 12 := by
  decide +kernel

lemma sg550 : RowSquare [4,2,2,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB550 sgT550 sgFlag550
  change solveCompact 9 (.full [6,3]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [6,3] (Equiv.refl (Fin 9)) sgB550 sgT550) sgFlag550 ≠ 0
  rw [sgCert550]
  norm_num

end UniversalTensorSquare
end
end

end OAI
