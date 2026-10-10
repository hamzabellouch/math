import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomains
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB10 : Equiv.Perm (Fin 4) := Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 3))
def sgT10 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * (Equiv.swap 1 0 * (Equiv.swap 0 2))
def sgFlag10 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(0,1,0)}
lemma sgCert10 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 = -2 := by
  decide +kernel

lemma sg10 : RowSquare [2,1,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB10 sgT10 sgFlag10
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 ≠ 0
  rw [sgCert10]
  norm_num

def sgB17 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * (Equiv.swap 0 1)
def sgT17 : Equiv.Perm (Fin 4) := Equiv.swap 2 3
def sgFlag17 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(1,1,0)}
lemma sgCert17 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 = -2 := by
  decide +kernel

lemma sg17 : RowSquare [3,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB17 sgT17 sgFlag17
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 ≠ 0
  rw [sgCert17]
  norm_num

def sgB67 : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * (Equiv.swap 1 0 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))
def sgT67 : Equiv.Perm (Fin 6) := Equiv.swap 3 5 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 4)))
def sgFlag67 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(3,0,1),(1,0,2),(0,1,0),(1,2,0)}
lemma sgCert67 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 = -8 := by
  decide +kernel

lemma sg67 : RowSquare [3,1,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB67 sgT67 sgFlag67
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 ≠ 0
  rw [sgCert67]
  norm_num

def sgB68 : Equiv.Perm (Fin 6) := Equiv.swap 2 5 * (Equiv.swap 0 1)
def sgT68 : Equiv.Perm (Fin 6) := Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 4))
def sgFlag68 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(2,0,2),(2,1,0),(0,2,0)}
lemma sgCert68 : solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB68 sgT68) sgFlag68 = 6 := by
  decide +kernel

lemma sg68 : RowSquare [3,1,1,1] [2,2,2] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB68 sgT68 sgFlag68
  change solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB68 sgT68) sgFlag68 ≠ 0
  rw [sgCert68]
  norm_num

def sgB71 : Equiv.Perm (Fin 6) := Equiv.swap 1 5 * (Equiv.swap 1 4 * (Equiv.swap 0 3))
def sgT71 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * (Equiv.swap 3 5 * (Equiv.swap 0 4))
def sgFlag71 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(1,1,0),(0,2,2)}
lemma sgCert71 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 = 2 := by
  decide +kernel

lemma sg71 : RowSquare [3,1,1,1] [3,3] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB71 sgT71 sgFlag71
  change solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 ≠ 0
  rw [sgCert71]
  norm_num

def sgB88 : Equiv.Perm (Fin 6) := Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 3))
def sgT88 : Equiv.Perm (Fin 6) := Equiv.swap 0 2
def sgFlag88 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,1),(3,0,2),(1,1,0),(0,2,0)}
lemma sgCert88 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB88 sgT88) sgFlag88 = 8 := by
  decide +kernel

lemma sg88 : RowSquare [4,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB88 sgT88 sgFlag88
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB88 sgT88) sgFlag88 ≠ 0
  rw [sgCert88]
  norm_num

def sgB89 : Equiv.Perm (Fin 6) := Equiv.swap 2 1 * (Equiv.swap 2 4 * (Equiv.swap 1 5))
def sgT89 : Equiv.Perm (Fin 6) := Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 1 4 * (Equiv.swap 1 0 * (Equiv.swap 0 2))))
def sgFlag89 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(1,0,2),(0,1,0),(1,2,0)}
lemma sgCert89 : solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB89 sgT89) sgFlag89 = 6 := by
  decide +kernel

lemma sg89 : RowSquare [4,1,1] [2,2,2] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB89 sgT89 sgFlag89
  change solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB89 sgT89) sgFlag89 ≠ 0
  rw [sgCert89]
  norm_num

def sgB92 : Equiv.Perm (Fin 6) := Equiv.swap 4 2 * (Equiv.swap 2 0 * (Equiv.swap 2 1 * (Equiv.swap 1 3 * (Equiv.swap 0 5))))
def sgT92 : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))
def sgFlag92 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,2),(1,1,0),(1,2,1)}
lemma sgCert92 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB92 sgT92) sgFlag92 = 1 := by
  decide +kernel

lemma sg92 : RowSquare [4,1,1] [3,3] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB92 sgT92 sgFlag92
  change solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB92 sgT92) sgFlag92 ≠ 0
  rw [sgCert92]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB143 : Equiv.Perm (Fin 7) := Equiv.swap 0 6 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 0 4)))
def sgT143 : Equiv.Perm (Fin 7) := Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 1 2))
def sgFlag143 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,0,2),(4,1,0),(2,1,1),(3,2,0)}
lemma sgCert143 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 = 6 := by
  decide +kernel

lemma sg143 : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
  norm_num

def sgB144 : Equiv.Perm (Fin 7) := Equiv.swap 5 1 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 4))))
def sgT144 : Equiv.Perm (Fin 7) := Equiv.swap 0 5 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 4))))
def sgFlag144 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,2),(1,1,0),(2,1,0),(3,2,0)}
lemma sgCert144 : solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB144 sgT144) sgFlag144 = 2 := by
  decide +kernel

lemma sg144 : RowSquare [3,2,1,1] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB144 sgT144 sgFlag144
  change solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB144 sgT144) sgFlag144 ≠ 0
  rw [sgCert144]
  norm_num

def sgB154 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * (Equiv.swap 0 2 * (Equiv.swap 2 6 * (Equiv.swap 0 3)))
def sgT154 : Equiv.Perm (Fin 7) := Equiv.swap 1 2 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 5)))
def sgFlag154 : Finset (ℕ × ℕ × ℕ) := {(5,0,0),(1,0,1),(3,0,2),(0,1,0),(2,1,0),(4,1,1),(0,2,1)}
lemma sgCert154 : solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB154 sgT154) sgFlag154 = 15 := by
  decide +kernel

lemma sg154 : RowSquare [3,2,2] [2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [6,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB154 sgT154 sgFlag154
  change solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB154 sgT154) sgFlag154 ≠ 0
  rw [sgCert154]
  norm_num

def sgB155 : Equiv.Perm (Fin 7) := Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))
def sgT155 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 5 * (Equiv.swap 2 0 * (Equiv.swap 0 3)))
def sgFlag155 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(3,0,1),(0,0,2),(1,1,0),(2,1,0),(1,1,1),(0,2,1)}
lemma sgCert155 : solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB155 sgT155) sgFlag155 = 12 := by
  decide +kernel

lemma sg155 : RowSquare [3,2,2] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB155 sgT155 sgFlag155
  change solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB155 sgT155) sgFlag155 ≠ 0
  rw [sgCert155]
  norm_num

def sgB156 : Equiv.Perm (Fin 7) := Equiv.swap 4 0 * (Equiv.swap 4 1 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))
def sgT156 : Equiv.Perm (Fin 7) := Equiv.swap 3 1 * (Equiv.swap 1 4)
def sgFlag156 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,1,0),(2,1,1),(3,1,1),(2,2,2)}
lemma sgCert156 : solveCompact 7 (.full [4,3]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,3] (Equiv.refl (Fin 7)) sgB156 sgT156) sgFlag156 = 12 := by
  decide +kernel

lemma sg156 : RowSquare [3,2,2] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB156 sgT156 sgFlag156
  change solveCompact 7 (.full [4,3]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,3] (Equiv.refl (Fin 7)) sgB156 sgT156) sgFlag156 ≠ 0
  rw [sgCert156]
  norm_num

def sgB157 : Equiv.Perm (Fin 7) := Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 0 5))))
def sgT157 : Equiv.Perm (Fin 7) := Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))
def sgFlag157 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(0,1,0),(4,1,1),(2,1,2),(3,2,0)}
lemma sgCert157 : solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB157 sgT157) sgFlag157 = 6 := by
  decide +kernel

lemma sg157 : RowSquare [3,2,2] [3,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB157 sgT157 sgFlag157
  change solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB157 sgT157) sgFlag157 ≠ 0
  rw [sgCert157]
  norm_num

def sgB158 : Equiv.Perm (Fin 7) := Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgT158 : Equiv.Perm (Fin 7) := Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 1 2))
def sgFlag158 : Finset (ℕ × ℕ × ℕ) := {(0,0,1),(3,0,1),(1,0,2),(0,1,0),(1,1,0),(2,1,1),(0,2,0)}
lemma sgCert158 : solveCompact 7 (.full [4,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,2,1] (Equiv.refl (Fin 7)) sgB158 sgT158) sgFlag158 = 4 := by
  decide +kernel

lemma sg158 : RowSquare [3,2,2] [3,2,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [4,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB158 sgT158 sgFlag158
  change solveCompact 7 (.full [4,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,2,1] (Equiv.refl (Fin 7)) sgB158 sgT158) sgFlag158 ≠ 0
  rw [sgCert158]
  norm_num

def sgB160 : Equiv.Perm (Fin 7) := Equiv.swap 4 6 * (Equiv.swap 2 3 * (Equiv.swap 1 5))
def sgT160 : Equiv.Perm (Fin 7) := Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 0 4))))
def sgFlag160 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(1,0,2),(1,1,0),(0,1,1),(0,2,0)}
lemma sgCert160 : solveCompact 7 (.full [3,2,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [3,2,2] (Equiv.refl (Fin 7)) sgB160 sgT160) sgFlag160 = -4 := by
  decide +kernel

lemma sg160 : RowSquare [3,2,2] [3,3,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB160 sgT160 sgFlag160
  change solveCompact 7 (.full [3,2,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [3,2,2] (Equiv.refl (Fin 7)) sgB160 sgT160) sgFlag160 ≠ 0
  rw [sgCert160]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB163 : Equiv.Perm (Fin 7) := Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 5))
def sgT163 : Equiv.Perm (Fin 7) := Equiv.swap 3 0 * (Equiv.swap 3 1 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgFlag163 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,1,1),(1,1,2),(1,2,1)}
lemma sgCert163 : solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB163 sgT163) sgFlag163 = -3 := by
  decide +kernel

lemma sg163 : RowSquare [3,2,2] [4,3] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB163 sgT163 sgFlag163
  change solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB163 sgT163) sgFlag163 ≠ 0
  rw [sgCert163]
  norm_num

def sgB165 : Equiv.Perm (Fin 7) := Equiv.swap 3 6 * (Equiv.swap 2 5 * (Equiv.swap 1 4))
def sgT165 : Equiv.Perm (Fin 7) := Equiv.swap 1 6 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 4)))
def sgFlag165 : Finset (ℕ × ℕ × ℕ) := {(4,0,0),(3,0,1),(5,0,2),(1,1,0),(0,1,1),(2,1,1),(0,2,0)}
lemma sgCert165 : solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 = 15 := by
  decide +kernel

lemma sg165 : RowSquare [3,3,1] [2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [6,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB165 sgT165 sgFlag165
  change solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 ≠ 0
  rw [sgCert165]
  norm_num

def sgB166 : Equiv.Perm (Fin 7) := Equiv.swap 5 4 * (Equiv.swap 4 6 * (Equiv.swap 2 0 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))
def sgT166 : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))
def sgFlag166 : Finset (ℕ × ℕ × ℕ) := {(1,0,1),(4,0,2),(0,1,0),(3,1,1),(2,2,0)}
lemma sgCert166 : solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 = 3 := by
  decide +kernel

lemma sg166 : RowSquare [3,3,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB166 sgT166 sgFlag166
  change solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 ≠ 0
  rw [sgCert166]
  norm_num

def sgB167 : Equiv.Perm (Fin 7) := Equiv.swap 3 1 * (Equiv.swap 1 6 * (Equiv.swap 0 2))
def sgT167 : Equiv.Perm (Fin 7) := Equiv.swap 2 0 * (Equiv.swap 2 5 * (Equiv.swap 0 6 * (Equiv.swap 2 4 * (Equiv.swap 0 3))))
def sgFlag167 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(3,0,2),(2,1,0),(1,1,1),(0,2,0)}
lemma sgCert167 : solveCompact 7 (.full [4,3]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,3] (Equiv.refl (Fin 7)) sgB167 sgT167) sgFlag167 = 12 := by
  decide +kernel

lemma sg167 : RowSquare [3,3,1] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB167 sgT167 sgFlag167
  change solveCompact 7 (.full [4,3]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,3] (Equiv.refl (Fin 7)) sgB167 sgT167) sgFlag167 ≠ 0
  rw [sgCert167]
  norm_num

def sgB168 : Equiv.Perm (Fin 7) := Equiv.swap 1 0 * (Equiv.swap 1 4 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 5))))
def sgT168 : Equiv.Perm (Fin 7) := Equiv.swap 1 6 * (Equiv.swap 1 4)
def sgFlag168 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(3,0,1),(0,1,0),(1,1,1),(4,1,2),(2,2,0)}
lemma sgCert168 : solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB168 sgT168) sgFlag168 = 6 := by
  decide +kernel

lemma sg168 : RowSquare [3,3,1] [3,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB168 sgT168 sgFlag168
  change solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB168 sgT168) sgFlag168 ≠ 0
  rw [sgCert168]
  norm_num

def sgB169 : Equiv.Perm (Fin 7) := Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))
def sgT169 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 6 * (Equiv.swap 0 5))))
def sgFlag169 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(0,1,0),(2,1,1),(0,1,2),(3,2,0)}
lemma sgCert169 : solveCompact 7 (.full [4,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,2,1] (Equiv.refl (Fin 7)) sgB169 sgT169) sgFlag169 = 3 := by
  decide +kernel

lemma sg169 : RowSquare [3,3,1] [3,2,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [4,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB169 sgT169 sgFlag169
  change solveCompact 7 (.full [4,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [4,2,1] (Equiv.refl (Fin 7)) sgB169 sgT169) sgFlag169 ≠ 0
  rw [sgCert169]
  norm_num

def sgB171 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 4 0 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 5))))
def sgT171 : Equiv.Perm (Fin 7) := Equiv.swap 0 3 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 0 4)))
def sgFlag171 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,2),(0,1,0),(1,1,1),(0,2,1)}
lemma sgCert171 : solveCompact 7 (.full [3,2,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [3,2,2] (Equiv.refl (Fin 7)) sgB171 sgT171) sgFlag171 = -1 := by
  decide +kernel

lemma sg171 : RowSquare [3,3,1] [3,3,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB171 sgT171 sgFlag171
  change solveCompact 7 (.full [3,2,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [3,2,2] (Equiv.refl (Fin 7)) sgB171 sgT171) sgFlag171 ≠ 0
  rw [sgCert171]
  norm_num

def sgB174 : Equiv.Perm (Fin 7) := Equiv.swap 1 4 * (Equiv.swap 4 6 * (Equiv.swap 1 5 * (Equiv.swap 1 2)))
def sgT174 : Equiv.Perm (Fin 7) := Equiv.swap 5 0 * (Equiv.swap 0 3 * (Equiv.swap 3 6 * (Equiv.swap 0 4)))
def sgFlag174 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,1,1),(1,1,2),(0,2,0)}
lemma sgCert174 : solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB174 sgT174) sgFlag174 = 1 := by
  decide +kernel

lemma sg174 : RowSquare [3,3,1] [4,3] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB174 sgT174 sgFlag174
  change solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB174 sgT174) sgFlag174 ≠ 0
  rw [sgCert174]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB194 : Equiv.Perm (Fin 7) := Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 1 4)))
def sgT194 : Equiv.Perm (Fin 7) := Equiv.swap 5 3 * (Equiv.swap 3 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))
def sgFlag194 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,1),(0,0,2),(0,1,0),(4,1,1),(2,2,0)}
lemma sgCert194 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB194 sgT194) sgFlag194 = 17 := by
  decide +kernel

lemma sg194 : RowSquare [4,2,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB194 sgT194 sgFlag194
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB194 sgT194) sgFlag194 ≠ 0
  rw [sgCert194]
  norm_num

def sgB195 : Equiv.Perm (Fin 7) := Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 5))))
def sgT195 : Equiv.Perm (Fin 7) := Equiv.swap 5 3 * (Equiv.swap 3 6 * (Equiv.swap 3 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))
def sgFlag195 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,1),(1,0,2),(0,1,0),(2,1,0),(2,2,1)}
lemma sgCert195 : solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB195 sgT195) sgFlag195 = 3 := by
  decide +kernel

lemma sg195 : RowSquare [4,2,1] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB195 sgT195 sgFlag195
  change solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB195 sgT195) sgFlag195 ≠ 0
  rw [sgCert195]
  norm_num

def sgB271 : Equiv.Perm (Fin 8) := Equiv.swap 5 4 * (Equiv.swap 4 7 * (Equiv.swap 2 6 * (Equiv.swap 0 1)))
def sgT271 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4)))
def sgFlag271 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(1,0,1),(2,0,2),(0,1,0),(2,1,0),(1,2,0)}
lemma sgCert271 : solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB271 sgT271) sgFlag271 = -4 := by
  decide +kernel

lemma sg271 : RowSquare [3,2,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB271 sgT271 sgFlag271
  change solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB271 sgT271) sgFlag271 ≠ 0
  rw [sgCert271]
  norm_num

def sgB275 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 1 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))
def sgT275 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 2 6 * (Equiv.swap 1 0 * (Equiv.swap 0 5))))
def sgFlag275 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,1),(1,0,2),(0,1,0),(0,1,1),(0,2,0)}
lemma sgCert275 : solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 = -1 := by
  decide +kernel

lemma sg275 : RowSquare [3,2,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB275 sgT275 sgFlag275
  change solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 ≠ 0
  rw [sgCert275]
  norm_num

def sgB285 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 1 4 * (Equiv.swap 2 5 * (Equiv.swap 1 0 * (Equiv.swap 0 3))))
def sgT285 : Equiv.Perm (Fin 8) := Equiv.swap 0 3 * (Equiv.swap 1 2 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgFlag285 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(4,1,0),(3,1,1),(2,1,2),(5,2,0)}
lemma sgCert285 : solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB285 sgT285) sgFlag285 = 24 := by
  decide +kernel

lemma sg285 : RowSquare [3,2,2,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB285 sgT285 sgFlag285
  change solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB285 sgT285) sgFlag285 ≠ 0
  rw [sgCert285]
  norm_num

def sgB286 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))
def sgT286 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgFlag286 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(0,0,1),(4,1,0),(1,1,1),(2,1,2),(3,2,0)}
lemma sgCert286 : solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB286 sgT286) sgFlag286 = -3 := by
  decide +kernel

lemma sg286 : RowSquare [3,2,2,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB286 sgT286 sgFlag286
  change solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB286 sgT286) sgFlag286 ≠ 0
  rw [sgCert286]
  norm_num

def sgB287 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 3)))
def sgT287 : Equiv.Perm (Fin 8) := Equiv.swap 6 2 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))
def sgFlag287 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(3,1,0),(0,1,1),(2,1,1),(3,2,0)}
lemma sgCert287 : solveCompact 8 (.full [4,4]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [4,4] (Equiv.refl (Fin 8)) sgB287 sgT287) sgFlag287 = 3 := by
  decide +kernel

lemma sg287 : RowSquare [3,2,2,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB287 sgT287 sgFlag287
  change solveCompact 8 (.full [4,4]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [4,4] (Equiv.refl (Fin 8)) sgB287 sgT287) sgFlag287 ≠ 0
  rw [sgCert287]
  norm_num

def sgB295 : Equiv.Perm (Fin 8) := Equiv.swap 4 6 * (Equiv.swap 2 7 * (Equiv.swap 0 3))
def sgT295 : Equiv.Perm (Fin 8) := Equiv.swap 6 2 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))
def sgFlag295 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(3,1,0),(4,1,1),(0,2,0),(5,2,2)}
lemma sgCert295 : solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB295 sgT295) sgFlag295 = 10 := by
  decide +kernel

lemma sg295 : RowSquare [3,3,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB295 sgT295 sgFlag295
  change solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB295 sgT295) sgFlag295 ≠ 0
  rw [sgCert295]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def sgB296 : Equiv.Perm (Fin 8) := Equiv.swap 4 0 * (Equiv.swap 3 1 * (Equiv.swap 0 7 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))
def sgT296 : Equiv.Perm (Fin 8) := Equiv.swap 4 2 * (Equiv.swap 2 0 * (Equiv.swap 4 6 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))
def sgFlag296 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(1,0,1),(4,0,1),(2,0,2),(1,1,0),(3,1,2),(0,2,0)}
lemma sgCert296 : solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB296 sgT296) sgFlag296 = 6 := by
  decide +kernel

lemma sg296 : RowSquare [3,3,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB296 sgT296 sgFlag296
  change solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB296 sgT296) sgFlag296 ≠ 0
  rw [sgCert296]
  norm_num

def sgB297 : Equiv.Perm (Fin 8) := Equiv.swap 1 6 * (Equiv.swap 0 4 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))
def sgT297 : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 0 6 * (Equiv.swap 2 5 * (Equiv.swap 0 3))))
def sgFlag297 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(3,0,2),(0,1,0),(1,1,2),(1,2,0),(3,2,0)}
lemma sgCert297 : solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 = -5 := by
  decide +kernel

lemma sg297 : RowSquare [3,3,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB297 sgT297 sgFlag297
  change solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 ≠ 0
  rw [sgCert297]
  norm_num

def sgB300 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 0 6 * (Equiv.swap 1 4 * (Equiv.swap 0 2)))
def sgT300 : Equiv.Perm (Fin 8) := Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 0 6)))))
def sgFlag300 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(3,1,0),(1,1,1),(0,2,0),(0,2,2)}
lemma sgCert300 : solveCompact 8 (.full [4,2,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB300 sgT300) sgFlag300 = -1 := by
  decide +kernel

lemma sg300 : RowSquare [3,3,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB300 sgT300 sgFlag300
  change solveCompact 8 (.full [4,2,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB300 sgT300) sgFlag300 ≠ 0
  rw [sgCert300]
  norm_num

def sgB301 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 6 * (Equiv.swap 1 5 * (Equiv.swap 1 2)))
def sgT301 : Equiv.Perm (Fin 8) := Equiv.swap 6 3 * (Equiv.swap 3 4 * (Equiv.swap 4 1 * (Equiv.swap 3 5 * (Equiv.swap 1 7 * (Equiv.swap 0 2)))))
def sgFlag301 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(0,0,1),(1,1,1),(1,1,2),(1,2,0),(0,2,2)}
lemma sgCert301 : solveCompact 8 (.full [3,3,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB301 sgT301) sgFlag301 = 5 := by
  decide +kernel

lemma sg301 : RowSquare [3,3,1,1] [3,3,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB301 sgT301 sgFlag301
  change solveCompact 8 (.full [3,3,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB301 sgT301) sgFlag301 ≠ 0
  rw [sgCert301]
  norm_num

def sgB309 : Equiv.Perm (Fin 8) := Equiv.swap 4 2 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 6 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 5))))))
def sgT309 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 2 4 * (Equiv.swap 0 5 * (Equiv.swap 0 1)))
def sgFlag309 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(1,0,2),(2,1,0),(0,1,1),(2,2,0),(4,2,1)}
lemma sgCert309 : solveCompact 8 (.full [5,3]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [5,3] (Equiv.refl (Fin 8)) sgB309 sgT309) sgFlag309 = -3 := by
  decide +kernel

lemma sg309 : RowSquare [3,3,2] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,2]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB309 sgT309 sgFlag309
  change solveCompact 8 (.full [5,3]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [5,3] (Equiv.refl (Fin 8)) sgB309 sgT309) sgFlag309 ≠ 0
  rw [sgCert309]
  norm_num

def sgB310 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 3 1 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 6)))))
def sgT310 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 0 6 * (Equiv.swap 0 1))))
def sgFlag310 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,1,0),(3,1,2),(0,2,1),(2,2,1)}
lemma sgCert310 : solveCompact 8 (.full [4,4]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [4,4] (Equiv.refl (Fin 8)) sgB310 sgT310) sgFlag310 = -2 := by
  decide +kernel

lemma sg310 : RowSquare [3,3,2] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,2]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB310 sgT310 sgFlag310
  change solveCompact 8 (.full [4,4]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [4,4] (Equiv.refl (Fin 8)) sgB310 sgT310) sgFlag310 ≠ 0
  rw [sgCert310]
  norm_num

def sgB311 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 0 2 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))))
def sgT311 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 5 3 * (Equiv.swap 0 7 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 4))))))
def sgFlag311 : Finset (ℕ × ℕ × ℕ) := {(0,0,1),(1,1,0),(0,1,2),(1,1,2),(1,2,0)}
lemma sgCert311 : solveCompact 8 (.full [2,2,2,2]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [2,2,2,2] (Equiv.refl (Fin 8)) sgB311 sgT311) sgFlag311 = 6 := by
  decide +kernel

lemma sg311 : RowSquare [3,3,2] [4,4] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,2]) (ts := [2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB311 sgT311 sgFlag311
  change solveCompact 8 (.full [2,2,2,2]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [2,2,2,2] (Equiv.refl (Fin 8)) sgB311 sgT311) sgFlag311 ≠ 0
  rw [sgCert311]
  norm_num

def sgB313 : Equiv.Perm (Fin 8) := Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgT313 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 3 * (Equiv.swap 0 7))
def sgFlag313 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(5,0,2),(4,0,3),(3,1,0),(1,2,0),(2,3,0)}
lemma sgCert313 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB313 sgT313) sgFlag313 = 24 := by
  decide +kernel

lemma sg313 : RowSquare [4,1,1,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB313 sgT313 sgFlag313
  change solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB313 sgT313) sgFlag313 ≠ 0
  rw [sgCert313]
  norm_num

end UniversalTensorSquare
end
end

end OAI
