import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomainsCore
import OAI.RepresentationTheory.UniversalSquare.Support.NumericalSupport

namespace OAI

/-! Eight Split Certificate. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

def eightPlaceB10 : Equiv.Perm (Fin 8) := Equiv.swap 0 3 * (Equiv.swap 1 7 * (Equiv.swap 3 6 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))

def eightPlaceT10 : Equiv.Perm (Fin 8) := Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 7)))

def eightFlag10 (r a b : ℕ) : ℤ :=
  if (r,a,b) ∈ ([(0,0,0),(0,2,1),(0,3,3),(1,0,0),(1,1,0),(2,1,1),(3,0,2)] : List (ℕ × ℕ × ℕ)) then 1 else 0

lemma eightCertificate10 : contractionInteger [4,2,1,1] [4,2,1,1] [4,2,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB10 eightPlaceT10 eightFlag10 = -4 := by
  unfold eightFlag10
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

end UniversalTensorSquare
end

end OAI
