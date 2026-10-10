import OAI.SetTheory.PartitionPrinciple.Models.GroundExternalWordQuotient

namespace OAI

section

namespace PartitionPilot.Forcing.ExternalWordRewrite
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (J S : Type u) [Group J]

theorem symbolValue_inverse (a : Alphabet J S) :
    symbolValue J S (externalSymbolInverse a) = (symbolValue J S a)⁻¹ := by
  cases a with
  | inl g => exact map_inv (old J S) g
  | inr p =>
    change free J S (FreeGroup.mk [(p.1, !p.2)]) = (free J S (FreeGroup.mk [p]))⁻¹
    rw [← map_inv, FreeGroup.inv_mk]
    rfl

theorem evalWord_inverse (xs : List (Alphabet J S)) :
    evalWord J S ((xs.map externalSymbolInverse).reverse) = (evalWord J S xs)⁻¹ := by
  induction xs with
  | nil => exact (inv_one : (1 : External J S)⁻¹ = 1).symm
  | cons a xs ih =>
    rw [List.map_cons, List.reverse_cons]
    have append (v w : List (Alphabet J S)) :
        evalWord J S (v ++ w) = evalWord J S v * evalWord J S w :=
      (evalWord J S).map_mul v w
    rw [append, ih]
    have singleton : evalWord J S [externalSymbolInverse a] = (symbolValue J S a)⁻¹ := by
      exact symbolValue_inverse J S a
    have cons : evalWord J S (a :: xs) = symbolValue J S a * evalWord J S xs := by
      exact (evalWord J S).map_mul (FreeMonoid.of a) (FreeMonoid.ofList xs)
    rw [singleton, cons, mul_inv_rev]

end PartitionPilot.Forcing.ExternalWordRewrite

end

end OAI
