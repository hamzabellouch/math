import Mathlib
import OAI.Topology.ArtinGroups.Geometry.DihedralScalar
import OAI.Topology.ArtinGroups.Coxeter.AltNext

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma alternating_next_root (i j : S) (hij : i ≠ j) (n : ℕ) :
    representation cs (cs.wordProd (altList i j n)) (Pi.single (altNext i j n) 1) =
      dihedralScalar (M i j) (n+1) • Pi.single i 1 +
        dihedralScalar (M i j) n • Pi.single j 1 := by
  induction n generalizing i j with
  | zero =>
    simp only [altList_zero, cs.wordProd_nil, map_one, altNext_zero,
      dihedralScalar_zero, zero_smul, add_zero]
    rw [dihedralScalar_one _ (by have := M.off_diagonal i j hij; omega), one_smul]
    rfl
  | succ n ih =>
    rw [altList_succ, cs.wordProd_cons, map_mul, LinearEquiv.mul_apply,
      altNext_succ, ih j i (Ne.symm hij)]
    simp only [representation_simple, map_add, map_smul,
      simpleReflection_basis_other i j hij, simpleReflection_basis_self,
      ← M.symmetric i j]
    rw [show n+1+1=n+2 by omega, dihedralScalar_recurrence]
    module

end HarmonicArtin.Geometric

end OAI
