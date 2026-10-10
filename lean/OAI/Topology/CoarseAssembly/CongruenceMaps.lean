import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CongruenceQuotients

namespace OAI

/-! # Compatible reductions between the congruence fibers

These are the actual entrywise reductions, including level zero. In
particular, the compatibility of the chosen holonomy is a theorem, not an
extra assumption on the graph construction.
-/

namespace CoarseAssembly.Congruence

@[simp] theorem quotientMap_self (k : ℕ) (q : Quotient k) :
    quotientMap (le_refl k) q = q := by
  apply Subtype.ext
  ext i j
  simp [quotientMap, residueMap, Matrix.SpecialLinearGroup.map_apply_coe]

@[simp] theorem quotientMap_comp {l k n : ℕ} (hlk : l ≤ k) (hkn : k ≤ n)
    (q : Quotient n) :
    quotientMap hlk (quotientMap hkn q) = quotientMap (hlk.trans hkn) q := by
  have hring : (residueMap hlk).comp (residueMap hkn) =
      residueMap (hlk.trans hkn) := RingHom.ext_zmod _ _
  apply Subtype.ext
  ext i j
  exact DFunLike.congr_fun hring (q.val i j)

@[simp] theorem quotientMap_reduce {l k : ℕ} (h : l ≤ k) (w : ArithmeticGroup) :
    quotientMap h (reduce k w) = reduce l w := by
  apply Subtype.ext
  ext i j
  simp [quotientMap, reduce, Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_diagonal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : Rˣ) :
    Matrix.SpecialLinearGroup.map f (diagonal t) =
      diagonal (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  ext i j
  change f ((diagonal t).val i j) = (diagonal (Units.map f.toMonoidHom t)).val i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, Matrix.diagonal]

@[simp] theorem quotientMap_holonomy (t : ℤ_[2]ˣ) {l k : ℕ} (h : l ≤ k) :
    quotientMap h (holonomy t k) = holonomy t l := by
  rw [quotientMap, holonomy, map_diagonal, holonomy]
  congr 1
  apply Units.ext
  exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow l k h) (t : ℤ_[2])

instance quotientZeroSubsingleton : Subsingleton (Quotient 0) := by
  have : Subsingleton (ZMod (2 ^ 0)) := by change Subsingleton (ZMod 1); infer_instance
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

end CoarseAssembly.Congruence

end OAI
