import OAI.Topology.CoarseAssembly.CongruenceFibers

namespace OAI

/-! # Surjectivity of the successive special-linear reductions

Lift the entries arbitrarily. The lifted determinant is odd, hence a unit;
rescaling one row by its inverse corrects the determinant without changing
the reduction. Level zero is handled by its singleton group.
-/

namespace CoarseAssembly.Congruence

@[simp] theorem residueMap_comp {l k n : ℕ} (hlk : l ≤ k) (hkn : k ≤ n)
    (a : ZMod (2 ^ n)) :
    residueMap hlk (residueMap hkn a) = residueMap (hlk.trans hkn) a := by
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((residueMap hlk).comp (residueMap hkn)) (residueMap (hlk.trans hkn))) a

theorem isUnit_of_residue_one {k : ℕ} (hk : 1 ≤ k) (a : ZMod (2 ^ (k + 1)))
    (ha : residueMap (Nat.le_succ k) a = 1) : IsUnit a := by
  have htwo := congrArg (residueMap hk) ha
  rw [residueMap_comp, map_one] at htwo
  have hval : (a.val : ZMod 2) = 1 := by
    simpa only [residueMap, ZMod.castHom_apply, ZMod.cast_eq_val, pow_one] using htwo
  rw [← ZMod.natCast_zmod_val a]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (Nat.succ_pos k)).2
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff a.val 2).2 hd
  exact zero_ne_one (hz.symm.trans hval)

theorem quotientMap_successor_surjective (k : ℕ) :
    Function.Surjective (quotientMap (Nat.le_succ k)) := by
  intro q
  by_cases hk : k = 0
  · subst k
    exact ⟨1, Subsingleton.elim _ _⟩
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  let φ := residueMap (Nat.le_succ k)
  let A : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ (k + 1))) :=
    fun i j => (q.val i j).val
  have hA : φ.mapMatrix A = q.val := by
    ext i j
    change φ ((q.val i j).val : ZMod (2 ^ (k + 1))) = q.val i j
    simp
  have hdet : φ A.det = 1 := by
    rw [RingHom.map_det, hA]
    exact q.property
  obtain ⟨u, hu⟩ := isUnit_of_residue_one hk1 A.det hdet
  let D : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ (k + 1))) :=
    Matrix.diagonal ![(u⁻¹ : (ZMod (2 ^ (k + 1)))ˣ), 1, 1]
  have hDdet : (D * A).det = 1 := by
    simp [D, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_succ, ← hu]
  have huφ : Units.map φ.toMonoidHom u = 1 := by
    apply Units.ext
    change φ (u : ZMod (2 ^ (k + 1))) = 1
    rw [hu]
    exact hdet
  have hinv : φ ((u⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) : ZMod (2 ^ (k + 1))) = 1 := by
    change ((Units.map φ.toMonoidHom u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = 1
    rw [map_inv, huφ]
    rfl
  have hD : φ.mapMatrix D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Matrix.diagonal, hinv]
  refine ⟨⟨D * A, hDdet⟩, ?_⟩
  apply Subtype.ext
  change φ.mapMatrix (D * A) = q.val
  rw [map_mul, hD, hA, one_mul]

end CoarseAssembly.Congruence

end OAI
