import OAI.Topology.CoarseAssembly.CongruenceSpectral

namespace OAI

/-! # Elementary generators in the finite congruence quotients -/

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

lemma reduce_transvection (k : ℕ) {i j : Fin 3} (h : i ≠ j) (a : ℤ) :
    reduce k (Matrix.SpecialLinearGroup.transvection h a) =
      Matrix.SpecialLinearGroup.transvection h (a : ZMod (2 ^ k)) := by
  apply Subtype.ext
  ext r s
  simp [reduce, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply]

lemma transvection_mem_elementaryReduction (k : ℕ) {i j : Fin 3} (h : i ≠ j)
    (a : ZMod (2 ^ k)) :
    Matrix.SpecialLinearGroup.transvection h a ∈ (elementaryReduction k).range := by
  refine ⟨Elementary.elementaryTransvection h (a.val : ℤ), ?_⟩
  change reduce k (Matrix.SpecialLinearGroup.transvection h (a.val : ℤ)) = _
  rw [reduce_transvection]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma elementaryReduction_zero_surjective : Function.Surjective (elementaryReduction 0) := by
  intro q
  exact ⟨1, Subsingleton.elim _ _⟩

lemma elementaryReduction_one_surjective : Function.Surjective (elementaryReduction 1) := by
  let : Fact (Nat.Prime (2 ^ 1)) := ⟨by norm_num⟩
  intro q
  have hmem : q ∈ (elementaryReduction 1).range := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun M => M ∈ (elementaryReduction 1).range) q
    · intro i j hij c hc
      have hc1 : c = 1 := by
        change ZMod 2 at c
        change c ≠ (0 : ZMod 2) at hc
        fin_cases c
        · exact (hc rfl).elim
        · rfl
      subst c
      have hdiag : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod (2 ^ 1)) (by simp) = 1 := by
        apply Subtype.ext
        ext r s
        simp [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.one_apply]
      rw [hdiag]
      exact one_mem _
    · intro i j hij a
      exact transvection_mem_elementaryReduction 1 hij a
    · intro A B hA hB
      exact mul_mem hA hB
  exact hmem

lemma elementary_row_same (k : ℕ) {i j : Fin 3} (h : i ≠ j)
    (a : ZMod (2 ^ k)) (q : Congruence.Quotient k) (c : Fin 3) :
    (Matrix.SpecialLinearGroup.transvection h a * q).val i c = q.val i c + a * q.val j c := by
  change (Matrix.transvection i j a * q.val) i c = _
  simp only [Matrix.transvection_mul_apply_same]

lemma elementary_row_other (k : ℕ) {i j : Fin 3} (h : i ≠ j)
    (a : ZMod (2 ^ k)) (q : Congruence.Quotient k) (r c : Fin 3) (hr : r ≠ i) :
    (Matrix.SpecialLinearGroup.transvection h a * q).val r c = q.val r c := by
  change (Matrix.transvection i j a * q.val) r c = _
  exact Matrix.transvection_mul_apply_of_ne i j r c hr a q.val

lemma upperUnitriangular_mem_elementaryReduction (k : ℕ) (q : Congruence.Quotient k)
    (h00 : q.val 0 0 = 1) (h11 : q.val 1 1 = 1) (h22 : q.val 2 2 = 1)
    (h10 : q.val 1 0 = 0) (h20 : q.val 2 0 = 0) (h21 : q.val 2 1 = 0) :
    q ∈ (elementaryReduction k).range := by
  let T (i j : Fin 3) (h : i ≠ j) (a : ZMod (2 ^ k)) :=
    Matrix.SpecialLinearGroup.transvection h a
  have he : q = T 0 1 (by decide) (q.val 0 1) *
      T 0 2 (by decide) (q.val 0 2 - q.val 0 1 * q.val 1 2) *
      T 1 2 (by decide) (q.val 1 2) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply,
        h00, h11, h22, h10, h20, h21]
  rw [he]
  exact mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
    (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _)

lemma diagonal_mem_elementaryReduction (k : ℕ) (u : (ZMod (2 ^ k))ˣ) :
    diagonal u ∈ (elementaryReduction k).range := by
  let T (i j : Fin 3) (h : i ≠ j) (a : ZMod (2 ^ k)) :=
    Matrix.SpecialLinearGroup.transvection h a
  have hw (v : (ZMod (2 ^ k))ˣ) :
      (T 0 1 (by decide) v *
        T 1 0 (by decide) (-((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 0 1 (by decide) v).val = !![0, (v : ZMod (2 ^ k)), 0; -((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), 0, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.single, Matrix.one_apply, mul_add, add_mul]
  have hneg : (T 0 1 (by decide) (-1) * T 1 0 (by decide) 1 *
      T 0 1 (by decide) (-1)).val = !![0, (-1 : ZMod (2 ^ k)), 0; 1, 0, 0; 0, 0, 1] := by
    simpa using hw (-1)
  have he : diagonal u =
      (T 0 1 (by decide) u *
        T 1 0 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 0 1 (by decide) u) *
      (T 0 1 (by decide) (-1) * T 1 0 (by decide) 1 *
        T 0 1 (by decide) (-1)) := by
    apply Subtype.ext
    change _ = (T 0 1 (by decide) u *
        T 1 0 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 0 1 (by decide) u).val * _
    rw [hw, hneg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]
  rw [he]
  exact mul_mem
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))

def secondDiagonal (k : ℕ) (u : (ZMod (2 ^ k))ˣ) : Congruence.Quotient k :=
  ⟨Matrix.diagonal ![1, (u : ZMod (2 ^ k)), ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))], by
    simp [Matrix.det_diagonal, Fin.prod_univ_succ]⟩

lemma secondDiagonal_mem_elementaryReduction (k : ℕ) (u : (ZMod (2 ^ k))ˣ) :
    secondDiagonal k u ∈ (elementaryReduction k).range := by
  let T (i j : Fin 3) (h : i ≠ j) (a : ZMod (2 ^ k)) :=
    Matrix.SpecialLinearGroup.transvection h a
  have hw (v : (ZMod (2 ^ k))ˣ) :
      (T 1 2 (by decide) v *
        T 2 1 (by decide) (-((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 1 2 (by decide) v).val = !![1, 0, 0; 0, 0, (v : ZMod (2 ^ k)); 0, -((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.single, Matrix.one_apply, mul_add, add_mul]
  have hneg : (T 1 2 (by decide) (-1) * T 2 1 (by decide) 1 *
      T 1 2 (by decide) (-1)).val = !![1, 0, 0; 0, 0, (-1 : ZMod (2 ^ k)); 0, 1, 0] := by
    simpa using hw (-1)
  have he : secondDiagonal k u =
      (T 1 2 (by decide) u *
        T 2 1 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 1 2 (by decide) u) *
      (T 1 2 (by decide) (-1) * T 2 1 (by decide) 1 *
        T 1 2 (by decide) (-1)) := by
    apply Subtype.ext
    change _ = (T 1 2 (by decide) u *
        T 2 1 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 1 2 (by decide) u).val * _
    rw [hw, hneg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [secondDiagonal, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]
  rw [he]
  exact mul_mem
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))

lemma upperTriangular_mem_elementaryReduction (k : ℕ) (q : Congruence.Quotient k)
    (h10 : q.val 1 0 = 0) (h20 : q.val 2 0 = 0) (h21 : q.val 2 1 = 0)
    (h00 : IsUnit (q.val 0 0)) (h11 : IsUnit (q.val 1 1)) :
    q ∈ (elementaryReduction k).range := by
  obtain ⟨u, hu⟩ := h00
  obtain ⟨v, hv⟩ := h11
  let a := diagonal u⁻¹
  let b := secondDiagonal k (u * v)⁻¹
  let n := b * (a * q)
  have hn (i j : Fin 3) : n.val i j =
      (![1, (((u * v)⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), ((u * v : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))] i) *
      ((![((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), (u : ZMod (2 ^ k)), 1] i) * q.val i j) := by
    change (b.val * (a.val * q.val)) i j = _
    simp [b, a, secondDiagonal, diagonal, Matrix.diagonal_mul]
  have hdet : ((u * v : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) * q.val 2 2 = 1 := by
    have h := q.property
    rw [Matrix.det_fin_three] at h
    simpa only [h10, h20, h21, mul_zero, zero_mul, add_zero, sub_zero,
      ← hu, ← hv, Units.val_mul, mul_assoc] using h
  have hn00 : n.val 0 0 = 1 := by rw [hn, ← hu]; simp
  have hn11 : n.val 1 1 = 1 := by
    rw [hn, ← hv]
    change (((u * v)⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) *
      ((u : ZMod (2 ^ k)) * (v : ZMod (2 ^ k))) = 1
    change (((u * v)⁻¹ * (u * v) : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = 1
    simp
  have hn22 : n.val 2 2 = 1 := by simpa [hn] using hdet
  have hn10 : n.val 1 0 = 0 := by rw [hn, h10]; simp
  have hn20 : n.val 2 0 = 0 := by rw [hn, h20]; simp
  have hn21 : n.val 2 1 = 0 := by rw [hn, h21]; simp
  have hnmem := upperUnitriangular_mem_elementaryReduction k n hn00 hn11 hn22 hn10 hn20 hn21
  have ha : a ∈ (elementaryReduction k).range := diagonal_mem_elementaryReduction k u⁻¹
  have hb : b ∈ (elementaryReduction k).range := secondDiagonal_mem_elementaryReduction k (u * v)⁻¹
  exact ((elementaryReduction k).range.mul_mem_cancel_left ha).mp
    (((elementaryReduction k).range.mul_mem_cancel_left hb).mp hnmem)

lemma isUnit_of_mod_two_one {k : ℕ} (hk : 1 ≤ k) (a : ZMod (2 ^ k))
    (ha : residueMap hk a = 1) : IsUnit a := by
  have hval : (a.val : ZMod 2) = 1 := by
    simpa only [residueMap, ZMod.castHom_apply, ZMod.cast_eq_val, pow_one] using ha
  rw [← ZMod.natCast_zmod_val a]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (lt_of_lt_of_le Nat.zero_lt_one hk)).2
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff a.val 2).2 hd
  exact zero_ne_one (hz.symm.trans hval)

lemma mod_two_identity_entry {k : ℕ} (hk : 1 ≤ k) (q : Congruence.Quotient k)
    (hq : quotientMap hk q = 1) (i j : Fin 3) :
    residueMap hk (q.val i j) = if i = j then 1 else 0 := by
  have h := congrArg (fun z : Congruence.Quotient 1 => z.val i j) hq
  simpa only [quotientMap, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply] using h

lemma mod_two_identity_first_pivot {k : ℕ} (hk : 1 ≤ k) (q : Congruence.Quotient k)
    (hq : quotientMap hk q = 1) : IsUnit (q.val 0 0) := by
  apply isUnit_of_mod_two_one hk
  simpa using mod_two_identity_entry hk q hq 0 0

lemma mod_two_identity_schur_pivot {k : ℕ} (hk : 1 ≤ k) (q : Congruence.Quotient k)
    (hq : quotientMap hk q = 1) (a : ZMod (2 ^ k)) :
    IsUnit (q.val 1 1 - q.val 1 0 * a * q.val 0 1) := by
  apply isUnit_of_mod_two_one hk
  rw [map_sub, map_mul, map_mul]
  have h11 : residueMap hk (q.val 1 1) = 1 := by
    simpa using mod_two_identity_entry hk q hq 1 1
  have h10 : residueMap hk (q.val 1 0) = 0 := by
    simpa using mod_two_identity_entry hk q hq 1 0
  rw [h11, h10, zero_mul, zero_mul, sub_zero]

lemma mod_two_kernel_mem_elementaryReduction {k : ℕ} (hk : 1 ≤ k)
    (q : Congruence.Quotient k) (hq : quotientMap hk q = 1) :
    q ∈ (elementaryReduction k).range := by
  obtain ⟨u, hu⟩ := mod_two_identity_first_pivot hk q hq
  let t1 := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0)
    (-q.val 1 0 * ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)))
  let m1 := t1 * q
  have hm1row0 (c : Fin 3) : m1.val 0 c = q.val 0 c :=
    elementary_row_other k _ _ q 0 c (by decide)
  have hm1row2 (c : Fin 3) : m1.val 2 c = q.val 2 c :=
    elementary_row_other k _ _ q 2 c (by decide)
  have hm110 : m1.val 1 0 = 0 := by
    change (t1 * q).val 1 0 = 0
    rw [elementary_row_same, ← hu]
    simp [mul_assoc]
  let t2 := Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0)
    (-q.val 2 0 * ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)))
  let m2 := t2 * m1
  have hm2row0 (c : Fin 3) : m2.val 0 c = q.val 0 c :=
    (elementary_row_other k _ _ m1 0 c (by decide)).trans (hm1row0 c)
  have hm210 : m2.val 1 0 = 0 :=
    (elementary_row_other k _ _ m1 1 0 (by decide)).trans hm110
  have hm220 : m2.val 2 0 = 0 := by
    change (t2 * m1).val 2 0 = 0
    rw [elementary_row_same, hm1row2, hm1row0, ← hu]
    simp [mul_assoc]
  have hm211 : m2.val 1 1 = q.val 1 1 - q.val 1 0 *
      ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) * q.val 0 1 := by
    change (t2 * m1).val 1 1 = _
    rw [elementary_row_other k _ _ m1 1 1 (by decide)]
    change (t1 * q).val 1 1 = _
    rw [elementary_row_same]
    ring
  have hunit2 : IsUnit (m2.val 1 1) := by
    rw [hm211]
    exact mod_two_identity_schur_pivot hk q hq _
  obtain ⟨v, hv⟩ := hunit2
  let t3 := Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1)
    (-m2.val 2 1 * ((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)))
  let m3 := t3 * m2
  have hm310 : m3.val 1 0 = 0 :=
    (elementary_row_other k _ _ m2 1 0 (by decide)).trans hm210
  have hm320 : m3.val 2 0 = 0 := by
    change (t3 * m2).val 2 0 = 0
    rw [elementary_row_same, hm220, hm210, mul_zero, add_zero]
  have hm321 : m3.val 2 1 = 0 := by
    change (t3 * m2).val 2 1 = 0
    rw [elementary_row_same, ← hv]
    simp [mul_assoc]
  have hm300 : IsUnit (m3.val 0 0) := by
    have he : m3.val 0 0 = q.val 0 0 :=
      (elementary_row_other k _ _ m2 0 0 (by decide)).trans (hm2row0 0)
    rw [he, ← hu]
    exact u.isUnit
  have hm311 : IsUnit (m3.val 1 1) := by
    have he : m3.val 1 1 = m2.val 1 1 := elementary_row_other k _ _ m2 1 1 (by decide)
    rw [he, ← hv]
    exact v.isUnit
  have hm3 := upperTriangular_mem_elementaryReduction k m3 hm310 hm320 hm321 hm300 hm311
  have ht1 : t1 ∈ (elementaryReduction k).range := transvection_mem_elementaryReduction k _ _
  have ht2 : t2 ∈ (elementaryReduction k).range := transvection_mem_elementaryReduction k _ _
  have ht3 : t3 ∈ (elementaryReduction k).range := transvection_mem_elementaryReduction k _ _
  exact ((elementaryReduction k).range.mul_mem_cancel_left ht1).mp
    (((elementaryReduction k).range.mul_mem_cancel_left ht2).mp
      (((elementaryReduction k).range.mul_mem_cancel_left ht3).mp hm3))

/-- Surjectivity is proved by reduction to level one followed by elimination
inside the kernel of reduction modulo two. -/
theorem elementaryReduction_surjective (k : ℕ) : Function.Surjective (elementaryReduction k) := by
  by_cases hk : k = 0
  · subst k
    exact elementaryReduction_zero_surjective
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  intro q
  obtain ⟨e, he⟩ := elementaryReduction_one_surjective (quotientMap hk1 q)
  let r := (elementaryReduction k e)⁻¹ * q
  have hr : quotientMap hk1 r = 1 := by
    change quotientMap hk1 ((elementaryReduction k e)⁻¹ * q) = 1
    rw [map_mul, map_inv]
    have heq : quotientMap hk1 (elementaryReduction k e) = quotientMap hk1 q := by
      change quotientMap hk1 (reduce k e.val) = _
      rw [quotientMap_reduce]
      exact he
    rw [heq, inv_mul_cancel]
  obtain ⟨f, hf⟩ := mod_two_kernel_mem_elementaryReduction hk1 r hr
  refine ⟨e * f, ?_⟩
  rw [map_mul, hf]
  change elementaryReduction k e * ((elementaryReduction k e)⁻¹ * q) = q
  group

end CoarseAssembly

end

end OAI
