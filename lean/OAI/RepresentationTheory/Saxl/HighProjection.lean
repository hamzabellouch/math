import OAI.RepresentationTheory.Saxl.StaircaseTensor

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
def highRowEquiv (h s : ℕ) :
    {x : (staircase (h+s)).cells // s ≤ x.val.2} ≃ (staircase h).cells where
  toFun x := ⟨(x.val.val.1, x.val.val.2 - s), by
    have hx : x.val.val.1 + x.val.val.2 < h+s := mem_staircase.mp x.val.property
    exact mem_staircase.mpr (by have := x.property; omega)⟩
  invFun x := ⟨⟨(x.val.1, x.val.2+s), by
    have hx : x.val.1 + x.val.2 < h := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩, by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := x.property
    ext <;> omega
  right_inv x := by apply Subtype.ext; simp

def highColEquiv (h s : ℕ) :
    {x : (staircase (h+s)).cells // s ≤ x.val.1} ≃ (staircase h).cells where
  toFun x := ⟨(x.val.val.1 - s, x.val.val.2), by
    have hx : x.val.val.1 + x.val.val.2 < h+s := mem_staircase.mp x.val.property
    exact mem_staircase.mpr (by have := x.property; omega)⟩
  invFun x := ⟨⟨(x.val.1+s, x.val.2), by
    have hx : x.val.1 + x.val.2 < h := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩, by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := x.property
    ext <;> omega
  right_inv x := by apply Subtype.ext; simp

theorem high_positions_rigidity (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by
  classical
  let A : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => s ≤ (g x).val.2)
  let B : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => x.val.1 + x.val.2 < h)
  let eR : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and])).trans
      (highRowEquiv h s)
  let eC : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv k (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc x)).trans
      (highColEquiv h s)
  let eB : B ≃ (staircase h).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa [B] using x.property)⟩
      invFun := fun x => ⟨⟨x.val, mem_staircase.mpr (by
        have hx := mem_staircase.mp x.property; omega)⟩, by simp [B, mem_staircase.mp x.property]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simpa [eR, eB, highRowEquiv, hg] using hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simpa [eC, eB, highColEquiv, hk] using hC.trans hB.symm
  let w := fun x : (staircase (h+s)).cells =>
    2 * (h : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this


lemma polytabloid_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (ha : polytabloid t a ≠ 0) :
    ∃ g : columnGroup t, a = rowWord t ∘ (g : Equiv.Perm (Fin n)) := by
  classical
  have hex : ∃ g : columnGroup t, a ∘ (g : Equiv.Perm (Fin n)) = rowWord t := by
    by_contra! hh
    apply ha
    unfold polytabloid
    simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
    simp [hh]
  obtain ⟨g, hg⟩ := hex
  refine ⟨g⁻¹, ?_⟩
  funext i
  have he := congrFun hg ((g : Equiv.Perm (Fin n))⁻¹ i)
  simpa using he

/- Local same-high projection in the ordinary pair-letter coordinate space. -/
def sameHighProjection (n d e s : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*e)) (wordRep n (d*e)) where
  toFun z w := if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val) then z w else 0
  map_add' z y := by ext w; dsimp; split_ifs <;> simp
  map_smul' c z := by ext w; dsimp; split_ifs <;> simp
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    funext w
    change (if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val) then z (w ∘ g) else 0) =
      (if (∀ i, s ≤ (splitLeft (w ∘ g) i).val ↔ s ≤ (splitRight (w ∘ g) i).val) then z (w ∘ g) else 0)
    congr 1
    apply propext
    exact (g.forall_congr_right).symm

theorem staircase_projected_high_positions (h s : ℕ)
    (w : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0))
    (hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w ≠ 0) :
    ∀ i, s ≤ (splitLeft w i).val ↔
      ((stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h) := by
  classical
  have heq : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    by_contra hh
    apply hw
    simp [sameHighProjection, hh]
  have hww : staircaseWord (h+s) w ≠ 0 := by
    simpa [sameHighProjection, heq] using hw
  have hp : polytabloid (stairRowTableau (h+s)) (splitLeft w) *
      polytabloid (stairTableau (h+s)) (splitRight w) ≠ 0 := by
    simpa only [staircaseWord, wordTensor_tmul] using hww
  obtain ⟨g, hg⟩ := polytabloid_support (stairRowTableau (h+s)) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨k, hk⟩ := polytabloid_support (stairTableau (h+s)) _ (mul_ne_zero_iff.mp hp).2
  let t := stairTableau (h+s)
  let gc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (g : Equiv.Perm _)).trans t
  let kc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (k : Equiv.Perm _)).trans t
  have hgc : ∀ x, (gc x).val.1 = x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm _) (t.symm x))).val.1 = (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hkc : ∀ x, (kc x).val.2 = x.val.2 := by
    intro x
    have hh := k.property (t.symm x)
    change (t ((k : Equiv.Perm _) (t.symm x))).val.2 = (t (t.symm x)).val.2 at hh
    simpa [kc] using hh
  have hcommon : ∀ x, s ≤ (gc x).val.2 ↔ s ≤ (kc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg, hk] at hh
    exact hh
  have hr := high_positions_rigidity h s gc kc hgc hkc hcommon
  intro i
  have hh := hr (t i)
  rw [hg]
  simpa [gc, t, rowWord, stairRowTableau, staircaseSwap] using hh


lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/
def rotateRowCell (h s : ℕ) (x : (staircase (h+s)).cells) : (staircase (h+s)).cells :=
  ⟨(x.val.1, if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)), by
    have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
    apply mem_staircase.mpr
    split_ifs <;> omega⟩

lemma rotateRowCell_injective (h s : ℕ) : Function.Injective (rotateRowCell h s) := by
  intro x y he
  have hi0 := congrArg (fun z : (staircase (h+s)).cells => z.val.1) he
  have hi : x.val.1 = y.val.1 := hi0
  have hj := congrArg (fun z : (staircase (h+s)).cells => z.val.2) he
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  have hy : y.val.1 + y.val.2 < h+s := mem_staircase.mp y.property
  dsimp [rotateRowCell] at hj
  apply Subtype.ext
  apply Prod.ext hi
  split_ifs at hj <;> omega

def rotateRow (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  Equiv.ofBijective (rotateRowCell h s) (⟨rotateRowCell_injective h s, Finite.surjective_of_injective (rotateRowCell_injective h s)⟩)

lemma rotateRow_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  change s ≤ (if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)) ↔ _
  split_ifs <;> omega

def rotateColumn (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  ((staircaseSwap (h+s)).trans (rotateRow h s)).trans (staircaseSwap (h+s))

lemma rotateColumn_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateColumn h s x).val.1 ↔ x.val.1 + x.val.2 < h := by
  have hh := rotateRow_high h s (staircaseSwap (h+s) x)
  change s ≤ (rotateRow h s (staircaseSwap (h+s) x)).val.2 ↔ _
  simpa [staircaseSwap, Nat.add_comm] using hh

def rotateRowPositions (h s : ℕ) : columnGroup (stairRowTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateRow h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateRow h s (stairTableau (h+s) i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def rotateColumnPositions (h s : ℕ) : columnGroup (stairTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateColumn h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateColumn h s (stairTableau (h+s) i)))).val.2 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

lemma polytabloid_column_coeff {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) :
    polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) = signC (g : Equiv.Perm (Fin n)) := by
  have hh := congrFun (polytabloid_alternating t g) (rowWord t)
  change polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) =
    signC (g : Equiv.Perm (Fin n)) * polytabloid t (rowWord t) at hh
  simpa [polytabloid_rowWord] using hh

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
theorem staircase_projected_ne_zero (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) ≠ 0 := by
  classical
  let a := rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)
  let b := rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)
  let w := mergeWords a b
  have ha (i) : s ≤ (a i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateRow_high h s (stairTableau (h+s) i)
    simpa [a, rowWord, stairRowTableau, rotateRowPositions, staircaseSwap] using hh
  have hb (i) : s ≤ (b i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateColumn_high h s (stairTableau (h+s) i)
    simpa [b, rowWord, rotateColumnPositions] using hh
  have hp : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    intro i
    simp only [w, splitLeft_merge, splitRight_merge]
    exact (ha i).trans (hb i).symm
  intro hz
  have he := congrFun hz w
  change sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0 at he
  simp only [sameHighProjection, Representation.IntertwiningMap.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, staircaseWord, wordTensor_tmul, w, splitLeft_merge, splitRight_merge,
    a, b, polytabloid_column_coeff] at he
  have hn (g : Equiv.Perm (Fin (staircase (h+s)).card)) : signC g ≠ 0 := by
    intro hz
    have hh := signC_mul_self g
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hpab : ∀ i, s ≤ (a i).val ↔ s ≤ (b i).val := fun i => (ha i).trans (hb i).symm
  rw [ite_eq_left hpab] at he
  exact mul_ne_zero (hn _) (hn _) he

end Saxl

end

end OAI
