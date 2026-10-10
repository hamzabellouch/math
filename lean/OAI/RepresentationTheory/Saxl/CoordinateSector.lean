import OAI.RepresentationTheory.Saxl.HighProjection

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
def coordinateProjection {n d : ℕ} (P : (Fin n → Fin d) → Prop) :
    Module.End ℂ (WordSpace n d) := by
  classical
  exact {
    toFun := fun x a => if P a then x a else 0
    map_add' := by intros; funext a; by_cases h : P a <;> simp [h]
    map_smul' := by intros; funext a; by_cases h : P a <;> simp [h] }

@[simp] lemma coordinateProjection_apply {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P x a = if P a then x a else 0 := by
  classical
  by_cases h : P a <;> simp [coordinateProjection, h]

lemma coordinateProjection_single {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P (Pi.single a 1) = if P a then Pi.single a 1 else 0 := by
  classical
  ext b
  by_cases he : b = a
  · subst b; by_cases h : P a <;> simp [h]
  · by_cases h : P a <;> simp [he, h]

/- Permutations preserving a position sector. -/
def sectorGroup {n : ℕ} (D : Fin n → Prop) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, D (g i) ↔ D i}
  one_mem' _ := Iff.rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

/- The genuine unnormalized signed block alternation. -/
def altWord {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    WordSpace n d := by
  classical
  letI := Fintype.ofFinite G
  exact ∑ g : G, signC (g : Equiv.Perm (Fin n)) •
    wordRep n d (g : Equiv.Perm (Fin n)) (Pi.single a 1)

lemma altWord_move {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (r : G) :
    altWord G (a ∘ (r : Equiv.Perm (Fin n))) =
      signC (r : Equiv.Perm (Fin n)) • altWord G a := by
  classical
  let := Fintype.ofFinite G
  have he : Pi.single (a ∘ (r : Equiv.Perm (Fin n))) (1 : ℂ) =
      wordRep n d (r⁻¹ : G) (Pi.single a 1) := by
    rw [wordRep_single]
    rfl
  unfold altWord
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, Finset.smul_sum]
  apply (Equiv.sum_comp (Equiv.mulRight r) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC ((g*r : G) : Equiv.Perm (Fin n)) •
    wordRep n d (((g*r : G) : Equiv.Perm (Fin n)) * (r : Equiv.Perm (Fin n))⁻¹) (Pi.single a 1) = _
  simp only [Subgroup.coe_mul, map_mul, mul_inv_cancel_right, smul_smul]
  rw [mul_comm (signC (g : Equiv.Perm (Fin n)))]

/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
theorem altWord_sector {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop)
    (ha : ∀ i, Q (a i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      altWord (G ⊓ sectorGroup D) a := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite ↥(G ⊓ sectorGroup D)
  have hh (g : G) :
      (∀ i, Q ((a ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) i) ↔ D i) ↔
        (g : Equiv.Perm (Fin n)) ∈ sectorGroup D := by
    constructor
    · intro h i
      have h' := (ha _).symm.trans (h ((g : Equiv.Perm (Fin n)) i))
      simpa using h'.symm
    · intro h i
      exact (ha _).trans (by simpa using (h (((g : Equiv.Perm (Fin n))⁻¹) i)).symm)
  unfold altWord
  simp only [map_sum, map_smul, wordRep_single, coordinateProjection_single, hh, smul_ite, smul_zero]
  let e : {g : G // (g : Equiv.Perm (Fin n)) ∈ sectorGroup D} ≃ ↥(G ⊓ sectorGroup D) := {
    toFun := fun g => ⟨g.val.val, g.val.property, g.property⟩
    invFun := fun g => ⟨⟨g.val, g.property.1⟩, g.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Finset.sum_filter]
  rw [← Finset.sum_attach]
  apply Fintype.sum_equiv ?_ _ _ ?_
  · exact (Equiv.subtypeEquivRight (fun g => by simp)).trans e
  · intro g
    rfl

end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/
def stairHigh (h s : ℕ) (i : Fin (staircase (h+s)).card) : Prop :=
  (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h

lemma staircase_projected_sector (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
    coordinateProjection (fun w => (∀ i, s ≤ (splitLeft w i).val ↔ stairHigh h s i) ∧
      (∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i)) (staircaseWord (h+s)) := by
  classical
  ext w
  by_cases he : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val
  · by_cases hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0
    · have hw' : staircaseWord (h+s) w = 0 := by simpa [sameHighProjection, he] using hw
      simp [hw, hw']
    · have hD := staircase_projected_high_positions h s w hw
      have hD' : ∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i :=
        fun i => (he i).symm.trans (hD i)
      simp [sameHighProjection, he, hD', stairHigh]
  · have hn : ¬ ((∀ i, s ≤ (splitLeft w i).val ↔ stairHigh h s i) ∧
        (∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i)) := by
      rintro ⟨h₁,h₂⟩
      exact he (fun i => (h₁ i).trans (h₂ i).symm)
    simp [sameHighProjection, he, hn]

lemma coordinateProjection_tensor {n d e : ℕ}
    (P : (Fin n → Fin d) → Prop) (Q : (Fin n → Fin e) → Prop)
    (x : WordSpace n d) (y : WordSpace n e) :
    coordinateProjection (fun w => P (splitLeft w) ∧ Q (splitRight w))
      (wordTensor n d e (x ⊗ₜ[ℂ] y)) =
    wordTensor n d e (coordinateProjection P x ⊗ₜ[ℂ] coordinateProjection Q y) := by
  classical
  ext w
  by_cases hp : P (splitLeft w) <;> by_cases hq : Q (splitRight w) <;>
    simp [hp,hq]

lemma altWord_sector_rotated {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop) (r : G)
    (ha : ∀ i, Q ((a ∘ (r : Equiv.Perm (Fin n))) i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      signC (r : Equiv.Perm (Fin n)) • altWord (G ⊓ sectorGroup D) (a ∘ (r : Equiv.Perm (Fin n))) := by
  have hh := altWord_sector G (a ∘ (r : Equiv.Perm (Fin n))) Q D ha
  rw [altWord_move, map_smul] at hh
  rw [← hh, smul_smul, signC_mul_self, one_smul]

lemma polytabloid_eq_altWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t = altWord (columnGroup t) (rowWord t) := rfl

/- The cut's two layers, with their exact retained row and column permutations. -/
def cutRowWord (h s : ℕ) :=
  altWord (columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _))

def cutColumnWord (h s : ℕ) :=
  altWord (columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _))

lemma rotatePositions_sign (h s : ℕ) :
    signC (rotateColumnPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) =
      signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) := by
  let q : Equiv.Perm (Fin (staircase (h+s)).card) :=
    ((stairTableau (h+s)).trans (staircaseSwap (h+s))).trans (stairTableau (h+s)).symm
  have he : (rotateColumnPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) =
      q * (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * q := by
    ext i
    simp [q, rotateColumnPositions, rotateRowPositions, rotateColumn]
  rw [he, map_mul, map_mul]
  calc
    signC q * signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * signC q =
      signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * (signC q * signC q) := by ring
    _ = _ := by rw [signC_mul_self, mul_one]

/- Exact sign cancellation in the two retained layers. -/
theorem staircase_cut_layers (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      wordTensor _ _ _ (cutRowWord h s ⊗ₜ[ℂ] cutColumnWord h s) := by
  rw [staircase_projected_sector, staircaseWord]
  rw [coordinateProjection_tensor
    (fun a : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0) =>
      ∀ i, s ≤ (a i).val ↔ stairHigh h s i)
    (fun a : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0) =>
      ∀ i, s ≤ (a i).val ↔ stairHigh h s i)]
  have hr := altWord_sector_rotated (columnGroup (stairRowTableau (h+s)))
    (rowWord (stairRowTableau (h+s))) (fun a => s ≤ a.val) (stairHigh h s)
    (rotateRowPositions h s) (by
      intro i
      simpa [rowWord, stairRowTableau, rotateRowPositions, stairHigh, staircaseSwap] using
        rotateRow_high h s (stairTableau (h+s) i))
  have hc := altWord_sector_rotated (columnGroup (stairTableau (h+s)))
    (rowWord (stairTableau (h+s))) (fun a => s ≤ a.val) (stairHigh h s)
    (rotateColumnPositions h s) (by
      intro i
      simpa [rowWord, rotateColumnPositions, stairHigh] using
        rotateColumn_high h s (stairTableau (h+s) i))
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord, hr, hc]
  rw [TensorProduct.smul_tmul_smul, rotatePositions_sign, signC_mul_self, one_smul]
  rfl

end Saxl

end

end OAI
