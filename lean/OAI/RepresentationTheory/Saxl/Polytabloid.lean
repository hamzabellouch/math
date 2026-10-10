import OAI.RepresentationTheory.Saxl.Basic

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- A finite set is the unique maximizer of its strictly signed separator.
Used below for the Ferrers equality case in the Specht submodule theorem. -/
lemma finset_eq_of_signed_sum {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  classical
  let f := fun x => if x ∈ A then w x else 0
  let g := fun x => if x ∈ B then w x else 0
  have hle : ∀ x ∈ A ∪ B, f x ≤ g x := by
    intro x hx
    dsimp [f, g]
    split_ifs with ha hb hb
    · rfl
    · exact (hn x hb).le
    · exact (hp x hb).le
    · rfl
  have hs : ∑ x ∈ A ∪ B, f x = ∑ x ∈ A ∪ B, g x := by
    simpa [f, g, ← Finset.sum_filter] using he
  have hh := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  ext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
  · simp [ha, hb]
  · have hx := hh x (Finset.mem_union_left B ha)
    have hneg := hn x hb
    simp [f, g, ha, hb] at hx
    omega
  · have hx := hh x (Finset.mem_union_right A hb)
    have hpos := hp x hb
    simp [f, g, ha, hb] at hx
    omega
  · simp [ha, hb]

/- A column-injective rearrangement of the canonical row word has precisely
Ferrers support. This is the equality-of-margins argument, without using
unproved Specht or Young-rule inputs. -/
lemma ferrers_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∀ i, ((t (g i)).val.1, (t i).val.2) ∈ μ := by
  classical
  let f : Fin n → ℕ × ℕ := fun i => ((t (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => 2 * (μ.rowLen c.1 : ℤ) - 2 * c.2 - 1
  have ht : Function.Injective (fun i : Fin n => (t i).val) :=
    Subtype.val_injective.comp t.injective
  have himage : Finset.univ.image (fun i : Fin n => (t i).val) = μ.cells := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (t i).property
    · intro hx
      exact ⟨t.symm ⟨x, hx⟩, by simp⟩
  have he : ∑ x ∈ Finset.univ.image f, w x = ∑ x ∈ μ.cells, w x := by
    rw [← himage, Finset.sum_image (fun _ _ _ _ h => hinj h),
      Finset.sum_image (fun _ _ _ _ h => ht h)]
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Equiv.sum_comp g (fun i => (μ.rowLen (t i).val.1 : ℤ))]
  have heq := finset_eq_of_signed_sum (Finset.univ.image f) μ.cells w
    (fun c hc => by
      have h := YoungDiagram.mem_iff_lt_rowLen.mp hc
      dsimp [w]
      omega)
    (fun c hc => by
      have h : μ.rowLen c.1 ≤ c.2 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_rowLen.mpr h))
      dsimp [w]
      omega) he
  intro i
  exact (le_of_eq heq) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/- The complex-valued sign character. -/
def signC {n : ℕ} : Equiv.Perm (Fin n) →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp Equiv.Perm.sign

@[simp] lemma signC_def {n : ℕ} (g : Equiv.Perm (Fin n)) :
    signC g = (((Equiv.Perm.sign g) : ℤ) : ℂ) := rfl

@[simp] lemma signC_inv {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g⁻¹ = signC g := by
  simp [signC_def, Equiv.Perm.sign_inv]

@[simp] lemma signC_mul_self {n : ℕ} (g : Equiv.Perm (Fin n)) : signC g * signC g = 1 := by
  calc signC g * signC g = signC (g⁻¹ * g) := by rw [map_mul, signC_inv]
       _ = 1 := by rw [inv_mul_cancel, map_one]

lemma wordRep_single {n d : ℕ} (g : Equiv.Perm (Fin n)) (a : Fin n → Fin d) :
    wordRep n d g (Pi.single a 1) = Pi.single (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) (1 : ℂ) := by
  classical
  ext b
  change (Pi.single a (1 : ℂ) : WordSpace n d) (b ∘ g) = _
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have hh := congrFun h (g⁻¹ i)
    simpa using hh
  · intro h
    funext i
    have hh := congrFun h (g i)
    simpa using hh

/- Actual column antisymmetrizer on the word-coordinate module. -/
def columnAlt {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Module.End ℂ (WordSpace n d) := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n d (g : Equiv.Perm (Fin n))

lemma columnAlt_mul {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulRight h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((g * h : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((g * h : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  congr 1
  calc signC (h : Equiv.Perm (Fin n)) *
      (signC (g : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) =
      signC (g : Equiv.Perm (Fin n)) *
        (signC (h : Equiv.Perm (Fin n)) * signC (h : Equiv.Perm (Fin n))) := by ring
    _ = signC (g : Equiv.Perm (Fin n)) := by rw [signC_mul_self, mul_one]

lemma columnAlt_row {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    columnAlt t (Pi.single (rowWord t) 1) = polytabloid t := by
  simp [columnAlt, polytabloid, LinearMap.sum_apply]

/- Construction of the witnessing column rearrangement. -/
lemma column_rearrangement {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n))
    (hinj : Function.Injective (fun i => ((t (g i)).val.1, (t i).val.2))) :
    ∃ h : columnGroup t, rowWord t ∘ g = rowWord t ∘ (h : Equiv.Perm (Fin n)) := by
  classical
  let f : Fin n → Fin n := fun i =>
    t.symm ⟨((t (g i)).val.1, (t i).val.2), ferrers_rearrangement t g hinj i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    have hh := congrArg (fun k => (t k).val) hij
    simpa [f] using hh
  let h : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hcol : h ∈ columnGroup t := by
    intro i
    change (t (f i)).val.2 = _
    simp [f]
  refine ⟨⟨h, hcol⟩, ?_⟩
  funext i
  apply Fin.ext
  change (t (g i)).val.1 = (t (f i)).val.1
  simp [f]

lemma columnAlt_collision {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
  classical
  let h : columnGroup t := ⟨Equiv.swap i j, fun k => Equiv.apply_swap_eq_self (v := fun l => (t l).val.2) hc k⟩
  have hs : signC (h : Equiv.Perm (Fin n)) = -1 := by
    simp [h, signC_def, Equiv.Perm.sign_swap hij]
  have hf : wordRep n d (h : Equiv.Perm (Fin n)) (Pi.single a 1) = Pi.single a 1 := by
    rw [wordRep_single]
    congr 1
    funext k
    exact Equiv.apply_swap_eq_self ha k
  have hh := congrArg (fun f : Module.End ℂ (WordSpace n d) => f (Pi.single a 1))
    (columnAlt_mul (d := d) t h)
  simp only [Module.End.mul_apply, hf, LinearMap.smul_apply, hs, neg_one_smul] at hh
  ext b
  exact CharZero.eq_neg_self_iff.mp (congrFun hh b)

lemma columnAlt_column {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt t (Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1) =
      signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  classical
  have he : wordRep n (μ.colLen 0) ((h⁻¹ : columnGroup t) : Equiv.Perm (Fin n))
      (Pi.single (rowWord t) 1) =
      Pi.single (rowWord t ∘ (h : Equiv.Perm (Fin n))) 1 := by
    rw [wordRep_single]
    simp only [Subgroup.coe_inv, inv_inv]
  rw [← he, ← Module.End.mul_apply, columnAlt_mul, LinearMap.smul_apply,
    columnAlt_row, Subgroup.coe_inv, signC_inv]

lemma columnAlt_single {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    columnAlt t (Pi.single (rowWord t ∘ g) 1) ∈
      Submodule.span ℂ {polytabloid t} := by
  classical
  by_cases hi : Function.Injective (fun i : Fin n => ((t (g i)).val.1, (t i).val.2))
  · obtain ⟨h, hh⟩ := column_rearrangement t g hi
    rw [hh, columnAlt_column]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨i, j, hc, hij⟩ := hi
    have ha : (rowWord t ∘ g) i = (rowWord t ∘ g) j := by
      apply Fin.ext
      have hh := congrArg Prod.fst hc
      exact hh
    have hcol := congrArg Prod.snd hc
    rw [columnAlt_collision t _ i j hij hcol ha]
    exact Submodule.zero_mem _

end Saxl

end

end OAI
