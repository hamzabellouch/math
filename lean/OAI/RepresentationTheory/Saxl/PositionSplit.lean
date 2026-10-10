import OAI.RepresentationTheory.Saxl.CoordinateSector

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/
def sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) : Equiv.Perm (Fin n) :=
  e.symm.permCongr (Equiv.sumCongr g h)

lemma signC_sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    signC (sumPerm e g h) = signC g * signC h := by
  simp [signC_def, sumPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

@[simp] lemma sumPerm_left {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin a) :
    sumPerm e g h (e.symm (Sum.inl i)) = e.symm (Sum.inl (g i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

@[simp] lemma sumPerm_right {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin b) :
    sumPerm e g h (e.symm (Sum.inr i)) = e.symm (Sum.inr (h i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

def leftWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin a → Fin d :=
  fun i => w (e.symm (Sum.inl i))

def rightWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin b → Fin d :=
  fun i => w (e.symm (Sum.inr i))

lemma word_eq_iff_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) : w = v ↔ leftWord e w = leftWord e v ∧ rightWord e w = rightWord e v := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨h₁,h₂⟩
    funext i
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    cases k with
    | inl k => exact congrFun h₁ k
    | inr k => exact congrFun h₂ k

def positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) : WordSpace n d :=
  fun w => x (leftWord e w) * y (rightWord e w)

lemma single_positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) :
    (Pi.single w (1:ℂ) : WordSpace n d) =
      positionProduct e (Pi.single (leftWord e w) 1) (Pi.single (rightWord e w) 1) := by
  classical
  ext v
  simp only [positionProduct, Pi.single_apply]
  simp only [word_eq_iff_parts e]
  split_ifs <;> simp_all

lemma altWord_split_term {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    (signC (sumPerm e g h) • wordRep n d (sumPerm e g h) (Pi.single w 1)) v =
    (signC g • wordRep a d g (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC h • wordRep b d h (Pi.single (rightWord e w) 1)) (rightWord e v) := by
  rw [single_positionProduct e w]
  change signC (sumPerm e g h) *
    ((Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e (v ∘ sumPerm e g h)) *
      (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e (v ∘ sumPerm e g h))) = _
  have h₁ : leftWord e (v ∘ sumPerm e g h) = leftWord e v ∘ g := by
    ext i; simp [leftWord]
  have h₂ : rightWord e (v ∘ sumPerm e g h) = rightWord e v ∘ h := by
    ext i; simp [rightWord]
  rw [h₁,h₂,signC_sumPerm]
  change _ = (signC g * (Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e v ∘ g)) *
    (signC h * (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e v ∘ h))
  ring

/- Independent block permutations factor with exactly the product sign. -/
theorem altWord_split {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (G : Subgroup (Equiv.Perm (Fin n))) (G₁ : Subgroup (Equiv.Perm (Fin a)))
    (G₂ : Subgroup (Equiv.Perm (Fin b))) (E : G ≃ G₁ × G₂)
    (hE : ∀ g : G, (g : Equiv.Perm (Fin n)) =
      sumPerm e ((E g).1 : Equiv.Perm (Fin a)) ((E g).2 : Equiv.Perm (Fin b)))
    (w : Fin n → Fin d) :
    altWord G w = positionProduct e (altWord G₁ (leftWord e w)) (altWord G₂ (rightWord e w)) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G₁
  let := Fintype.ofFinite G₂
  ext v
  unfold altWord
  simp only [Finset.sum_apply, positionProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : G₁ × G₂,
      (signC (p.1 : Equiv.Perm (Fin a)) • wordRep a d p.1 (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC (p.2 : Equiv.Perm (Fin b)) • wordRep b d p.2 (Pi.single (rightWord e w) 1)) (rightWord e v) := by
        apply Fintype.sum_equiv E
        intro g
        rw [hE g]
        exact altWord_split_term e w v _ _
    _ = _ := Fintype.sum_prod_type _



def fiberGroup {n : ℕ} {α : Type uAlpha} (f : Fin n → α) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, f (g i) = f i}
  one_mem' _ := rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

def leftPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin a ≃ {i : Fin n // (e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inl i), by simp⟩
  invFun i := (e i.val).getLeft i.property
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inl_getLeft _ _

def rightPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin b ≃ {i : Fin n // ¬(e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inr i), by simp⟩
  invFun i := (e i.val).getRight (by
    have hi := i.property
    cases h : e i.val <;> simp_all)
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inr_getRight _ _

def leftRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin a) :=
  (leftPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm g.property)

def rightRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin b) :=
  (rightPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm (fun i => not_congr (g.property i)))

lemma leftRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin a) :
    e.symm (Sum.inl (leftRestriction e g i)) = g.val (e.symm (Sum.inl i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inl_getLeft _ _

lemma rightRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin b) :
    e.symm (Sum.inr (rightRestriction e g i)) = g.val (e.symm (Sum.inr i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inr_getRight _ _

lemma sumPerm_restrictions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) :
    sumPerm e (leftRestriction e g) (rightRestriction e g) = g.val := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j => simpa using leftRestriction_apply e g j
  | inr j => simpa using rightRestriction_apply e g j

lemma sumPerm_injective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Injective (fun p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b) => sumPerm e p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inl i)))) hpq
    simpa using h
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inr i)))) hpq
    simpa using h

def fiberSplit {n a b : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin n → α) :
    (fiberGroup (fun i => f (e.symm (Sum.inl i)))) × (fiberGroup (fun i => f (e.symm (Sum.inr i)))) ≃
      ↥(fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) := by
  let F : (fiberGroup (fun i => f (e.symm (Sum.inl i)))) ×
      (fiberGroup (fun i => f (e.symm (Sum.inr i)))) →
      ↥(fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) := fun p =>
    ⟨sumPerm e p.1.val p.2.val, by
      constructor
      · intro i
        obtain ⟨j,rfl⟩ := e.symm.surjective i
        cases j with
        | inl j => simpa using p.1.property j
        | inr j => simpa using p.2.property j
      · intro i
        obtain ⟨j,rfl⟩ := e.symm.surjective i
        cases j <;> simp⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q hpq
    have hh : sumPerm e p.1.val p.2.val = sumPerm e q.1.val q.2.val := congrArg Subtype.val hpq
    have h := @sumPerm_injective n a b e (p.1.val,p.2.val) (q.1.val,q.2.val) hh
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  · intro g
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g.val,g.property.2⟩
    refine ⟨(⟨leftRestriction e g', ?_⟩, ⟨rightRestriction e g', ?_⟩), ?_⟩
    · intro i
      dsimp only
      rw [leftRestriction_apply]
      exact g.property.1 _
    · intro i
      dsimp only
      rw [rightRestriction_apply]
      exact g.property.1 _
    · exact Subtype.ext (sumPerm_restrictions e g')

lemma fiberSplit_apply {n a b : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin n → α)
    (p : (fiberGroup (fun i => f (e.symm (Sum.inl i)))) × (fiberGroup (fun i => f (e.symm (Sum.inr i))))) :
    (fiberSplit e f p).val = sumPerm e p.1.val p.2.val := rfl

/- Exact independent-block factorization for arbitrary row/column labels. -/
theorem altWord_fiber_split {n a b d : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Fin n → α) (w : Fin n → Fin d) :
    altWord (fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) w =
      positionProduct e
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inl i)))) (leftWord e w))
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inr i)))) (rightWord e w)) := by
  apply altWord_split e _ _ _ (fiberSplit e f).symm
  intro g
  exact (congrArg Subtype.val ((fiberSplit e f).apply_symm_apply g)).symm


@[simp] lemma staircase_colLen (m j : ℕ) : (staircase m).colLen j = m-j := by
  have hh : ∀ i, i < (staircase m).colLen j ↔ i < m-j := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).colLen j)
  have h₂ := hh (m-j)
  omega

end Saxl

end

end OAI
