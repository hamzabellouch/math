import OAI.RepresentationTheory.Saxl.BandOrbit

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/
def bandGlue {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) : X →ₗ[ℂ] WordSpace n d where
  toFun x w := L (fun cb => T x cb (leftWord e w)) (rightWord e w)
  map_add' x y := by
    ext w
    simp only [map_add, Pi.add_apply]
    change L ((fun cb => T x cb (leftWord e w)) + (fun cb => T y cb (leftWord e w))) (rightWord e w) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    ext w
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    change L (c • (fun cb => T x cb (leftWord e w))) (rightWord e w) = _
    rw [map_smul]
    rfl

lemma bandGlue_sum {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) (x : X) :
    bandGlue e T L x = ∑ c : Fin b → Fin k, positionProduct e (T x c) (L (Pi.single c 1)) := by
  classical
  ext w
  change L (fun cb => T x cb (leftWord e w)) (rightWord e w) = _
  have he : (fun cb => T x cb (leftWord e w)) =
      ∑ c : Fin b → Fin k, T x c (leftWord e w) • (Pi.single c (1:ℂ) : WordSpace b k) := by
    ext c
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, positionProduct]

lemma bandGlue_equivariant {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (L : Representation.IntertwiningMap (wordRep b k) (wordRep b d))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) :
    bandGlue e T L.toLinearMap (ρ (sumPerm e h q) x) =
      wordRep n d (sumPerm e h q) (bandGlue e T L.toLinearMap x) := by
  ext w
  change L (fun cb => T (ρ (sumPerm e h q) x) cb (leftWord e w)) (rightWord e w) = _
  simp only [hT]
  have he : (fun cb => (wordRep a d h (T x (cb ∘ q))) (leftWord e w)) =
      wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h)) := rfl
  rw [he]
  have hL : L (wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h))) =
      wordRep b d q (L (fun cb => T x cb ((leftWord e w) ∘ h))) :=
    LinearMap.congr_fun (L.isIntertwining' q) _
  rw [hL]
  change L (fun cb => T x cb ((leftWord e w) ∘ h)) ((rightWord e w) ∘ q) =
    L (fun cb => T x cb (leftWord e (w ∘ sumPerm e h q))) (rightWord e (w ∘ sumPerm e h q))
  have hl : leftWord e (w ∘ sumPerm e h q) = (leftWord e w) ∘ h := by
    funext i
    simp [leftWord,sumPerm_left]
  have hr : rightWord e (w ∘ sumPerm e h q) = (rightWord e w) ∘ q := by
    funext i
    simp [rightWord,sumPerm_right]
  rw [hl,hr]

lemma bandGlue_mem {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  exact product_mem_cyclic e v u _ _ (hT x c) (hL _)

/- A module containing every band Specht type of the relevant height detects
any nonzero high-valued colored-band vector. No multiplicity hypothesis is needed. -/
theorem bandGlue_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) := by
  classical
  obtain ⟨x,c,w,hxc⟩ : ∃ x c w, T x c w ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hT0
    ext x c w
    exact hh x c w
  have hv : (fun cb => T x cb w) ≠ (0 : WordSpace b k) := by
    intro hz
    exact hxc (congrFun hz c)
  obtain ⟨L,hL⟩ := word_support_separates (cyclic (wordRep b d) u).toRepresentation hband _ hv
  let L' := (subrepInclusion (cyclic (wordRep b d) u)).comp L
  have hL' : L' (fun cb => T x cb w) ≠ 0 := by
    intro hz
    apply hL
    exact Subtype.ext hz
  obtain ⟨z,hz⟩ : ∃ z, L' (fun cb => T x cb w) z ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hL' (funext hh)
  refine ⟨bandGlue e T L'.toLinearMap, ?_, bandGlue_equivariant e ρ T hT L', ?_⟩
  · intro he
    apply hz
    have hh := congrArg (fun f : X →ₗ[ℂ] WordSpace n d => f x (joinPositions e w z)) he
    change L' (fun cb => T x cb (leftWord e (joinPositions e w z))) (rightWord e (joinPositions e w z)) = 0 at hh
    simpa only [leftWord_join, rightWord_join] using hh
  · exact bandGlue_mem e v u T hTm L'.toLinearMap (fun y => (L y).property)


def coordinateSub (n d : ℕ) (P : (Fin n → Fin d) → Prop) : Submodule ℂ (WordSpace n d) where
  carrier := {x | ∀ w, ¬ P w → x w = 0}
  zero_mem' := by intro w hw; rfl
  add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
  smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero]

lemma positionProduct_sector {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (A : Fin d → Prop) (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ alphabetSub a d A) (hy : y ∈ alphabetSub b d (fun z => ¬A z)) :
    positionProduct e x y ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  intro w hw
  by_contra hn
  apply hw
  have hxy : x (leftWord e w) ≠ 0 ∧ y (rightWord e w) ≠ 0 := mul_ne_zero_iff.mp hn
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,leftWord] using
      (alphabetSub_iff A x).mp hx _ hxy.1 j
  | inr j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,rightWord] using
      (alphabetSub_iff (fun z => ¬A z) y).mp hy _ hxy.2 j

lemma bandGlue_sector {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (A : Fin d → Prop)
    (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d A) (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  apply positionProduct_sector
  · exact cyclic_alphabet A v hv _ (hT x c)
  · exact cyclic_alphabet (fun z => ¬A z) u hu _ (hL _)

theorem bandGlue_sector_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hvA : v ∈ alphabetSub a d A)
    (huA : u ∈ alphabetSub b d (fun z => ¬A z))
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) ∧
      (∀ x, f x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A)) := by
  classical
  obtain ⟨x,c,w,hxc⟩ : ∃ x c w, T x c w ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hT0
    ext x c w
    exact hh x c w
  have hv : (fun cb => T x cb w) ≠ (0 : WordSpace b k) := by
    intro hz
    exact hxc (congrFun hz c)
  obtain ⟨L,hL⟩ := word_support_separates (cyclic (wordRep b d) u).toRepresentation hband _ hv
  let L' := (subrepInclusion (cyclic (wordRep b d) u)).comp L
  have hL' : L' (fun cb => T x cb w) ≠ 0 := by
    intro hz
    apply hL
    exact Subtype.ext hz
  obtain ⟨z,hz⟩ : ∃ z, L' (fun cb => T x cb w) z ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hL' (funext hh)
  refine ⟨bandGlue e T L'.toLinearMap, ?_, bandGlue_equivariant e ρ T hT L', ?_, ?_⟩
  · intro he
    apply hz
    have hh := congrArg (fun f : X →ₗ[ℂ] WordSpace n d => f x (joinPositions e w z)) he
    change L' (fun cb => T x cb (leftWord e (joinPositions e w z))) (rightWord e (joinPositions e w z)) = 0 at hh
    simpa only [leftWord_join, rightWord_join] using hh
  · exact bandGlue_mem e v u T hTm L'.toLinearMap (fun y => (L y).property)

  · exact bandGlue_sector e A v u hvA huA T hTm L'.toLinearMap (fun y => (L y).property)

end Saxl

end

end OAI
