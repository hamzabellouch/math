import OAI.RepresentationTheory.Saxl.CyclicTensor

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

lemma weighted_perm_sum {X : Type uX} [Fintype X] (t a : X → ℝ)
    (g : Equiv.Perm X) (hg : ∀ i, t (g i) = t i) :
    ∑ i, t i * a (g i) = ∑ i, t i * a i := by
  simpa only [hg] using Equiv.sum_comp g (fun i => t i * a i)

/- The strict square-moment equality used in the dominance projection.
The labels may be real; the application uses actual nonnegative integer letters. -/
theorem pair_sum_rigidity {X : Type uX} [Fintype X]
    (a t c : X → ℝ) (ω g h k : Equiv.Perm X)
    (hω : ∀ i, t (ω i) = t i) (hcomp : ∀ i, a i + a (ω i) = t i)
    (hg : ∀ i, t (g i) = t i) (hh : ∀ i, t (h i) = t i)
    (hc : ∀ i, c i = a (g i) + a (h i)) (hk : ∀ i, c i = t (k i)) : c = t := by
  have hbase : 2 * (∑ i, t i * a i) = ∑ i, t i ^ 2 := by
    have he := weighted_perm_sum t a ω hω
    have hs : (∑ i, t i * a i) + (∑ i, t i * a (ω i)) = ∑ i, t i ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, hcomp i, pow_two]
    linarith
  have hcross : ∑ i, t i * c i = ∑ i, t i ^ 2 := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib, weighted_perm_sum t a g hg, weighted_perm_sum t a h hh]
    linarith
  have hsquare : ∑ i, c i ^ 2 = ∑ i, t i ^ 2 := by
    simp only [hk]
    exact Equiv.sum_comp k (fun i => t i ^ 2)
  have hsum : ∑ i, (c i - t i) ^ 2 = 0 := by
    calc
      (∑ i, (c i - t i) ^ 2) = (∑ i, c i ^ 2) - 2 * (∑ i, t i * c i) +
          (∑ i, t i ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hsquare, hcross]; ring
  funext i
  have hz : (c i - t i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j-t j))).mp hsum i
      (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end Saxl

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

def wordOrbit {n d : ℕ} (t : Fin n → Fin d) (c : Fin n → Fin d) : Prop :=
  ∃ g : Equiv.Perm (Fin n), c = t ∘ g

lemma wordOrbit_perm {n d : ℕ} (t c : Fin n → Fin d) (g : Equiv.Perm (Fin n)) :
    wordOrbit t (c ∘ g) ↔ wordOrbit t c := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h*g⁻¹, ?_⟩
    funext i
    have he := congrFun hh (g⁻¹ i)
    simpa using he
  · rintro ⟨h, rfl⟩
    exact ⟨h*g, rfl⟩

def orbitProjection {n d : ℕ} (t : Fin n → Fin d) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n d) where
  toLinearMap := coordinateProjection (wordOrbit t)
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    ext c
    change (if wordOrbit t c then x (c ∘ g) else 0) =
      (if wordOrbit t (c ∘ g) then x (c ∘ g) else 0)
    rw [wordOrbit_perm]

def pairSumMap (n d e : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n e) :=
  wordMap (fun a c => if (finProdFinEquiv.symm a).1.val +
    (finProdFinEquiv.symm a).2.val = c.val then 1 else 0)

lemma wordTensor_single {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordTensor n d e (Pi.single a 1 ⊗ₜ[ℂ] Pi.single b 1) = Pi.single (mergeWords a b) 1 := by
  classical
  ext c
  rw [wordTensor_tmul]
  by_cases h : c = mergeWords a b
  · subst c; simp
  · have hh : splitLeft c ≠ a ∨ splitRight c ≠ b := by
      by_contra hn
      push Not at hn
      exact h (by rw [← merge_split c, hn.1, hn.2])
    rcases hh with hl | hr
    · simp [Pi.single_apply, h, hl]
    · simp [Pi.single_apply, h, hr]

lemma pairSumMap_single {n d e : ℕ} (a b : Fin n → Fin d) (c : Fin n → Fin e) :
    pairSumMap n d e (Pi.single (mergeWords a b) 1) c =
      if ∀ i, (a i).val + (b i).val = (c i).val then 1 else 0 := by
  classical
  rw [pairSumMap, wordMap_single]
  simp only [mergeWords, Equiv.symm_apply_apply]
  by_cases h : ∀ i, (a i).val + (b i).val = (c i).val
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma altWord_inverse_sum {n d : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) :
    letI := Fintype.ofFinite H
    altWord H a = ∑ g : H, signC (g : Equiv.Perm (Fin n)) • Pi.single (a ∘ (g : Equiv.Perm (Fin n))) 1 := by
  classical
  let := Fintype.ofFinite H
  unfold altWord
  simp_rw [wordRep_single]
  apply Eq.trans ?_ (Equiv.sum_comp (Equiv.inv H) _)
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  exact (signC_inv g.val).symm


lemma paired_relation_iff {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    (∀ i, (a (g.val i)).val + (a (h.val i)).val = (t i).val) ↔ h = ω*g := by
  constructor
  · intro hh
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply ha
    apply Prod.ext
    · exact (ht h i).trans ((ht ω (g.val i)).trans (ht g i)).symm
    · apply Fin.ext
      have he := hω (g.val i)
      rw [ht g i] at he
      exact Nat.add_left_cancel ((hh i).trans he.symm)
  · rintro rfl i
    have he := hω (g.val i)
    rw [ht g i] at he
    exact he

lemma paired_term_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  ext c
  change (if wordOrbit t c then pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) c else 0) = _
  rw [pairSumMap_single]
  simp only [Function.comp_apply]
  by_cases he : h = ω*g
  · rw [ite_eq_left he]
    have hr := (paired_relation_iff H a t ω ht ha hω g h).mpr he
    by_cases hc : c = t
    · subst c
      rw [ite_eq_left ⟨1, rfl⟩, ite_eq_left hr]
      simp
    · rw [Pi.single_eq_of_ne hc]
      have hn : ¬ ∀ i, (a (g.val i)).val + (a (h.val i)).val = (c i).val := by
        intro hh
        apply hc
        funext i
        exact Fin.ext ((hh i).symm.trans (hr i))
      simp only [hn, ite_false, ite_self]
  · rw [ite_eq_right he]
    change (if wordOrbit t c then _ else _) = (0:ℂ)
    by_cases ho : wordOrbit t c
    · rw [ite_eq_left ho]
      apply ite_eq_right
      intro hh
      obtain ⟨k,hk⟩ := ho
      have heq : (fun i => ((c i).val : ℝ)) = fun i => ((t i).val : ℝ) := by
        apply pair_sum_rigidity (fun i => ((a i).val : ℝ)) (fun i => ((t i).val : ℝ))
          (fun i => ((c i).val : ℝ)) ω.val g.val h.val k
        · intro i; rw [ht ω i]
        · intro i; exact_mod_cast hω i
        · intro i; rw [ht g i]
        · intro i; rw [ht h i]
        · intro i; exact_mod_cast (hh i).symm
        · intro i; rw [hk]; rfl
      have hct : c = t := by
        funext i
        apply Fin.ext
        exact_mod_cast congrFun heq i
      rw [hct] at hh
      exact he ((paired_relation_iff H a t ω ht ha hω g h).mp hh)
    · rw [ite_eq_right ho]

theorem repeated_alt_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by
  classical
  let := Fintype.ofFinite H
  rw [altWord_inverse_sum, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul_smul, map_smul,
    wordTensor_single, paired_term_projection H a t ω ht ha hω]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs (g : H) : signC g.val * signC (ω*g).val = signC ω.val := by
    simp only [Subgroup.coe_mul, map_mul]
    calc
      signC g.val * (signC ω.val * signC g.val) = signC ω.val * (signC g.val * signC g.val) := by ring
      _ = signC ω.val := by rw [signC_mul_self, mul_one]
  simp only [hs, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_eq_nat_card]

end Saxl

end

end OAI
