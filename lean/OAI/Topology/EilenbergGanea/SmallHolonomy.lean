import OAI.Topology.EilenbergGanea.WordEquations
import OAI.GroupTheory.RightAngledArtin.ResidualFiniteness
import Mathlib.Topology.Compactness.Compact
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion ContDiff
/-- Squared chord length on the unit-quaternion sphere. -/
theorem su2_distance_square (a : SU2) :
    ‖(a : ℍ) - 1‖ ^ 2 = 2 - 2 * (a : ℍ).re := by
  have hu := (quaternion_mem_unitary_iff _).mp a.property
  have hs : Quaternion.normSq ((a : ℍ) - 1) = Quaternion.normSq (a : ℍ) + 1 - 2 * (a : ℍ).re := by
    simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_one,
      Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    ring
  simpa only [Quaternion.normSq_eq_norm_mul_self, hu, one_mul, sq, one_add_one_eq_two] using hs

def arcBlend (a : SU2) (t : ℝ) : ℍ :=
  (1 - Real.smoothTransition t) • (1 : ℍ) + Real.smoothTransition t • (a : ℍ)

theorem arcBlend_norm_le (a : SU2) (t : ℝ) : ‖arcBlend a t‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  have hn := (quaternion_mem_unitary_iff _).mp a.property
  calc
    _ ≤ ‖(1 - Real.smoothTransition t) • (1 : ℍ)‖ +
        ‖Real.smoothTransition t • (a : ℍ)‖ := norm_add_le _ _
    _ = 1 := by rw [norm_smul, norm_smul, norm_one, hn, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg h0]; ring

theorem small_unit_re (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) :
    0 < (a : ℍ).re ∧ (a : ℍ).re ≤ 1 := by
  have h := su2_distance_square a
  have hn := norm_nonneg ((a : ℍ) - 1)
  constructor <;> nlinarith [sq_nonneg ‖(a : ℍ) - 1‖]

theorem arcBlend_re_le (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) (t : ℝ) :
    (a : ℍ).re ≤ (arcBlend a t).re := by
  have h := (small_unit_re a ha).2
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  simp only [arcBlend, Quaternion.re_add, Quaternion.re_smul, Quaternion.re_one, smul_eq_mul]
  nlinarith

theorem arcBlend_ne_zero (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) (t : ℝ) :
    arcBlend a t ≠ 0 := by
  have h := (small_unit_re a ha).1.trans_le (arcBlend_re_le a ha t)
  intro he
  simp only [he, Quaternion.re_zero, lt_self_iff_false] at h

/-- A globally smooth path that remains in the closed chord ball of its
endpoint, avoiding any branch choice of a quaternion logarithm. -/
def smallQuaternionArc (a : SU2) (t : ℝ) : SU2 := normalizeQuaternion (arcBlend a t)

@[simp] theorem smallQuaternionArc_zero (a : SU2) : smallQuaternionArc a 0 = 1 := by
  simpa [smallQuaternionArc, arcBlend] using (normalizeQuaternion_unitary (1 : SU2))

@[simp] theorem smallQuaternionArc_one (a : SU2) : smallQuaternionArc a 1 = a := by
  simp [smallQuaternionArc, arcBlend]

theorem smallQuaternionArc_smooth (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) :
    ContDiff ℝ ∞ (fun t => (smallQuaternionArc a t : ℍ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (normalizeQuaternion_coe_contDiffAt (arcBlend_ne_zero a ha t)).comp t
    (((contDiff_const.sub Real.smoothTransition.contDiff).smul contDiff_const).add
      (Real.smoothTransition.contDiff.smul contDiff_const)).contDiffAt

theorem smallQuaternionArc_distance (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) (t : ℝ) :
    ‖(smallQuaternionArc a t : ℍ) - 1‖ ≤ ‖(a : ℍ) - 1‖ := by
  have hp : 0 < ‖arcBlend a t‖ := norm_pos_iff.mpr (arcBlend_ne_zero a ha t)
  have hre : (a : ℍ).re ≤ (smallQuaternionArc a t : ℍ).re := by
    rw [smallQuaternionArc, normalizeQuaternion_coe_of_ne_zero (arcBlend_ne_zero a ha t)]
    simp only [Quaternion.re_smul, smul_eq_mul]
    rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact (mul_le_of_le_one_right (small_unit_re a ha).1.le (arcBlend_norm_le a t)).trans
      (arcBlend_re_le a ha t)
  have h0 := su2_distance_square a
  have h1 := su2_distance_square (smallQuaternionArc a t)
  nlinarith [norm_nonneg ((a : ℍ)-1), norm_nonneg ((smallQuaternionArc a t : ℍ)-1)]

end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section SelectedEquations
variable {E : Type*} {m d : ℕ}

/-- The selected unknowns remain separate from coefficients, even when two
letters have the same image in the group quotient. -/
def selectedAlphabet (σ : Fin m ↪ E) (e : E) : E ⊕ Fin m := by
  classical
  exact if h : ∃ i, σ i = e then .inr h.choose else .inl e

@[simp] theorem selectedAlphabet_selected (σ : Fin m ↪ E) (i : Fin m) :
    selectedAlphabet σ (σ i) = .inr i := by
  classical
  have h : ∃ j, σ j = σ i := ⟨i,rfl⟩
  simp only [selectedAlphabet, dite_eq_left h]
  exact congrArg Sum.inr (σ.injective h.choose_spec)

 theorem selectedAlphabet_other (σ : Fin m ↪ E) (e : E) (he : ∀ i, σ i ≠ e) :
    selectedAlphabet σ e = .inl e := by
  classical
  simp [selectedAlphabet, he]

def selectedWord (σ : Fin m ↪ E) : FreeGroup E →* FreeGroup (E ⊕ Fin m) :=
  FreeGroup.map (selectedAlphabet σ)

def selectedLabel (σ : Fin m ↪ E) (a : E → SU2) (x : Fin m → SU2) (e : E) : SU2 :=
  Sum.elim a x (selectedAlphabet σ e)

@[simp] theorem selectedLabel_selected (σ : Fin m ↪ E) (a : E → SU2)
    (x : Fin m → SU2) (i : Fin m) : selectedLabel σ a x (σ i) = x i := by
  simp [selectedLabel]

 theorem selectedLabel_other (σ : Fin m ↪ E) (a : E → SU2) (x : Fin m → SU2)
    (e : E) (he : ∀ i, σ i ≠ e) : selectedLabel σ a x e = a e := by
  rw [selectedLabel, selectedAlphabet_other σ e he]
  rfl

 theorem selectedWord_eval (σ : Fin m ↪ E) (a : E → SU2) (x : Fin m → SU2)
    (w : FreeGroup E) :
    FreeGroup.lift (Sum.elim a x) (selectedWord σ w) =
      FreeGroup.lift (selectedLabel σ a x) w := by
  have he : (FreeGroup.lift (Sum.elim a x)).comp (selectedWord σ) =
      FreeGroup.lift (selectedLabel σ a x) := by
    apply FreeGroup.ext_hom
    intro e
    simp [selectedWord, selectedLabel]
  exact congrArg (fun f : FreeGroup E →* SU2 => f w) he

 theorem selectedWord_exponents [DecidableEq E] (σ : Fin m ↪ E) (w : FreeGroup E) (j : Fin m) :
    wordExponents (eraseCoefficients (selectedWord σ w)) j = wordExponents w (σ j) := by
  classical
  have he : (FreeGroup.lift (fun i : Fin m => Multiplicative.ofAdd (if j = i then (1 : ℤ) else 0))).comp
      (eraseCoefficients.comp (selectedWord σ)) =
      FreeGroup.lift (fun e : E => Multiplicative.ofAdd (if σ j = e then (1 : ℤ) else 0)) := by
    apply FreeGroup.ext_hom
    intro e
    by_cases h : ∃ i, σ i = e
    · obtain ⟨i,rfl⟩ := h
      simp [selectedWord, eraseCoefficients, σ.injective.eq_iff]
    · have h' : ∀ i, σ i ≠ e := by simpa only [not_exists] using h
      simp [selectedWord, eraseCoefficients, selectedAlphabet_other σ e h', h' j]
  exact congrArg (fun f : FreeGroup E →* Multiplicative ℤ => (f w).toAdd) he

/-- Solve a finite, full-rank system while keeping every unselected label fixed.
The distinguished sublevel condition is the actual isolated root condition,
not a nonsingularity assumption on the roots. -/
theorem selected_word_sublevel_solvable [DecidableEq E]
    (σ : Fin m ↪ E) (w : Fin m → FreeGroup E) (ρ : Fin d → FreeGroup E)
    (a : ℝ → E → SU2) (ha : ∀ e, ContDiff ℝ ∞ (fun t => (a t e : ℍ)))
    (ha0 : ∀ e, a 0 e = 1)
    (hB : Matrix.det (fun i j => wordExponents (w i) (σ j)) ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Fin m → SU2,
      (∀ i, FreeGroup.lift (selectedLabel σ (a t) x) (w i) = 1) →
      ‖(fun i => (FreeGroup.lift (selectedLabel σ (a t) x) (ρ i) : ℍ)) - 1‖ ≠ δ) :
    ∃ b : E → SU2,
      (∀ e, (∀ i, σ i ≠ e) → b e = a 1 e) ∧
      (∀ i, FreeGroup.lift b (w i) = 1) ∧
      ‖(fun i => (FreeGroup.lift b (ρ i) : ℍ)) - 1‖ < δ := by
  have hb : (exponentMatrix (fun i => eraseCoefficients (selectedWord σ (w i)))).det ≠ 0 := by
    change (Matrix.det (fun i j => wordExponents (eraseCoefficients (selectedWord σ (w i))) j)) ≠ 0
    simpa only [selectedWord_exponents] using hB
  obtain ⟨x,hx,hρ⟩ := coefficient_word_sublevel_solvable
    (fun i => selectedWord σ (w i)) (fun i => selectedWord σ (ρ i)) a ha ha0 hb δ hδ
    (fun t ht x hx => by
      simp only [coefficientWordMap, selectedWord_eval]
      apply hiso t ht x
      intro i
      have hi := congrFun hx i
      simpa only [coefficientWordMap, selectedWord_eval, Pi.one_apply] using hi)
  refine ⟨selectedLabel σ (a 1) x, fun e he => selectedLabel_other σ _ x e he, ?_, ?_⟩
  · intro i
    have hi := congrFun hx i
    simpa only [coefficientWordMap, selectedWord_eval, Pi.one_apply] using hi
  · simpa only [coefficientWordMap, selectedWord_eval] using hρ

end SelectedEquations
end EilenbergGanea

namespace EilenbergGanea

variable {Γ S H : Type*} [Group Γ] [Group H]

def labelLift (v : S → Γ) (a : Γ → S → H) :
    FreeGroup S →* ((Γ → H) ⋊[functionShift Γ H] Γ) :=
  FreeGroup.lift (fun s => ⟨fun g => a g s, v s⟩)

def wordValue (v : S → Γ) : FreeGroup S →* Γ := FreeGroup.lift v

def pathProduct (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) (g : Γ) : H :=
  (labelLift v a w).left g

 theorem labelLift_right (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) :
    (labelLift v a w).right = wordValue v w := by
  have he : (SemidirectProduct.rightHom : ((Γ → H) ⋊[functionShift Γ H] Γ) →* Γ).comp
      (labelLift v a) = wordValue v := by
    apply FreeGroup.ext_hom
    intro s
    simp [labelLift, wordValue]
  exact congrArg (fun f : FreeGroup S →* Γ => f w) he

@[simp] theorem pathProduct_one (v : S → Γ) (a : Γ → S → H) (g : Γ) :
    pathProduct v a 1 g = 1 := by simp [pathProduct]
@[simp] theorem pathProduct_of (v : S → Γ) (a : Γ → S → H) (s : S) (g : Γ) :
    pathProduct v a (FreeGroup.of s) g = a g s := by simp [pathProduct, labelLift]
 theorem pathProduct_mul (v : S → Γ) (a : Γ → S → H) (w z : FreeGroup S) (g : Γ) :
    pathProduct v a (w*z) g = pathProduct v a w g * pathProduct v a z (g * wordValue v w) := by
  simp only [pathProduct, map_mul, SemidirectProduct.mul_left, Pi.mul_apply, labelLift_right]
  rfl
 theorem pathProduct_inv (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) (g : Γ) :
    pathProduct v a w⁻¹ g = (pathProduct v a w (g * (wordValue v w)⁻¹))⁻¹ := by
  simp only [pathProduct, map_inv, SemidirectProduct.inv_left, labelLift_right]
  rfl

 theorem pathProduct_conjugate_loop (v : S → Γ) (a : Γ → S → H)
    (u r : FreeGroup S) (hr : wordValue v r = 1) (g : Γ) :
    pathProduct v a (u*r*u⁻¹) g = pathProduct v a u g *
      pathProduct v a r (g * wordValue v u) * (pathProduct v a u g)⁻¹ := by
  rw [pathProduct_mul, pathProduct_mul, pathProduct_inv, map_mul, hr, mul_one]
  simp only [mul_inv_cancel_right]

 theorem pathProduct_continuous [TopologicalSpace H] [IsTopologicalGroup H]
    (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    Continuous (fun a : Γ → S → H => pathProduct v a w g) := by
  induction w using FreeGroup.induction_on generalizing g with
  | one => simpa using (continuous_const : Continuous (fun _ : Γ → S → H => (1 : H)))
  | of s =>
      simp only [pathProduct_of]
      exact continuous_apply_apply g s
  | inv_of s =>
      simp only [pathProduct_inv, pathProduct_of]
      exact (continuous_apply_apply (g * (wordValue v (FreeGroup.of s))⁻¹) s).inv
  | mul w z hw hz =>
      simp only [pathProduct_mul]
      exact (hw g).mul (hz (g * wordValue v w))

/-- The set of vertices inspected by a word is finite, independently of the
label values. No countability hypothesis on the alphabet is needed. -/
theorem pathProduct_finite_locations (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    ∃ P : Finset Γ, ∀ a b : Γ → S → H,
      (∀ p ∈ P, ∀ s, a p s = b p s) → pathProduct v a w g = pathProduct v b w g := by
  classical
  induction w using FreeGroup.induction_on generalizing g with
  | one => exact ⟨∅, fun _ _ _ => by simp⟩
  | of s => exact ⟨{g}, fun a b hab => by simpa using hab g (by simp) s⟩
  | inv_of s =>
      exact ⟨{g * (wordValue v (FreeGroup.of s))⁻¹}, fun a b hab => by
        rw [pathProduct_inv, pathProduct_inv, pathProduct_of, pathProduct_of, hab _ (by simp)]⟩
  | mul w z hw hz =>
      obtain ⟨P, hP⟩ := hw g
      obtain ⟨Q, hQ⟩ := hz (g * wordValue v w)
      refine ⟨P ∪ Q, fun a b hab => ?_⟩
      rw [pathProduct_mul, pathProduct_mul, hP a b (fun p hp => hab p (Finset.mem_union_left Q hp)),
        hQ a b (fun p hp => hab p (Finset.mem_union_right P hp))]

/-- Evaluation commutes with pullback of a labeling along a group quotient,
including when different alphabet letters have the same image. -/
theorem pathProduct_pullback {D : Type*} [Group D] (q : Γ →* D)
    (v : S → Γ) (a : D → S → H) (w : FreeGroup S) (g : Γ) :
    pathProduct v (fun p s => a (q p) s) w g = pathProduct (fun s => q (v s)) a w (q g) := by
  have hv : ∀ w : FreeGroup S, wordValue (fun s => q (v s)) w = q (wordValue v w) := by
    have he : wordValue (fun s => q (v s)) = q.comp (wordValue v) := by
      apply FreeGroup.ext_hom
      intro s
      simp [wordValue]
    intro w
    exact congrArg (fun f : FreeGroup S →* D => f w) he
  induction w using FreeGroup.induction_on generalizing g with
  | one => simp
  | of s => simp
  | inv_of s => simp only [pathProduct_inv, pathProduct_of, hv, map_inv, map_mul]
  | mul w z hw hz => simp only [pathProduct_mul, hv, map_mul, hw, hz]


/-- Once every final relator has trivial transport at every vertex, normal
closure gives trivial transport on every null word, not just on a finite
collection of test loops. -/
 theorem pathProduct_trivial_of_relators (v : S → Γ) (a : Γ → S → H)
    (R : Set (FreeGroup S)) (hR : R ⊆ (wordValue v).ker)
    (hp : (wordValue v).ker = Subgroup.normalClosure R)
    (ha : ∀ r ∈ R, ∀ g, pathProduct v a r g = 1)
    (w : FreeGroup S) (hw : wordValue v w = 1) (g : Γ) : pathProduct v a w g = 1 := by
  have hrel : R ⊆ (labelLift v a).ker := by
    intro r hr
    change labelLift v a r = 1
    apply SemidirectProduct.ext
    · funext g
      exact ha r hr g
    · rw [labelLift_right]
      exact hR hr
  have hle : Subgroup.normalClosure R ≤ (labelLift v a).ker :=
    Subgroup.normalClosure_le_normal hrel
  have he : labelLift v a w = 1 := hle (by rw [← hp]; exact hw)
  change (labelLift v a w).left g = 1
  rw [he]
  rfl

 def pathChain (v : S → Γ) (w : FreeGroup S) (g : Γ) : (Γ × S) →₀ ℤ :=
  (pathProduct v (fun p s => Multiplicative.ofAdd (Finsupp.single (p,s) 1)) w g).toAdd

@[simp] theorem pathChain_one (v : S → Γ) (g : Γ) : pathChain v 1 g = 0 := by
  simp [pathChain]
@[simp] theorem pathChain_of (v : S → Γ) (s : S) (g : Γ) :
    pathChain v (FreeGroup.of s) g = Finsupp.single (g,s) 1 := by simp [pathChain]
 theorem pathChain_mul (v : S → Γ) (w z : FreeGroup S) (g : Γ) :
    pathChain v (w*z) g = pathChain v w g + pathChain v z (g * wordValue v w) := by
  simp only [pathChain, pathProduct_mul, toAdd_mul]
 theorem pathChain_inv (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    pathChain v w⁻¹ g = -pathChain v w (g * (wordValue v w)⁻¹) := by
  simp only [pathChain, pathProduct_inv, toAdd_inv]
 theorem pathChain_conjugate (v : S → Γ) (u r : FreeGroup S)
    (hr : wordValue v r = 1) (g : Γ) :
    pathChain v (u*r*u⁻¹) g = pathChain v r (g * wordValue v u) := by
  simp only [pathChain, pathProduct_conjugate_loop v _ u r hr g,
    toAdd_mul, toAdd_inv]
  abel

variable {R : Type*}
abbrev NormalFactor (S R : Type*) := FreeGroup S × R × Bool

 def normalFactorWord (r : R → FreeGroup S) (f : NormalFactor S R) : FreeGroup S :=
  f.1 * (if f.2.2 then r f.2.1 else (r f.2.1)⁻¹) * f.1⁻¹

 def normalFactorCount (v : S → Γ) (f : NormalFactor S R) (g : Γ) : (Γ × R) →₀ ℤ :=
  Finsupp.single (g * wordValue v f.1, f.2.1) (if f.2.2 then 1 else -1)

 def relatorChainMap (v : S → Γ) (r : R → FreeGroup S) :
    ((Γ × R) →₀ ℤ) →ₗ[ℤ] ((Γ × S) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun i => pathChain v (r i.2) i.1)

 theorem normalFactor_value (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (f : NormalFactor S R) :
    wordValue v (normalFactorWord r f) = 1 := by
  dsimp only [normalFactorWord]
  split_ifs <;> simp [hr]

 theorem pathChain_normalFactor (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (f : NormalFactor S R) (g : Γ) :
    pathChain v (normalFactorWord r f) g = relatorChainMap v r (normalFactorCount v f g) := by
  simp only [normalFactorWord, normalFactorCount, relatorChainMap, Finsupp.linearCombination_single]
  split_ifs with h
  · rw [pathChain_conjugate v _ _ (hr _)]; simp only [one_smul]
  · rw [pathChain_conjugate v _ _ (by simp [hr]), pathChain_inv, hr]
    simp only [inv_one, mul_one, neg_one_smul]

 theorem pathChain_normalProduct (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (l : List (NormalFactor S R)) (g : Γ) :
    pathChain v (l.map (normalFactorWord r)).prod g =
      relatorChainMap v r (l.map (fun f => normalFactorCount v f g)).sum := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, pathChain_mul,
        normalFactor_value v r hr f, mul_one, pathChain_normalFactor v r hr f g, ih]

/-- The coefficient identity is an equality in the full free abelian group of
translated indexed relators. Injectivity is sufficient; no finiteness of the
relator or generator types is assumed. -/
 theorem exact_translated_relator_counts (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (hinj : Function.Injective (relatorChainMap v r))
    (z : FreeGroup S) (ρ : R) (hchain : pathChain v z 1 = pathChain v (r ρ) 1)
    (l : List (NormalFactor S R)) (he : z = (l.map (normalFactorWord r)).prod) :
    (l.map (fun f => normalFactorCount v f 1)).sum = Finsupp.single (1,ρ) 1 := by
  apply hinj
  rw [← pathChain_normalProduct v r hr, ← he, hchain]
  simp [relatorChainMap]

end EilenbergGanea

namespace EilenbergGanea
variable {Γ S H : Type*} [Group Γ] [Group H]


section CompactLabeling
variable {T I : Type*}

 def mergeLabels (a : Γ → S → H) (b : Γ → T → H) : Γ → S ⊕ T → H :=
  fun g => Sum.elim (a g) (b g)

 omit [Group Γ] [Group H] in
 theorem mergeLabels_continuous [TopologicalSpace H] (a : Γ → S → H) :
    Continuous (fun b : Γ → T → H => mergeLabels a b) := by
  apply continuous_pi
  intro g
  apply continuous_pi
  intro s
  cases s with
  | inl s => exact continuous_const
  | inr t => exact continuous_apply_apply g t

/-- Copy arbitrary prescribed labels to a finite quotient solely on the finite
set of vertices currently being tested. This does not assert that the original
labeling is periodic or descends to a single quotient. -/
 theorem copy_labels_on_finite_set {D : Type*} [Group D] (q : Γ →* D)
    (P : Finset Γ) (hq : Set.InjOn q (P : Set Γ)) (a : Γ → S → H)
    (Allowed : H → Prop) (h1 : Allowed 1) (ha : ∀ g s, Allowed (a g s)) :
    ∃ aF : D → S → H, (∀ d s, Allowed (aF d s)) ∧ ∀ p ∈ P, ∀ s, aF (q p) s = a p s := by
  classical
  let aF : D → S → H := fun d s => if hd : ∃ p ∈ P, q p = d then a hd.choose s else 1
  refine ⟨aF, ?_, ?_⟩
  · intro d s
    dsimp [aF]
    split_ifs
    · exact ha _ _
    · exact h1
  · intro p hp s
    have he : ∃ p' ∈ P, q p' = q p := ⟨p, hp, rfl⟩
    simp only [aF, dite_eq_left he]
    have heq : he.choose = p := hq he.choose_spec.1 hp he.choose_spec.2
    rw [heq]

/-- Tychonoff compactness for all extra generators, with the original labels
fixed. The finite-quotient premise is exactly the separate finite solvability
obligation, not a periodicity assumption on the prescribed assignment. -/
 theorem compact_labeling_from_finite_quotients [Group.ResiduallyFinite Γ]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (v : S ⊕ T → Γ) (a : Γ → S → H) (w : I → FreeGroup (S ⊕ T)) (g : I → Γ)
    (K : I → Set H) (hK : ∀ i, IsClosed (K i))
    (Allowed : H → Prop) (h1 : Allowed 1) (ha : ∀ g s, Allowed (a g s))
    (hsolve : ∀ (N : FiniteIndexNormalSubgroup Γ) (J : Finset I)
      (aF : (Γ ⧸ N.toSubgroup) → S → H), (∀ d s, Allowed (aF d s)) →
      ∃ bF : (Γ ⧸ N.toSubgroup) → T → H, ∀ i ∈ J, ∀ d,
        pathProduct (fun s => QuotientGroup.mk' N.toSubgroup (v s))
          (mergeLabels aF bF) (w i) d ∈ K i) :
    ∃ b : Γ → T → H, ∀ i, pathProduct v (mergeLabels a b) (w i) (g i) ∈ K i := by
  classical
  let C : I → Set (Γ → T → H) := fun i =>
    {b | pathProduct v (mergeLabels a b) (w i) (g i) ∈ K i}
  have hc : ∀ i, IsClosed (C i) := fun i =>
    (hK i).preimage ((pathProduct_continuous v (w i) (g i)).comp (mergeLabels_continuous a))
  have hf : ∀ J : Finset I, (⋂ i ∈ J, C i).Nonempty := by
    intro J
    choose P hP using (fun i : I => pathProduct_finite_locations (H := H) v (w i) (g i))
    let V := J.biUnion P
    obtain ⟨N, hN⟩ := finite_set_quotient_injective V
    let q := QuotientGroup.mk' N.toSubgroup
    obtain ⟨aF, haF, heF⟩ := copy_labels_on_finite_set q V hN a Allowed h1 ha
    obtain ⟨bF, hbF⟩ := hsolve N J aF haF
    refine ⟨fun p t => bF (q p) t, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    change pathProduct v (mergeLabels a (fun p t => bF (q p) t)) (w i) (g i) ∈ K i
    have he : pathProduct v (mergeLabels a (fun p t => bF (q p) t)) (w i) (g i) =
        pathProduct v (fun p s => mergeLabels aF bF (q p) s) (w i) (g i) := by
      apply hP i
      intro p hp s
      cases s with
      | inl s => exact (heF p (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩) s).symm
      | inr t => rfl
    rw [he, pathProduct_pullback]
    exact hbF i hi (q (g i))
  obtain ⟨b, hb⟩ := CompactSpace.iInter_nonempty hc hf
  exact ⟨b, fun i => Set.mem_iInter.mp hb i⟩
end CompactLabeling
end EilenbergGanea

open scoped Quaternion
namespace EilenbergGanea

theorem su2_norm (a : SU2) : ‖(a : ℍ)‖ = 1 := by
  have h : star (a : ℍ) * (a : ℍ) = 1 := a.property.1
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg (a : ℍ)]

/-- The two elementary estimates needed for the presentation argument, with
constants independent of the Cayley graph or any finite quotient. -/
theorem unit_product_linearization (l : List ℍ) (h : ℝ) (hh : 0 ≤ h)
    (hu : ∀ a ∈ l, ‖a‖ = 1) (hb : ∀ a ∈ l, ‖a - 1‖ ≤ h) :
    ‖l.prod - 1‖ ≤ l.length * h ∧
    ‖l.prod - 1 - (l.map (fun a => a - 1)).sum‖ ≤ (l.length : ℝ)^2 * h^2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hp, he⟩ := ih (fun b hm => hu b (by simp [hm])) (fun b hm => hb b (by simp [hm]))
      have hna := hu a (by simp)
      have hba := hb a (by simp)
      have hid : a * l.prod - 1 = a * (l.prod - 1) + (a - 1) := by noncomm_ring
      have hie : a * l.prod - 1 - ((a - 1) + (l.map (fun b => b - 1)).sum) =
          (a - 1) * (l.prod - 1) + (l.prod - 1 - (l.map (fun b => b - 1)).sum) := by noncomm_ring
      constructor
      · simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hid]
        calc
          _ ≤ ‖a * (l.prod - 1)‖ + ‖a - 1‖ := norm_add_le _ _
          _ = ‖l.prod - 1‖ + ‖a - 1‖ := by rw [norm_mul, hna, one_mul]
          _ ≤ (l.length + 1) * h := by nlinarith
      · simp only [List.prod_cons, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hie]
        have hn : 0 ≤ (l.length : ℝ) := Nat.cast_nonneg _
        calc
          _ ≤ ‖(a - 1) * (l.prod - 1)‖ + ‖l.prod - 1 - (l.map (fun b => b - 1)).sum‖ := norm_add_le _ _
          _ = ‖a - 1‖ * ‖l.prod - 1‖ + ‖l.prod - 1 - (l.map (fun b => b - 1)).sum‖ := by rw [norm_mul]
          _ ≤ h * (l.length * h) + (l.length : ℝ)^2 * h^2 :=
            add_le_add (mul_le_mul hba hp (norm_nonneg _) hh) he
          _ ≤ (l.length + 1)^2 * h^2 := by nlinarith [sq_nonneg h]

 theorem quaternion_commutator_bound (a b : ℍ) :
    ‖a * b - b * a‖ ≤ 2 * ‖a - 1‖ * ‖b - 1‖ := by
  have he : a * b - b * a = (a - 1) * (b - 1) - (b - 1) * (a - 1) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(a - 1) * (b - 1)‖ + ‖(b - 1) * (a - 1)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul, norm_mul]; ring

 theorem su2_conjugation_error (a b : SU2) :
    ‖((a * b * a⁻¹ : SU2) : ℍ) - (b : ℍ)‖ ≤ 2 * ‖(a : ℍ) - 1‖ * ‖(b : ℍ) - 1‖ := by
  have he : ((a * b * a⁻¹ : SU2) : ℍ) - (b : ℍ) =
      ((a : ℍ) * (b : ℍ) - (b : ℍ) * (a : ℍ)) * ((a⁻¹ : SU2) : ℍ) := by
    change (a : ℍ) * (b : ℍ) * star (a : ℍ) - (b : ℍ) = _
    change _ = ((a : ℍ) * (b : ℍ) - (b : ℍ) * (a : ℍ)) * star (a : ℍ)
    rw [sub_mul, mul_assoc (b : ℍ), a.property.2, mul_one]
  rw [he, norm_mul, su2_norm, mul_one]
  exact quaternion_commutator_bound _ _

 theorem su2_inverse_distance (b : SU2) : ‖((b⁻¹ : SU2) : ℍ) - 1‖ = ‖(b : ℍ) - 1‖ := by
  change ‖star (b : ℍ) - 1‖ = _
  calc
    _ = ‖star ((b : ℍ) - 1)‖ := by rw [star_sub, star_one]
    _ = _ := norm_star _

 theorem su2_inverse_linearization (b : SU2) :
    ‖((b⁻¹ : SU2) : ℍ) - 1 + ((b : ℍ) - 1)‖ ≤ ‖(b : ℍ) - 1‖^2 := by
  have he : ((b⁻¹ : SU2) : ℍ) - 1 + ((b : ℍ) - 1) =
      -((((b⁻¹ : SU2) : ℍ) - 1) * ((b : ℍ) - 1)) := by
    have hb : ((b⁻¹ : SU2) : ℍ) * (b : ℍ) = 1 := b.property.1
    noncomm_ring [hb]
  rw [he, norm_neg, norm_mul, su2_inverse_distance, pow_two]

/-- Replacing each displacement by its linear model introduces only the sum
of the errors. Combined with exact signed counts, this avoids any choice of
an ordering of the relator indices (which can be uncountable). -/
theorem unit_product_with_linear_models {I : Type*} (l : List I)
    (f : I → SU2) (v : I → ℍ) (h D : ℝ) (hh : 0 ≤ h)
    (hb : ∀ i ∈ l, ‖(f i : ℍ) - 1‖ ≤ h)
    (he : ∀ i ∈ l, ‖(f i : ℍ) - 1 - v i‖ ≤ D) :
    ‖((l.map (fun i => (f i : ℍ))).prod - 1) - (l.map v).sum‖ ≤
      (l.length : ℝ)^2 * h^2 + l.length * D := by
  have hp := (unit_product_linearization (l.map (fun i => (f i : ℍ))) h hh
    (by intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact su2_norm _)
    (by intro a ha; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hb i hi)).2
  simp only [List.length_map, List.map_map, Function.comp_def] at hp
  have hs : ∀ l : List I, (∀ i ∈ l, ‖(f i : ℍ) - 1 - v i‖ ≤ D) →
      ‖(l.map (fun i => (f i : ℍ) - 1)).sum - (l.map v).sum‖ ≤ l.length * D := by
    intro l he
    induction l with
    | nil => simp
    | cons i l ih =>
        have hi := he i (by simp)
        have hrest := ih (fun j hj => he j (by simp [hj]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        have heq : (f i : ℍ) - 1 + (l.map (fun j => (f j : ℍ) - 1)).sum -
            (v i + (l.map v).sum) = ((f i : ℍ) - 1 - v i) +
              ((l.map (fun j => (f j : ℍ) - 1)).sum - (l.map v).sum) := by abel
        rw [heq]
        exact (norm_add_le _ _).trans (by linarith)

  calc
    _ ≤ ‖((l.map (fun i => (f i : ℍ))).prod - 1) - (l.map (fun i => (f i : ℍ) - 1)).sum‖ +
      ‖(l.map (fun i => (f i : ℍ) - 1)).sum - (l.map v).sum‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hp (hs l he)
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion

theorem su2_conjugation_distance (a b : SU2) :
    ‖((a * b * a⁻¹ : SU2) : ℍ) - 1‖ = ‖(b : ℍ) - 1‖ := by
  have he : ((a * b * a⁻¹ : SU2) : ℍ) - 1 =
      (a : ℍ) * ((b : ℍ) - 1) * star (a : ℍ) := by
    change (a : ℍ) * (b : ℍ) * star (a : ℍ) - 1 = _
    rw [mul_sub, sub_mul, mul_one, a.property.2]
  rw [he, norm_mul, norm_mul, norm_star, su2_norm, one_mul, mul_one]

def signedUnit (b : SU2) (ε : Bool) : SU2 := if ε then b else b⁻¹
def signedDisplacement (b : SU2) (ε : Bool) : ℍ := if ε then (b : ℍ) - 1 else -((b : ℍ) - 1)

 theorem signedUnit_distance (b : SU2) (ε : Bool) :
    ‖(signedUnit b ε : ℍ) - 1‖ = ‖(b : ℍ) - 1‖ := by
  cases ε <;> simp [signedUnit, su2_inverse_distance]

 theorem signedUnit_error (b : SU2) (ε : Bool) :
    ‖(signedUnit b ε : ℍ) - 1 - signedDisplacement b ε‖ ≤ ‖(b : ℍ) - 1‖^2 := by
  cases ε with
  | false =>
      change ‖((b⁻¹ : SU2) : ℍ) - 1 - (-((b : ℍ) - 1))‖ ≤ _
      simpa only [sub_neg_eq_add] using su2_inverse_linearization b
  | true => simp [signedUnit, signedDisplacement]

 theorem conjugated_signedUnit_error (a b : SU2) (ε : Bool) (A h : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (ha : ‖(a : ℍ) - 1‖ ≤ A) (hb : ‖(b : ℍ) - 1‖ ≤ h) :
    ‖((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - 1 - signedDisplacement b ε‖ ≤
      2 * A * h + h^2 := by
  have he : ((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - 1 - signedDisplacement b ε =
      (((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - (signedUnit b ε : ℍ)) +
      ((signedUnit b ε : ℍ) - 1 - signedDisplacement b ε) := by abel
  rw [he]
  have hsq : ‖(b : ℍ) - 1‖^2 ≤ h^2 := by nlinarith [norm_nonneg ((b : ℍ) - 1)]
  calc
    _ ≤ ‖((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - (signedUnit b ε : ℍ)‖ +
      ‖(signedUnit b ε : ℍ) - 1 - signedDisplacement b ε‖ := norm_add_le _ _
    _ ≤ 2 * ‖(a : ℍ) - 1‖ * ‖(b : ℍ) - 1‖ + ‖(b : ℍ) - 1‖^2 := by
      simpa only [signedUnit_distance] using add_le_add (su2_conjugation_error a (signedUnit b ε)) (signedUnit_error b ε)
    _ ≤ _ := add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left ha (by positivity)) hb
      (norm_nonneg _) (mul_nonneg (by positivity) hA)) hsq

abbrev RelatorFactor (I : Type*) := SU2 × I × Bool

def relatorFactorValue {I : Type*} (x : I → SU2) (r : RelatorFactor I) : SU2 :=
  r.1 * signedUnit (x r.2.1) r.2.2 * r.1⁻¹

def relatorSignedCounts {I : Type*} (l : List (RelatorFactor I)) : I →₀ ℤ :=
  (l.map (fun r => Finsupp.single r.2.1 (if r.2.2 then 1 else -1))).sum

 theorem relator_linear_models {I : Type*} (l : List (RelatorFactor I)) (x : I → SU2) :
    (l.map (fun r => signedDisplacement (x r.2.1) r.2.2)).sum =
      Finsupp.linearCombination ℤ (fun i => (x i : ℍ) - 1) (relatorSignedCounts l) := by
  induction l with
  | nil => simp [relatorSignedCounts]
  | cons r l ih =>
      simp only [List.map_cons, List.sum_cons, relatorSignedCounts, map_add, Finsupp.linearCombination_single]
      rw [← show Finsupp.linearCombination ℤ (fun i => (x i : ℍ) - 1)
          ((l.map (fun r => Finsupp.single r.2.1 (if r.2.2 then 1 else -1))).sum) =
          (l.map (fun r => signedDisplacement (x r.2.1) r.2.2)).sum from ih.symm]
      congr 2
      cases r.2.2 <;> simp [signedDisplacement]

/-- Exact translated counts cancel the full linear term; the remaining bound
is quadratic. The index set is arbitrary, not necessarily countable. -/
theorem relator_product_quadratic {I : Type*} (l : List (RelatorFactor I)) (x : I → SU2)
    (i₀ : I) (hc : relatorSignedCounts l = Finsupp.single i₀ 1)
    (h ε K : ℝ) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hb : ∀ r ∈ l, ‖(x r.2.1 : ℍ) - 1‖ ≤ h)
    (ha : ∀ r ∈ l, ‖(r.1 : ℍ) - 1‖ ≤ K * (ε + h)) :
    ‖(l.map (fun r => (relatorFactorValue x r : ℍ))).prod - (x i₀ : ℍ)‖ ≤
      ((l.length : ℝ)^2 + l.length + 2 * l.length * K) * (ε + h) * h := by
  have hp := unit_product_with_linear_models l (relatorFactorValue x)
    (fun r => signedDisplacement (x r.2.1) r.2.2) h
    (2 * (K * (ε + h)) * h + h^2) hh
    (fun r hr => by rw [relatorFactorValue, su2_conjugation_distance, signedUnit_distance]; exact hb r hr)
    (fun r hr => conjugated_signedUnit_error r.1 (x r.2.1) r.2.2 _ h
      (mul_nonneg hK (add_nonneg hε hh)) hh (ha r hr) (hb r hr))
  rw [relator_linear_models, hc, Finsupp.linearCombination_single, one_smul] at hp
  have he : (l.map (fun r => (relatorFactorValue x r : ℍ))).prod - 1 - ((x i₀ : ℍ) - 1) =
      (l.map (fun r => (relatorFactorValue x r : ℍ))).prod - (x i₀ : ℍ) := by abel
  rw [he] at hp
  apply hp.trans
  have hlen : 0 ≤ (l.length : ℝ) := Nat.cast_nonneg _
  have hnh : 0 ≤ ((l.length : ℝ)^2 + l.length) * ε * h :=
    mul_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) hlen) hε) hh
  nlinarith
end EilenbergGanea

namespace EilenbergGanea

/-- A uniform size for an arbitrary family, normalized to zero for an empty
index set. This is a real supremum, not an attained maximum. -/
def familySize {I : Type*} (f : I → ℝ) : ℝ := sSup (Set.range f ∪ {0})

 theorem familySize_nonneg {I : Type*} (f : I → ℝ) (hf : BddAbove (Set.range f)) :
    0 ≤ familySize f := by
  apply le_csSup (hf.union bddAbove_singleton)
  exact Or.inr (Set.mem_singleton _)

 theorem le_familySize {I : Type*} (f : I → ℝ) (hf : BddAbove (Set.range f)) (i : I) :
    f i ≤ familySize f := le_csSup (hf.union bddAbove_singleton) (Or.inl (Set.mem_range_self i))

 theorem familySize_le {I : Type*} (f : I → ℝ) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i, f i ≤ c) :
    familySize f ≤ c := by
  apply csSup_le (Set.union_nonempty.mpr (Or.inr (Set.singleton_nonempty 0)))
  rintro x (⟨i, rfl⟩ | rfl)
  · exact hf i
  · exact hc

/-- The source no-threshold-crossing argument does not assume attainment of
its supremum. -/
 theorem familySize_ne_threshold {I : Type*} (f : I → ℝ)
    (hf : BddAbove (Set.range f)) (C δ η ε : ℝ)
    (hδ : 0 < δ) (hC : 0 ≤ C) (_hη : 0 ≤ η) (hε : 0 ≤ ε) (hεη : ε ≤ η)
    (hc₁ : C * (δ + η) < 1/2) (hc₂ : C * η < δ/2)
    (hbound : ∀ i, f i ≤ C * ε + C * (familySize f + ε) * familySize f) :
    familySize f ≠ δ := by
  intro he
  have hs : familySize f ≤ C * ε + C * (familySize f + ε) * familySize f :=
    familySize_le f (by positivity [familySize_nonneg f hf]) hbound
  rw [he] at hs
  have hce : C * ε ≤ C * η := mul_le_mul_of_nonneg_left hεη hC
  have hfactor : C * (δ + ε) ≤ C * (δ + η) := mul_le_mul_of_nonneg_left (by linarith) hC
  nlinarith [mul_lt_mul_of_pos_right hc₁ hδ, mul_le_mul_of_nonneg_right hfactor hδ.le]

/-- Uniform contraction of all residual errors. This handles even an
uncountable family and does not replace the supremum by a maximum. -/
 theorem familySize_contraction {I : Type*} (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (δ C η : ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hb : ∀ i, f i ≤ δ) (hc : C * (δ + η) < 1)
    (he : ∀ i, f i ≤ C * (familySize f + η) * familySize f) : ∀ i, f i = 0 := by
  have hbounded : BddAbove (Set.range f) := ⟨δ, by rintro _ ⟨i, rfl⟩; exact hb i⟩
  have h0 := familySize_nonneg f hbounded
  have hmax := familySize_le f hδ hb
  have hs := familySize_le f (c := C * (familySize f + η) * familySize f) (by positivity) he
  have hmul : C * (familySize f + η) ≤ C * (δ + η) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have heq : familySize f = 0 := by
    by_contra hn
    have hp : 0 < familySize f := lt_of_le_of_ne h0 (Ne.symm hn)
    have ht := mul_lt_mul_of_pos_right (lt_of_le_of_lt hmul hc) hp
    nlinarith
  intro i
  exact le_antisymm (by simpa only [heq] using le_familySize f hbounded i) (hf i)

 theorem small_thresholds_exist (C : ℝ) (hC : 1 ≤ C) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < η ∧ η < 1 ∧
      C * (δ + η) < 1/2 ∧ C * η < δ/2 := by
  have hc : 0 < C := by linarith
  let δ := 1 / (8*C)
  let η := δ / (8*C)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ < 1 := by dsimp [δ]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  have he : 0 < η := by dsimp [η]; positivity
  have heδ : η < δ := by dsimp [η]; apply (div_lt_iff₀ (by positivity)).mpr; nlinarith
  have hcd : C * δ = 1/8 := by dsimp [δ]; field_simp
  have hce : C * η = δ/8 := by dsimp [η]; field_simp
  refine ⟨δ, η, hd, hd1, he, heδ.trans hd1, ?_, ?_⟩
  · rw [mul_add, hcd, hce]; linarith
  · rw [hce]; linarith
end EilenbergGanea


end

end OAI
