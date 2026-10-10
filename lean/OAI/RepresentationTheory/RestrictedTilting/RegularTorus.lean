import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.RegularActions

namespace OAI

/-! Torus density, regular localization and coprime denominator gluing. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
variable (k : Type*) [Field k] [Infinite k]

abbrev planeTorusPoints := {x : Fin 2 → k // ∀ i, x i ≠ 0}

noncomputable def planeTorusEvaluation :
    MvPolynomial (Fin 2) k →ₐ[k] (planeTorusPoints k → k) :=
  MvPolynomial.aeval (fun i x => x.val i)

omit [Infinite k] in
lemma planeTorusEvaluation_apply (P : MvPolynomial (Fin 2) k) (x : planeTorusPoints k) :
    planeTorusEvaluation k P x = MvPolynomial.eval x.val P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [planeTorusEvaluation]
  | add P Q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X P i hp =>
    simp only [map_mul, Pi.mul_apply, hp]
    congr 1
    simp [planeTorusEvaluation]

theorem planeTorusEvaluation_injective : Function.Injective (planeTorusEvaluation k) := by
  intro P Q h
  apply MvPolynomial.funext_set (fun _ : Fin 2 => ({0} : Set k)ᶜ)
    (fun _ => (Set.finite_singleton (0 : k)).infinite_compl)
  intro x hx
  have hx' : ∀ i, x i ≠ 0 := by
    intro i
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx i (Set.mem_univ i)
  exact (planeTorusEvaluation_apply k P ⟨x,hx'⟩).symm.trans
    ((congrFun h ⟨x,hx'⟩).trans (planeTorusEvaluation_apply k Q ⟨x,hx'⟩))

omit [Infinite k] in
lemma planeTorusEvaluation_X_isUnit (i : Fin 2) :
    IsUnit (planeTorusEvaluation k (MvPolynomial.X i)) := by
  refine ⟨⟨fun x => x.val i, fun x => (x.val i)⁻¹, ?_, ?_⟩, ?_⟩
  · funext x; exact mul_inv_cancel₀ (x.property i)
  · funext x; exact inv_mul_cancel₀ (x.property i)
  · ext x; simp [planeTorusEvaluation]

abbrev planeCoordinateChart (i : Fin 2) :=
  Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 2) k)

noncomputable def planeChartEvaluation (i : Fin 2) :
    planeCoordinateChart k i →ₐ[k] (planeTorusPoints k → k) :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X i) (planeTorusEvaluation_X_isUnit k i)

omit [Infinite k] in
lemma planeChartEvaluation_algebraMap (i : Fin 2) (P : MvPolynomial (Fin 2) k) :
    planeChartEvaluation k i
      (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i) P) =
      planeTorusEvaluation k P :=
  IsLocalization.Away.lift_eq _ (planeTorusEvaluation_X_isUnit k i) _

theorem planeChartEvaluation_injective (i : Fin 2) :
    Function.Injective (planeChartEvaluation k i) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (R := MvPolynomial (Fin 2) k) (S := planeCoordinateChart k i)
    (Submonoid.powers (MvPolynomial.X i)) (planeChartEvaluation k i).toRingHom).mpr
  intro P Q
  constructor
  · exact congrArg (planeChartEvaluation k i)
  · intro h
    have h' : planeTorusEvaluation k P = planeTorusEvaluation k Q := by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        planeChartEvaluation_algebraMap] using h
    exact congrArg (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i))
      (planeTorusEvaluation_injective k h')

end

section
universe u
variable (k : Type u) [Field k]

 
lemma regularSL2_polynomial_path (f : regularSL2Functions k)
    (g : k → SL2 k) (A : Matrix (Fin 2) (Fin 2) (Polynomial k))
    (hA : ∀ t i j, (A i j).eval t = g t i j) :
    ∃ P : Polynomial k, ∀ t, P.eval t = f.val (g t) := by
  obtain ⟨Q,hQ⟩ := f.property
  change coordinateEvaluation k Q = f.val at hQ
  refine ⟨MvPolynomial.aeval (fun ij => A ij.1 ij.2) Q, ?_⟩
  intro t
  rw [← congrFun hQ (g t), coordinateEvaluation_apply]
  clear hQ
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add Q R hQ hR => simp only [map_add, Polynomial.eval_add, hQ, hR]
  | mul_X Q i hQ =>
    simp only [map_mul, Polynomial.eval_mul, MvPolynomial.aeval_X, hA,
      MvPolynomial.eval_X, hQ]

noncomputable def regularLowerShear (t : k) : SL2 k :=
  ⟨!![1,0;t,1], by simp [Matrix.det_fin_two]⟩

lemma regularLowerShear_zero : regularLowerShear k 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma lowerShear_mul_entry (t : k) (g : SL2 k) (i j : Fin 2) :
    (regularLowerShear k t * g) i j =
      (!![g 0 0, g 0 1; t * g 0 0 + g 1 0, t * g 0 1 + g 1 1]) i j := by
  change ((regularLowerShear k t : Matrix (Fin 2) (Fin 2) k) *
    (g : Matrix (Fin 2) (Fin 2) k)) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [regularLowerShear, Matrix.mul_apply, Fin.sum_univ_two]

lemma upperShear_mul_entry (t : k) (g : SL2 k) (i j : Fin 2) :
    (unipotent k t * g) i j =
      (!![g 0 0 + t * g 1 0, g 0 1 + t * g 1 1; g 1 0, g 1 1]) i j := by
  change ((unipotent k t : Matrix (Fin 2) (Fin 2) k) *
    (g : Matrix (Fin 2) (Fin 2) k)) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [unipotent, Matrix.mul_apply, Fin.sum_univ_two]

 

theorem regularSL2_torus_dense [Infinite k] (f : regularSL2Functions k)
    (hf : ∀ g : SL2 k, g 0 0 ≠ 0 → g 1 0 ≠ 0 → f.val g = 0) : f = 0 := by
  have hfirst (g : SL2 k) (ha : g 0 0 ≠ 0) : f.val g = 0 := by
    obtain ⟨P,hP⟩ := regularSL2_polynomial_path k f (fun t => regularLowerShear k t * g)
      (!![Polynomial.C (g 0 0), Polynomial.C (g 0 1);
        Polynomial.X * Polynomial.C (g 0 0) + Polynomial.C (g 1 0),
        Polynomial.X * Polynomial.C (g 0 1) + Polynomial.C (g 1 1)]) (by
          intro t i j
          rw [lowerShear_mul_entry]
          fin_cases i <;> fin_cases j <;> simp <;> ring)
    have hzero : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply ((Set.finite_singleton (-g 1 0 / g 0 0)).infinite_compl).mono
      intro t ht
      change P.eval t = 0
      rw [hP]
      apply hf
      · simpa [lowerShear_mul_entry] using ha
      · have ht' : t ≠ -g 1 0 / g 0 0 := ht
        simp only [lowerShear_mul_entry]
        intro hz
        exact ht' ((eq_div_iff ha).mpr (eq_neg_of_add_eq_zero_left hz))
    have h := hP 0
    rw [hzero, Polynomial.eval_zero, regularLowerShear_zero, one_mul] at h
    exact h.symm
  apply Subtype.ext
  funext g
  change f.val g = 0
  by_cases ha : g 0 0 = 0
  · have hc : g 1 0 ≠ 0 := by
      intro hc
      have hd := g.property
      rw [Matrix.det_fin_two, ha, hc] at hd
      norm_num at hd
    obtain ⟨P,hP⟩ := regularSL2_polynomial_path k f (fun t => unipotent k t * g)
      (!![Polynomial.C (g 0 0) + Polynomial.X * Polynomial.C (g 1 0),
        Polynomial.C (g 0 1) + Polynomial.X * Polynomial.C (g 1 1);
        Polynomial.C (g 1 0), Polynomial.C (g 1 1)]) (by
          intro t i j
          rw [upperShear_mul_entry]
          fin_cases i <;> fin_cases j <;> simp <;> ring)
    have hzero : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply ((Set.finite_singleton (0 : k)).infinite_compl).mono
      intro t ht
      change P.eval t = 0
      rw [hP]
      apply hfirst
      simpa [upperShear_mul_entry, ha] using mul_ne_zero ht hc
    have h := hP 0
    rw [hzero, Polynomial.eval_zero, unipotent_zero, one_mul] at h
    exact h.symm
  · exact hfirst g ha


noncomputable def regularEntry (i j : Fin 2) : regularSL2Functions k :=
  coordinateToRegular k (MvPolynomial.X (i,j))

lemma regularEntry_apply (i j : Fin 2) (g : SL2 k) :
    (regularEntry k i j).val g = g i j := by
  change coordinateEvaluation k (MvPolynomial.X (i,j)) g = _
  rw [coordinateEvaluation_apply, MvPolynomial.eval_X]

lemma regularFirstColumn_eq_entry (i : Fin 2) :
    regularFirstColumn k i = regularEntry k i 0 := rfl

abbrev regularTorusPoints := {g : SL2 k // ∀ i, g i 0 ≠ 0}

noncomputable def regularTorusRestriction :
    regularSL2Functions k →ₐ[k] (regularTorusPoints k → k) where
  toFun f g := f.val g.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

lemma regularTorusRestriction_injective [Infinite k] :
    Function.Injective (regularTorusRestriction k) := by
  intro f h he
  apply sub_eq_zero.mp
  apply regularSL2_torus_dense k
  intro g ha hc
  exact sub_eq_zero.mpr (congrFun he ⟨g, by intro i; fin_cases i; exact ha; exact hc⟩)

noncomputable def regularPlane :
    MvPolynomial (Fin 2) k →ₐ[k] regularSL2Functions k :=
  MvPolynomial.aeval (regularFirstColumn k)

lemma regularPlane_evaluation (P : MvPolynomial (Fin 2) k) (g : SL2 k) :
    (regularPlane k P).val g = MvPolynomial.eval (fun i => g i 0) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [regularPlane]
  | add P Q hP hQ =>
    simp only [map_add, Subalgebra.coe_add, Pi.add_apply, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp only [Subalgebra.coe_mul, Pi.mul_apply]
    rw [hP]
    congr 1
    simpa only [regularPlane, MvPolynomial.aeval_X] using regularFirstColumn_apply k i g

abbrev regularCoordinateLocalization (i : Fin 2) :=
  Localization.Away (regularFirstColumn k i)

lemma regularTorusRestriction_coordinate_isUnit (i : Fin 2) :
    IsUnit (regularTorusRestriction k (regularFirstColumn k i)) := by
  refine ⟨⟨fun g => g.val i 0, fun g => (g.val i 0)⁻¹, ?_, ?_⟩, ?_⟩
  · funext g; exact mul_inv_cancel₀ (g.property i)
  · funext g; exact inv_mul_cancel₀ (g.property i)
  · funext g; exact (regularFirstColumn_apply k i g.val).symm

noncomputable def regularLocalizationEvaluation (i : Fin 2) :
    regularCoordinateLocalization k i →ₐ[k] (regularTorusPoints k → k) :=
  IsLocalization.Away.liftAlgHom (regularFirstColumn k i)
    (regularTorusRestriction_coordinate_isUnit k i)

lemma regularLocalizationEvaluation_algebraMap (i : Fin 2) (f : regularSL2Functions k) :
    regularLocalizationEvaluation k i
      (algebraMap (regularSL2Functions k) (regularCoordinateLocalization k i) f) =
      regularTorusRestriction k f :=
  IsLocalization.Away.lift_eq _ (regularTorusRestriction_coordinate_isUnit k i) _

noncomputable def planeChartPullback (i : Fin 2) :
    planeCoordinateChart k i →ₐ[k] regularCoordinateLocalization k i :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X i : MvPolynomial (Fin 2) k)
    (f := (IsScalarTower.toAlgHom k (regularSL2Functions k)
      (regularCoordinateLocalization k i)).comp (regularPlane k)) (by
        change IsUnit (algebraMap (regularSL2Functions k) (regularCoordinateLocalization k i)
          (regularPlane k (MvPolynomial.X i)))
        simp only [regularPlane, MvPolynomial.aeval_X]
        exact IsLocalization.Away.algebraMap_isUnit _)

lemma planeChartPullback_algebraMap (i : Fin 2) (P : MvPolynomial (Fin 2) k) :
    planeChartPullback k i
      (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i) P) =
      algebraMap (regularSL2Functions k) (regularCoordinateLocalization k i) (regularPlane k P) := by
  unfold planeChartPullback
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

noncomputable def regularToPlaneTorus (g : regularTorusPoints k) : planeTorusPoints k :=
  ⟨fun i => g.val i 0, g.property⟩

lemma planeChartPullback_evaluation (i : Fin 2) (f : planeCoordinateChart k i)
    (g : regularTorusPoints k) :
    regularLocalizationEvaluation k i (planeChartPullback k i f) g =
      planeChartEvaluation k i f (regularToPlaneTorus k g) := by
  let ev : (planeTorusPoints k → k) →+* (regularTorusPoints k → k) :=
    { toFun := fun f g => f (regularToPlaneTorus k g)
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have h : (regularLocalizationEvaluation k i).toRingHom.comp
      (planeChartPullback k i).toRingHom = ev.comp (planeChartEvaluation k i).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
    apply RingHom.ext
    intro P
    ext g
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      planeChartPullback_algebraMap, regularLocalizationEvaluation_algebraMap,
      planeChartEvaluation_algebraMap]
    exact (regularPlane_evaluation k P g.val).trans
      (planeTorusEvaluation_apply k P (regularToPlaneTorus k g)).symm
  exact congrFun (RingHom.congr_fun h f) g

noncomputable def regularCoordinateInverse (i : Fin 2) : regularCoordinateLocalization k i :=
  IsLocalization.Away.invSelf (S := regularCoordinateLocalization k i) (regularFirstColumn k i)

lemma regularCoordinateInverse_evaluation (i : Fin 2) (g : regularTorusPoints k) :
    regularLocalizationEvaluation k i (regularCoordinateInverse k i) g = (g.val i 0)⁻¹ := by
  have hmul := IsLocalization.Away.mul_invSelf (S := regularCoordinateLocalization k i)
    (regularFirstColumn k i)
  have h := congrFun (congrArg (regularLocalizationEvaluation k i) hmul) g
  simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply,
    regularLocalizationEvaluation_algebraMap] at h
  change (regularFirstColumn k i).val g.val *
    regularLocalizationEvaluation k i (regularCoordinateInverse k i) g = 1 at h
  rw [regularFirstColumn_apply] at h
  exact mul_left_cancel₀ (g.property i) (h.trans (mul_inv_cancel₀ (g.property i)).symm)

 

lemma regularLocalization_has_numerator (i : Fin 2) (f : regularCoordinateLocalization k i) :
    ∃ (n : ℕ) (a : regularSL2Functions k), ∀ g : regularTorusPoints k,
      (g.val i 0)^n * regularLocalizationEvaluation k i f g = a.val g.val := by
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj (regularFirstColumn k i) f
  refine ⟨n,a,fun g => ?_⟩
  have h := congrFun (congrArg (regularLocalizationEvaluation k i) ha) g
  simp only [map_mul, map_pow, regularLocalizationEvaluation_algebraMap,
    Pi.mul_apply, Pi.pow_apply] at h
  change _ * ((regularFirstColumn k i).val g.val)^n = a.val g.val at h
  rwa [regularFirstColumn_apply, mul_comm] at h

end

 

lemma coprime_denominator_glue {R : Type*} [CommRing R] {a b : R}
    (hab : IsCoprime a b) (n m : ℕ) (f g : R)
    (hfg : b^m * f = a^n * g) :
    ∃ h : R, a^n * h = f ∧ b^m * h = g := by
  obtain ⟨c,d,hcd⟩ := (hab.pow : IsCoprime (a^n) (b^m))
  refine ⟨c*f+d*g, ?_, ?_⟩
  · calc
      a^n * (c*f+d*g) = c*a^n*f + d*(a^n*g) := by ring
      _ = c*a^n*f + d*(b^m*f) := by rw [hfg]
      _ = (c*a^n+d*b^m)*f := by ring
      _ = f := by rw [hcd, one_mul]
  · calc
      b^m * (c*f+d*g) = c*(b^m*f) + d*b^m*g := by ring
      _ = c*(a^n*g) + d*b^m*g := by rw [hfg]
      _ = (c*a^n+d*b^m)*g := by ring
      _ = g := by rw [hcd, one_mul]

universe u
variable (k : Type u) [Field k] [Infinite k]

omit [Infinite k] in
lemma regularFirstColumns_coprime :
    IsCoprime (regularFirstColumn k 0) (regularFirstColumn k 1) := by
  refine ⟨regularEntry k 1 1, -regularEntry k 0 1, ?_⟩
  apply Subtype.ext
  funext g
  change (regularEntry k 1 1).val g * (regularFirstColumn k 0).val g +
    -(regularEntry k 0 1).val g * (regularFirstColumn k 1).val g = 1
  rw [regularEntry_apply, regularEntry_apply, regularFirstColumn_apply, regularFirstColumn_apply]
  have hd := g.property
  rw [Matrix.det_fin_two] at hd
  linear_combination hd

 

theorem regularTorus_glue (F : regularTorusPoints k → k)
    (f₀ : regularCoordinateLocalization k 0) (f₁ : regularCoordinateLocalization k 1)
    (h₀ : regularLocalizationEvaluation k 0 f₀ = F)
    (h₁ : regularLocalizationEvaluation k 1 f₁ = F) :
    ∃ f : regularSL2Functions k, regularTorusRestriction k f = F := by
  obtain ⟨n,a,ha⟩ := regularLocalization_has_numerator k 0 f₀
  obtain ⟨m,b,hb⟩ := regularLocalization_has_numerator k 1 f₁
  have hab : (regularFirstColumn k 1)^m * a = (regularFirstColumn k 0)^n * b := by
    apply regularTorusRestriction_injective k
    funext g
    change ((regularFirstColumn k 1).val g.val)^m * a.val g.val =
      ((regularFirstColumn k 0).val g.val)^n * b.val g.val
    rw [regularFirstColumn_apply, regularFirstColumn_apply, ← ha g, ← hb g, h₀, h₁]
    ring
  obtain ⟨f,hf,-⟩ := coprime_denominator_glue (regularFirstColumns_coprime k) n m a b hab
  refine ⟨f,funext fun g => ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero n (g.property 0))
  have h := congrArg (fun a : regularSL2Functions k => a.val g.val) hf
  change ((regularFirstColumn k 0).val g.val)^n * f.val g.val = a.val g.val at h
  rw [regularFirstColumn_apply, ← ha g, h₀] at h
  exact h

omit [Infinite k] in
lemma subalgebra_polynomial_mem {Ω σ : Type*} (S : Subalgebra k (Ω → k))
    (x : σ → Ω → k) (hx : ∀ i, x i ∈ S) (P : MvPolynomial σ k) :
    (fun g => MvPolynomial.eval (fun i => x i g) P) ∈ S := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    convert S.algebraMap_mem c using 1
    ext g
    simp
  | add P Q hP hQ =>
    convert S.add_mem hP hQ using 1
    ext g
    simp
  | mul_X P i hP =>
    convert S.mul_mem hP (hx i) using 1
    ext g
    simp

omit [Infinite k] in
lemma regularSL2_pullback_mem (φ : SL2 k → SL2 k)
    (A : Matrix (Fin 2) (Fin 2) (regularSL2Functions k))
    (hA : ∀ g i j, (A i j).val g = φ g i j) (f : regularSL2Functions k) :
    (fun g => f.val (φ g)) ∈ regularSL2Functions k := by
  obtain ⟨P,hP⟩ := f.property
  have h := subalgebra_polynomial_mem k (regularSL2Functions k)
    (fun ij : Fin 2 × Fin 2 => (A ij.1 ij.2).val) (fun ij => (A ij.1 ij.2).property) P
  have he : (fun g => MvPolynomial.eval (fun ij => (A ij.1 ij.2).val g) P) =
      (fun g => f.val (φ g)) := by
    funext g
    simp only [hA]
    exact (coordinateEvaluation_apply k P (φ g)).symm.trans (congrFun hP (φ g))
  exact he ▸ h

noncomputable def regularRightTranslation (h : SL2 k) (f : regularSL2Functions k) :
    regularSL2Functions k :=
  ⟨fun g => f.val (g*h), regularSL2_pullback_mem k (fun g => g*h)
    (fun i j => ∑ l : Fin 2, (h l j) • regularEntry k i l) (by
      intro g i j
      rw [Fin.sum_univ_two]
      change h 0 j * (regularEntry k i 0).val g + h 1 j * (regularEntry k i 1).val g =
        ((g : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k)) i j
      rw [regularEntry_apply, regularEntry_apply, Matrix.mul_apply, Fin.sum_univ_two]
      ring) f⟩

omit [Infinite k] in
lemma regularRightTranslation_apply (h g : SL2 k) (f : regularSL2Functions k) :
    (regularRightTranslation k h f).val g = f.val (g*h) := rfl

end FiberFunctorProof
end

end OAI
