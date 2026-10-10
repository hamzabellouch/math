import OAI.RingTheory.BassTrace.PfaffianDetector

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Relative exponents use orbit representatives internally, without assuming an equivariant section. -/

namespace RelativeExponents

lemma exists_affine_function {L P : Type*} [Group L] [MulAction L P]
    (χ : L → ℝ) (hχ : ∀ a b, χ (a*b) = χ a + χ b)
    (hstab : ∀ (a : L) (p : P), a • p = p → χ a = 0) :
    ∃ B : P → ℝ, ∀ (a : L) (p : P), B (a • p) = B p + χ a := by
  classical
  let q (p : P) : MulAction.orbitRel.Quotient L P := Quotient.mk _ p
  have ht (p : P) : ∃ a : L, a • (q p).out = p := by
    exact Quotient.exact (Quotient.out_eq (q p)).symm
  let t (p : P) : L := (ht p).choose
  have htp (p : P) : t p • (q p).out = p := (ht p).choose_spec
  have hq (a : L) (p : P) : q (a • p) = q p := Quotient.sound ⟨a, rfl⟩
  have h1 : χ 1 = 0 := by have hh := hχ 1 1; simpa using hh
  have hinv (a : L) : χ a⁻¹ = -χ a := by
    have hh := hχ a⁻¹ a
    rw [inv_mul_cancel, h1] at hh
    linarith
  refine ⟨fun p => χ (t p), ?_⟩
  intro a p
  have he : ((t (a • p))⁻¹ * (a * t p)) • (q p).out = (q p).out := by
    rw [mul_smul, mul_smul, htp]
    have hr := htp (a • p)
    rw [hq] at hr
    calc
      _ = (t (a • p))⁻¹ • (t (a • p) • (q p).out) := congrArg _ hr.symm
      _ = _ := inv_smul_smul _ _
  have hz := hstab _ _ he
  rw [hχ, hχ, hinv] at hz
  linarith

variable {G : Type*} [Group G]

abbrev Positions (g : G) :=
  (Multiplicative ℤ × Multiplicative ℤ) × Subgroup.centralizer ({g} : Set G)

lemma centralizer_commutes (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Commute g (c : G) :=
  (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm

def positionHom (g : G) : Positions g →* G × G where
  toFun a := (g ^ Multiplicative.toAdd a.1.1 * a.2,
    g ^ Multiplicative.toAdd a.1.2 * a.2)
  map_one' := by simp
  map_mul' a b := by
    apply Prod.ext
    · change g ^ (Multiplicative.toAdd a.1.1 + Multiplicative.toAdd b.1.1) *
          ((a.2 : G) * b.2) = (g ^ Multiplicative.toAdd a.1.1 * a.2) *
          (g ^ Multiplicative.toAdd b.1.1 * b.2)
      rw [zpow_add]
      have hc := (centralizer_commutes g a.2).symm.zpow_right
        (Multiplicative.toAdd b.1.1)
      simp only [mul_assoc]
      rw [← mul_assoc (a.2 : G), hc.eq, mul_assoc]
    · change g ^ (Multiplicative.toAdd a.1.2 + Multiplicative.toAdd b.1.2) *
          ((a.2 : G) * b.2) = (g ^ Multiplicative.toAdd a.1.2 * a.2) *
          (g ^ Multiplicative.toAdd b.1.2 * b.2)
      rw [zpow_add]
      have hc := (centralizer_commutes g a.2).symm.zpow_right
        (Multiplicative.toAdd b.1.2)
      simp only [mul_assoc]
      rw [← mul_assoc (a.2 : G), hc.eq, mul_assoc]

def character (g : G) (a : Positions g) : ℝ :=
  ((Multiplicative.toAdd a.1.2 : ℤ) : ℝ) - ((Multiplicative.toAdd a.1.1 : ℤ) : ℝ)

lemma character_mul (g : G) (a b : Positions g) :
    character g (a*b) = character g a + character g b := by
  change (((Multiplicative.toAdd a.1.2 + Multiplicative.toAdd b.1.2 : ℤ) : ℝ) -
    ((Multiplicative.toAdd a.1.1 + Multiplicative.toAdd b.1.1 : ℤ) : ℝ)) = _
  simp only [character, Int.cast_add]
  ring

theorem exists_beta (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ β : G → G → ℝ,
      (∀ h k, β k h = -β h k) ∧
      (∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
        β (c*h) (c*k) = β h k) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r) := by
  let : MulAction (Positions g) (G × G) := MulAction.compHom (G × G) (positionHom g)
  have hstab (a : Positions g) (p : G × G) (h : a • p = p) : character g a = 0 := by
    have hleft := congrArg Prod.fst h
    have hright := congrArg Prod.snd h
    change (g ^ Multiplicative.toAdd a.1.1 * a.2) * p.1 = p.1 at hleft
    change (g ^ Multiplicative.toAdd a.1.2 * a.2) * p.2 = p.2 at hright
    have hl : g ^ Multiplicative.toAdd a.1.1 * a.2 = 1 := by simpa only [mul_eq_right] using hleft
    have hr : g ^ Multiplicative.toAdd a.1.2 * a.2 = 1 := by simpa only [mul_eq_right] using hright
    have he : Multiplicative.toAdd a.1.1 = Multiplicative.toAdd a.1.2 :=
      injective_zpow_iff_not_isOfFinOrder.mpr hg (mul_right_cancel (hl.trans hr.symm))
    simp [character, he]
  obtain ⟨B, hB⟩ := exists_affine_function (character g) (character_mul g) hstab
  have hBc (c : Subgroup.centralizer ({g} : Set G)) (h k : G) :
      B (c*h,c*k) = B (h,k) := by
    have he := hB ((1,1),c) (h,k)
    simpa [positionHom, MulAction.compHom_smul_def, character] using he
  have hBp (r s : ℤ) (h k : G) : B (g^r*h,g^s*k) = B (h,k) + s - r := by
    have he := hB ((Multiplicative.ofAdd r,Multiplicative.ofAdd s),1) (h,k)
    simpa [positionHom, MulAction.compHom_smul_def, character, sub_eq_add_neg, add_assoc] using he
  refine ⟨fun h k => (B (h,k) - B (k,h))/2, ?_, ?_, ?_⟩
  · intro h k; ring
  · intro c h k; dsimp only; rw [hBc, hBc]
  · intro r s h k; dsimp only; rw [hBp, hBp]; ring

end RelativeExponents

namespace Detector

section

open scoped BigOperators

open Oriented ChainHomotopy

variable {G : Type*} [Group G]

def Vertex (g : G) := Quotient (QuotientGroup.rightRel (Subgroup.zpowers g))

def project (g : G) (h : G) : Vertex g := Quotient.mk _ h

def sectionLift (g : G) (y : Vertex g) : G := y.out

lemma project_sectionLift (g : G) (y : Vertex g) :
    project g (sectionLift g y) = y := Quotient.out_eq y

lemma project_eq_iff (g h k : G) :
    project g h = project g k ↔ ∃ r : ℤ, g^r*h = k := by
  constructor
  · intro he
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hr
    exact ⟨r, (eq_mul_inv_iff_mul_eq.mp hr)⟩
  · rintro ⟨r, rfl⟩
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simp only [mul_inv_cancel_right]
    exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) r

lemma exists_section_power (g h : G) :
    ∃ r : ℤ, g^r*h = sectionLift g (project g h) := by
  apply (project_eq_iff g _ _).mp
  exact (project_sectionLift g _).symm

def centralizerAct (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Vertex g → Vertex g := Quotient.lift (fun h => project g (c*h)) (by
  intro h k hhk
  obtain ⟨r, hr⟩ := (project_eq_iff g h k).mp (Quotient.sound hhk)
  apply (project_eq_iff g _ _).mpr
  refine ⟨r, ?_⟩
  have hc := (RelativeExponents.centralizer_commutes g c).zpow_left r
  rw [← mul_assoc, hc.eq, mul_assoc, hr])

@[simp] lemma centralizerAct_project (g : G)
    (c : Subgroup.centralizer ({g} : Set G)) (h : G) :
    centralizerAct g c (project g h) = project g (c*h) := rfl

lemma centralizerAct_one (g : G) (y : Vertex g) :
    centralizerAct g 1 y = y := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g ((1:G)*h) = project g h
    rw [one_mul]

lemma centralizerAct_mul (g : G) (c d : Subgroup.centralizer ({g} : Set G))
    (y : Vertex g) : centralizerAct g (c*d) y =
      centralizerAct g c (centralizerAct g d y) := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (((c:G)*d)*h) = project g (c*(d*h))
    rw [mul_assoc]

lemma centralizerAct_power (g : G) (r : ℤ) (y : Vertex g) :
    project g (g^r*sectionLift g y) = y := by
  exact (((project_eq_iff g _ _).mpr ⟨r, rfl⟩).symm).trans
    (project_sectionLift g y)

lemma exists_complex_beta (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ β : G → G → ℂ,
      (∀ h k, β h k = -β k h) ∧
      (∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
        β (c*h) (c*k) = β h k) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r) := by
  obtain ⟨β, hβ, hc, hl⟩ := RelativeExponents.exists_beta g hg
  refine ⟨fun h k => (β h k : ℂ), ?_, ?_, ?_⟩
  · intro h k
    simpa only [Complex.ofReal_neg] using congrArg Complex.ofReal (hβ k h)
  · intro c h k
    exact congrArg Complex.ofReal (hc c h k)
  · intro r s h k
    simp only [hl, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_intCast]

lemma detector_section (g : G) (β : G → G → ℂ)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (m : ℕ) (h : Fin (2*m+1) → G) :
    detector m (fun i j => β (sectionLift g (project g (h i)))
      (sectionLift g (project g (h j)))) =
      detector m (fun i j => β (h i) (h j)) := by
  choose r hr using fun i => exists_section_power g (h i)
  have hb : (fun i j => β (sectionLift g (project g (h i)))
      (sectionLift g (project g (h j)))) =
      (fun i j => β (h i) (h j) + (r j : ℂ) - (r i : ℂ)) := by
    funext i j
    rw [← hr i, ← hr j, hl]
  rw [hb]
  exact detector_lift_independent m (fun i j => β (h i) (h j)) (fun i => (r i : ℂ))

lemma detector_section_invariant (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
      β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (m : ℕ) (c : Subgroup.centralizer ({g} : Set G)) (v : Fin (2*m+1) → Vertex g) :
    detector m (fun i j => β (sectionLift g (centralizerAct g c (v i)))
      (sectionLift g (centralizerAct g c (v j)))) =
      detector m (fun i j => β (sectionLift g (v i)) (sectionLift g (v j))) := by
  have hp (i) : centralizerAct g c (v i) =
      project g (c*sectionLift g (v i)) := by
    rw [← centralizerAct_project, project_sectionLift]
  simp only [hp]
  rw [detector_section g β hl m (fun i => c*sectionLift g (v i))]
  simp only [hc]

end

section

open Oriented ChainHomotopy

variable {G : Type*} [Group G]

def cosetCocycle (g : G) (m : ℕ) (β : G → G → ℂ) :
    Degree (Vertex g) (2*m+1) →ₗ[ℂ] ℂ := by
  classical
  letI : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  exact cocycle m (fun y z => β (sectionLift g y) (sectionLift g z))

lemma cosetCocycle_wedge (g : G) (m : ℕ) (β : G → G → ℂ)
    (v : Fin (2*m+1) → Vertex g) :
    cosetCocycle g m β (wedge (2*m+1) v) =
      detector m (fun i j => β (sectionLift g (v i)) (sectionLift g (v j))) := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  unfold cosetCocycle
  exact cocycle_wedge _ _ _

lemma cosetCocycle_lifts (g : G) (m : ℕ) (β : G → G → ℂ)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (h : Fin (2*m+1) → G) :
    cosetCocycle g m β (wedge (2*m+1) (project g ∘ h)) =
      detector m (fun i j => β (h i) (h j)) := by
  rw [cosetCocycle_wedge]
  exact detector_section g β hl m h

lemma cosetCocycle_closed (g : G) (m : ℕ) (β : G → G → ℂ)
    (hβ : ∀ y z, β y z = -β z y)
    (x : Degree (Vertex g) (2*m+2)) :
    cosetCocycle g m β (d (2*m+1) x) = 0 := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  unfold cosetCocycle
  exact cocycle_closed m _ (fun y z => hβ _ _) x

lemma cosetCocycle_invariant (g : G) (m : ℕ) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
      β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (c : Subgroup.centralizer ({g} : Set G))
    (x : Degree (Vertex g) (2*m+1)) :
    cosetCocycle g m β (relabel (2*m+1) (centralizerAct g c) x) =
      cosetCocycle g m β x := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  have he : (cosetCocycle g m β).comp (relabel (2*m+1) (centralizerAct g c)) =
      cosetCocycle g m β := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, relabel_wedge, cosetCocycle_wedge,
      Function.comp_apply]
    exact detector_section_invariant g β hc hl m c v
  exact LinearMap.congr_fun he x

theorem exists_coset_detector (g : G) (hg : ¬ IsOfFinOrder g) (m : ℕ) :
    ∃ β : G → G → ℂ, ∃ ψ : Degree (Vertex g) (2*m+1) →ₗ[ℂ] ℂ,
      (∀ h k, β h k = -β k h) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k+s-r) ∧
      (∀ x, ψ (d (2*m+1) x) = 0) ∧
      (∀ c x, ψ (relabel (2*m+1) (centralizerAct g c) x) = ψ x) ∧
      (∀ h : Fin (2*m+1) → G, ψ (wedge (2*m+1) (project g ∘ h)) =
        detector m (fun i j => β (h i) (h j))) := by
  obtain ⟨β,hβ,hc,hl⟩ := exists_complex_beta g hg
  exact ⟨β,cosetCocycle g m β,hβ,hl,cosetCocycle_closed g m β hβ,
    cosetCocycle_invariant g m β hc hl,cosetCocycle_lifts g m β hl⟩

end

open scoped BigOperators

lemma square_decomposable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : M) :
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R v), ι_mul_ι_neg v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
    zero_mul, zero_mul, neg_zero]

lemma nilpotent_binomial {A : Type*} [Ring A] (b c : A) (hc : Commute c b)
    (hz : c*c = 0) (m : ℕ) :
    (b+c)^(m+1) = b^(m+1) + (m+1) • (c*b^m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlast : c*b^m*c = 0 := by
      rw [(hc.pow_right m).eq, mul_assoc, hz, mul_zero]
    calc
      (b+c)^(m+1+1) = (b^(m+1)+(m+1) • (c*b^m)) * (b+c) := by
        rw [pow_succ, ih]
      _ = b^(m+1+1) + c*b^(m+1) + (m+1) • (c*b^(m+1)) := by
        rw [add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, hlast,
          nsmul_zero, add_zero, ← pow_succ, (hc.pow_right (m+1)).eq.symm]
        simp only [mul_assoc, ← pow_succ]
      _ = b^(m+1+1) + (m+1+1) • (c*b^(m+1)) := by
        simp only [add_nsmul, one_nsmul]
        abel

lemma factorial_cancel (m : ℕ) :
    ((m+1).factorial : ℂ)⁻¹ * (m+1 : ℂ) = (m.factorial : ℂ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  field_simp

lemma normalized_decomposable_update {I : Type*} (b : CoordinateAlgebra I)
    (hb : b ∈ ⋀[ℂ]^2 (CoordinateSpace I)) (u v : CoordinateSpace I) (m : ℕ) :
    ((m+1).factorial : ℂ)⁻¹ • (b+ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v)^(m+1) =
      ((m+1).factorial : ℂ)⁻¹ • b^(m+1) +
        (m.factorial : ℂ)⁻¹ • (ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v*b^m) := by
  have hc : Commute (ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v) b :=
    (ι_commute_degree_two u hb).mul_left (ι_commute_degree_two v hb)
  rw [nilpotent_binomial _ _ hc (square_decomposable u v), smul_add,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [factorial_cancel]

lemma coordinateVector_minor {n : ℕ} (i : Fin (n+1)) :
    coordinateVector (fun _ : Fin (n+1) => (1 : ℂ)) = coordinate i +
      coordinateMap i.succAbove (coordinateVector (fun _ : Fin n => (1 : ℂ))) := by
  simp only [coordinateVector, one_smul, map_sum, coordinateMap_coordinate]
  exact Fin.sum_univ_succAbove coordinate i

lemma coordinateVector_indicator {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    coordinateVector (fun j => if j = i then (1 : ℂ) else 0) = coordinate i := by
  simp [coordinateVector, ite_smul]

lemma pfaffianForm_lift_basis (m : ℕ)
    (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ)
    (hB : ∀ k l, B k l = -B l k) (i : Fin (2*m+1+1)) :
    pfaffianForm (m+1) (fun k l => B k l + (if l = i then 1 else 0) -
      (if k = i then 1 else 0)) =
      pfaffianForm (m+1) B - insertCoordinate i
        (detectorForm m (fun k l => B (i.succAbove k) (i.succAbove l))) := by
  classical
  apply Subtype.ext
  let b := twoForm (fun k l => B (i.succAbove k) (i.succAbove l))
  let u := coordinateVector (fun _ : Fin (2*m+1+1) => (1 : ℂ))
  let u' := coordinateVector (fun _ : Fin (2*m+1) => (1 : ℂ))
  have hm : ExteriorAlgebra.map (coordinateMap i.succAbove) b ∈
      ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m+1+1))) := by
    have h := (exteriorPower.map 2 (coordinateMap i.succAbove)
      (⟨b, twoForm_mem _⟩ : ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m+1))))).property
    simpa only [exteriorMap_coe] using h
  have hc : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) =
      -(ExteriorAlgebra.ι ℂ (coordinate i) *
        ExteriorAlgebra.ι ℂ (coordinateMap i.succAbove u')) := by
    rw [ι_mul_ι_neg, show u = coordinate i + coordinateMap i.succAbove u' from
      coordinateVector_minor i, map_add, mul_add, ExteriorAlgebra.ι_sq_zero, zero_add]
  have hcorr : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) * (twoForm B)^m =
      -(ExteriorAlgebra.ι ℂ (coordinate i) *
        (ExteriorAlgebra.ι ℂ (coordinateMap i.succAbove u') *
          (ExteriorAlgebra.map (coordinateMap i.succAbove) b)^m)) := by
    rw [mul_assoc, twoForm_row B hB i, gauge_invariance _ _ hm,
      ← mul_assoc, hc, neg_mul, mul_assoc]
  simp only [pfaffianForm, Submodule.coe_sub, insertCoordinate, LinearMap.comp_apply,
    multiplyVector_coe, exteriorMap_coe, detectorForm, map_mul, map_smul, map_pow,
    ExteriorAlgebra.map_apply_ι]
  rw [twoForm_lift_change B (fun k => if k = i then 1 else 0), coordinateVector_indicator,
    normalized_decomposable_update _ (twoForm_mem B)]
  change _ + (m.factorial : ℂ)⁻¹ •
      (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) * (twoForm B)^m) = _
  rw [hcorr, smul_neg, sub_eq_add_neg]
  congr 1
  rw [mul_smul_comm, mul_smul_comm]

lemma pfaffian_lift_basis (m : ℕ)
    (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ)
    (hB : ∀ k l, B k l = -B l k) (i : Fin (2*m+1+1)) :
    pfaffian (m+1) (fun k l => B k l + (if l = i then 1 else 0) -
      (if k = i then 1 else 0)) =
      pfaffian (m+1) B - (-1 : ℂ)^i.val *
        detector m (fun k l => B (i.succAbove k) (i.succAbove l)) := by
  have he := congrArg (topCoefficient (2*(m+1))) (pfaffianForm_lift_basis m B hB i)
  rw [map_sub] at he
  change pfaffian (m+1) _ = pfaffian (m+1) B -
    topCoefficient (2*m+1+1) (insertCoordinate i
      (detectorForm m (fun k l => B (i.succAbove k) (i.succAbove l)))) at he
  rw [topCoefficient_insertCoordinate] at he
  exact he

end Detector

end BassTrace

end

end OAI
