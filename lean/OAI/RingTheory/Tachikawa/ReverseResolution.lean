import OAI.RingTheory.Tachikawa.Socle

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def dualCoeff (i : Fin 10) : DualBimodule k (C k q) := LinearMap.proj i

@[simp] lemma dualCoeff_apply (i : Fin 10) (a : C k q) : dualCoeff q i a = a i := rfl

lemma e_fixed_z : e q • dualCoeff q 4 = dualCoeff q 4 := by
  ext a
  change (a * e q) 4 = a 4
  rw [mul_e]
  rfl

lemma e_fixed_j : e q • dualCoeff q 8 = dualCoeff q 8 := by
  ext a
  change (a * e q) 8 = a 8
  rw [mul_e]
  rfl

def leftDualZ : Ce q →ₗ[C k q] DualBimodule k (C k q) :=
  LeftCorner.lift (dualCoeff q 4) (e_fixed_z q)

def leftDualJ : Ce q →ₗ[C k q] DualBimodule k (C k q) :=
  LeftCorner.lift (dualCoeff q 8) (e_fixed_j q)

lemma leftDualZ_ce (a b c d t j : k) (x : C k q) :
    leftDualZ q (ce q a b c d t j) x =
      x 0*d + x 4*a + q*x 2*c + x 3*b + x 5*j + q*x 6*t := rfl

lemma leftDualJ_ce (a b c d t j : k) (x : C k q) :
    leftDualJ q (ce q a b c d t j) x =
      x 1*j + x 8*a + x 7*b + q^2*x 7*c + q*x 9*t := rfl

def leftDualAug : (Ce q × Ce q) →ₗ[C k q] DualBimodule k (C k q) :=
  (leftDualZ q).coprod (leftDualJ q)

lemma leftDualAug_surjective (hq : q ≠ 0) : Function.Surjective (leftDualAug q) := by
  intro φ
  refine ⟨(ce q (φ (basis q 4)) (φ (basis q 3)) (φ (basis q 2)/q)
    (φ (basis q 0)) (φ (basis q 6)/q) (φ (basis q 5)),
    ce q (φ (basis q 8)) (φ (basis q 7)) 0 0 (φ (basis q 9)/q) (φ (basis q 1))), ?_⟩
  change (_ : Module.Dual k (C k q)) = φ
  apply (basis q).ext
  intro i
  change leftDualZ q _ (basis q i) + leftDualJ q _ (basis q i) = φ (basis q i)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, leftDualZ_ce, leftDualJ_ce]
  fin_cases i <;> simp [basis_apply] <;> field_simp

def leftDualD₁ : Ce q →ₗ[C k q] (Ce q × Ce q) :=
  (0 : Ce q →ₗ[C k q] Ce q).prod (rhoEll q ((q^2)⁻¹))

def t : C k q := ![0,0,0,0,0,0,0,1,0,0]
lemma t_mul_e : t q * e q = t q := by rw [mul_e]; rfl

def rhoT : Cf q →ₗ[C k q] Ce q := LeftCorner.mulRight (t q) (t_mul_e q)

lemma rhoT_cf (a u v n : k) :
    rhoT q (cf q a u v n) = ce q 0 (q*u) u (q*v) a (q*n) := by
  apply Subtype.ext
  ext i
  change mul q ![0,a,0,0,0,u,v,0,0,n] (t q) i = _
  fin_cases i <;> simp [mul, t, ce]

lemma rhoT_injective (hq : q ≠ 0) : Function.Injective (rhoT q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  rw [← cf_eta q x, rhoT_cf, ce_eq_zero] at hx
  obtain ⟨_, _, hu, hv, ha, hn⟩ := hx
  rw [← cf_eta q x, cf_eq_zero]
  exact ⟨ha, hu, (mul_eq_zero.mp hv).resolve_left hq, (mul_eq_zero.mp hn).resolve_left hq⟩

lemma leftDualAug_apply (x y : Ce q) (a : C k q) :
    leftDualAug q (x,y) a =
      a 0*x.val 4 + a 4*x.val 0 + q*a 2*x.val 3 + a 3*x.val 2 +
      a 5*x.val 8 + q*a 6*x.val 7 +
      (a 1*y.val 8 + a 8*y.val 0 + a 7*y.val 2 + q^2*a 7*y.val 3 + q*a 9*y.val 7) := by
  rw [← ce_eta q x, ← ce_eta q y]
  change leftDualZ q _ a + leftDualJ q _ a = _
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, leftDualZ_ce, leftDualJ_ce]
  rfl

lemma leftDualAug_eq_zero_iff (hq : q ≠ 0) (x y : Ce q) :
    leftDualAug q (x,y) = 0 ↔ x = 0 ∧ y.val 0 = 0 ∧
      y.val 2 + q^2*y.val 3 = 0 ∧ y.val 7 = 0 ∧ y.val 8 = 0 := by
  constructor
  · intro hh
    have h (i : Fin 10) := congrArg (fun ψ : DualBimodule k (C k q) => ψ (basis q i)) hh
    simp only [leftDualAug_apply, DualBimodule.zero_apply] at h
    have hx0 : x.val 0 = 0 := by simpa [basis_apply] using h 4
    have hx2 : x.val 2 = 0 := by simpa [basis_apply] using h 3
    have hx3 : x.val 3 = 0 := by simpa [basis_apply, hq] using h 2
    have hx4 : x.val 4 = 0 := by simpa [basis_apply] using h 0
    have hx7 : x.val 7 = 0 := by simpa [basis_apply, hq] using h 6
    have hx8 : x.val 8 = 0 := by simpa [basis_apply] using h 5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← ce_eta q x, ce_eq_zero]
      exact ⟨hx0,hx2,hx3,hx4,hx7,hx8⟩
    · simpa [basis_apply] using h 8
    · simpa [basis_apply] using h 7
    · simpa [basis_apply, hq] using h 9
    · simpa [basis_apply] using h 1
  · rintro ⟨rfl, hy0, hy2, hy7, hy8⟩
    ext a
    rw [leftDualAug_apply]
    change _ = 0
    simp only [Submodule.coe_zero, zero_apply, mul_zero, add_zero, zero_add, hy0, hy7, hy8]
    calc a 7 * y.val 2 + q^2*a 7*y.val 3 = a 7 * (y.val 2 + q^2*y.val 3) := by ring
         _ = 0 := by rw [hy2, mul_zero]

variable [CharP k 2]

lemma exact_leftDualAug (hq : q ≠ 0) :
    Function.Exact (leftDualD₁ q) (leftDualAug q) := by
  rintro ⟨x,y⟩
  constructor
  · intro hh
    obtain ⟨hx, ha, hbc, ht, hj⟩ := (leftDualAug_eq_zero_iff q hq x y).mp hh
    subst x
    have hb : y.val 2 = q^2*y.val 3 := by
      have he := eq_neg_of_add_eq_zero_left hbc
      simpa only [CharTwo.neg_eq] using he
    refine ⟨ce q (q^2*y.val 3) 0 (y.val 4) 0 0 0, ?_⟩
    apply Prod.ext
    · rfl
    · change rhoEll q ((q^2)⁻¹) _ = y
      rw [rhoEll_ce]
      have hy := ce_eta q y
      rw [ha, ht, hj, hb] at hy
      simpa only [mul_zero, add_zero, zero_add, inv_mul_cancel_left₀ (pow_ne_zero 2 hq)] using hy
  · rintro ⟨z, hz⟩
    rw [← hz]
    change leftDualAug q (0, rhoEll q ((q^2)⁻¹) z) = 0
    rw [leftDualAug_eq_zero_iff q hq]
    rw [← ce_eta q z, rhoEll_ce]
    change (0 : Ce q) = 0 ∧ (0:k) = 0 ∧ z.val 0 + q^2*((q^2)⁻¹*z.val 0) = 0 ∧
      (0:k) = 0 ∧ (1+q^2*(q^2)⁻¹)*z.val 7 = 0
    simp [mul_inv_cancel₀ (pow_ne_zero 2 hq), mul_inv_cancel_left₀ (pow_ne_zero 2 hq), CharTwo.add_self_eq_zero]

lemma exact_rhoT (hq : q ≠ 0) : Function.Exact (rhoT q) (rhoEll q ((q^2)⁻¹)) := by
  intro x
  constructor
  · intro hh
    rw [← ce_eta q x, rhoEll_ce, ce_eq_zero] at hh
    obtain ⟨_, ha, _, hbc, _, _⟩ := hh
    have hc : x.val 3 = q*(q^2)⁻¹*x.val 2 := by
      have he := eq_neg_of_add_eq_zero_right hbc
      simpa only [CharTwo.neg_eq] using he
    have hb : q*x.val 3 = x.val 2 := by
      rw [hc]
      field_simp
    refine ⟨cf q (x.val 7) (x.val 3) (x.val 4/q) (x.val 8/q), ?_⟩
    rw [rhoT_cf, hb]
    have hx := ce_eta q x
    rw [ha] at hx
    simpa only [mul_div_cancel₀ _ hq] using hx
  · rintro ⟨z, rfl⟩
    rw [← cf_eta q z, rhoT_cf, rhoEll_ce, ce_eq_zero]
    have hz : q*(q^2)⁻¹*q = 1 := by field_simp
    simp only [mul_zero, mul_inv_cancel₀ (pow_ne_zero 2 hq),
      CharTwo.add_self_eq_zero, zero_mul, true_and, and_true]
    rw [← _root_.mul_assoc, hz, one_mul, CharTwo.add_self_eq_zero]

end Tachikawa.C

namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def leftDualResObj : ℕ → ModuleCat (C k q)
  | 0 => ModuleCat.of _ (Ce q × Ce q)
  | 1 => ModuleCat.of _ (Ce q)
  | 2 => ModuleCat.of _ (Cf q)
  | _+3 => ModuleCat.of _ PUnit

def leftDualResD : ∀ n, leftDualResObj q (n+1) ⟶ leftDualResObj q n
  | 0 => ModuleCat.ofHom (leftDualD₁ q)
  | 1 => ModuleCat.ofHom (rhoT q)
  | _+2 => 0

lemma leftDualResD_exact (hq : q ≠ 0) (n : ℕ) :
    Function.Exact (leftDualResD q (n+1)) (leftDualResD q n) := by
  rcases n with _ | _ | _ | n
  · change Function.Exact (rhoT q) (leftDualD₁ q)
    intro x
    change (0, rhoEll q ((q^2)⁻¹) x) = (0,0) ↔ _
    rw [Prod.mk.injEq]
    simpa only [true_and] using exact_rhoT q hq x
  · change Function.Exact (fun _ : PUnit => (0 : Cf q)) (rhoT q)
    intro x
    constructor
    · intro hx
      refine ⟨PUnit.unit, ?_⟩
      exact ((rhoT_injective q hq) (hx.trans (map_zero (rhoT q)).symm)).symm
    · rintro ⟨_, rfl⟩
      exact map_zero _
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : Cf q))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : PUnit))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩

def leftDualProjectiveResolution (hq : q ≠ 0) :
    ProjectiveResolution (ModuleCat.of (C k q) (DualBimodule k (C k q))) :=
  resolutionOfExact _ (leftDualResObj q) (leftDualResD q)
    (ModuleCat.ofHom (leftDualAug q)) (leftDualResD_exact q hq)
    (exact_leftDualAug q hq) (leftDualAug_surjective q hq) (fun n => by
      rcases n with _ | _ | _ | n <;> dsimp [leftDualResObj] <;> infer_instance)

lemma leftDual_projectiveDimension (hq : q ≠ 0) :
    HasProjectiveDimensionLE (ModuleCat.of (C k q) (DualBimodule k (C k q))) 2 := by
  let P := leftDualProjectiveResolution q hq
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (i+1) rfl
  have hs : Subsingleton (P.complex.X i) := by
    change Subsingleton (leftDualResObj q i)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_comm 3 n]
    exact inferInstanceAs (Subsingleton PUnit)
  have h : f = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [hs.elim x 0]
    exact map_zero _
  subst f
  exact P.extMk_zero _ _

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def j : C k q := ![0,0,0,0,0,0,0,0,1,0]
def x : C k q := ![0,0,1,0,0,0,0,0,0,0]
lemma j_mul_e : j q * e q = j q := by rw [mul_e]; rfl
lemma x_mul_e : x q * e q = x q := by rw [mul_e]; rfl
lemma v_mul_f : v q * f q = v q := by rw [mul_f]; rfl

def rhoJ : Cf q →ₗ[C k q] Ce q := LeftCorner.mulRight (j q) (j_mul_e q)
def rhoX : Ce q →ₗ[C k q] Ce q := LeftCorner.mulRight (x q) (x_mul_e q)
def rhoV : Ce q →ₗ[C k q] Cf q := LeftCorner.mulRight (v q) (v_mul_f q)

lemma rhoJ_cf (a u v n : k) : rhoJ q (cf q a u v n) = ce q 0 0 0 u 0 a := by
  apply Subtype.ext
  ext i
  change mul q ![0,a,0,0,0,u,v,0,0,n] (j q) i = _
  fin_cases i <;> simp [mul, j, ce]

lemma rhoX_ce (a b c d t j : k) : rhoX q (ce q a b c d t j) = ce q 0 a 0 c 0 t := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (x q) i = _
  fin_cases i <;> simp [mul, x, ce]

lemma rhoV_ce (a b c d t j : k) : rhoV q (ce q a b c d t j) = cf q 0 0 a 0 := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (v q) i = _
  fin_cases i <;> simp [mul, v, cf]

def reverseCoeff (n : ℕ) : k := (q^(n+2))⁻¹

lemma reverseCoeff_step (hq : q ≠ 0) (n : ℕ) :
    q * reverseCoeff q (n+1) = reverseCoeff q n := by
  unfold reverseCoeff
  rw [show n+1+2=(n+2)+1 by omega, pow_succ, mul_inv_rev]
  rw [← _root_.mul_assoc, mul_inv_cancel₀ hq, one_mul]

lemma one_add_inv_power_ne_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (hn : 0 < n) : 1+(q^n)⁻¹ ≠ 0 := by
  intro h
  have he : (q^n)⁻¹ = -1 := eq_neg_of_add_eq_zero_right h
  have he' := congrArg Inv.inv he
  simp only [inv_inv, inv_neg, inv_one] at he'
  exact hp n hn (by rw [he', add_neg_cancel])

lemma reverseCoeff_nonexceptional (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    1 + q^2 * reverseCoeff q (n+1) ≠ 0 := by
  have he : q^2 * reverseCoeff q (n+1) = (q^(n+1))⁻¹ := by
    unfold reverseCoeff
    rw [show n+1+2=2+(n+1) by omega, pow_add, mul_inv_rev]
    field_simp
  rw [he]
  exact one_add_inv_power_ne_zero q hp (n+1) (by omega)

variable [CharP k 2]

lemma reverseD_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Function.Exact (rhoEll q (reverseCoeff q (n+1)))
      (rhoEll q (reverseCoeff q (n+2))) := by
  rw [← reverseCoeff_step q hq (n+1)]
  apply exact_rhoEll
  · exact reverseCoeff_nonexceptional q hq hp (n+1)
  · rw [reverseCoeff_step q hq (n+1)]
    exact reverseCoeff_nonexceptional q hq hp n

lemma reverseD_comp (hq : q ≠ 0) (n : ℕ) (a : Ce q) :
    rhoEll q (reverseCoeff q (n+1)) (rhoEll q (reverseCoeff q n) a) = 0 := by
  rw [← reverseCoeff_step q hq n]
  exact rhoEll_comp_zero q _ a

omit [CharP k 2] in
lemma comparison_one (hq : q ≠ 0) :
    (rhoEll q (reverseCoeff q 0)).comp (q • rhoX q) = (rhoJ q).comp (rhoU q) := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    ← ce_eta q a, rhoX_ce, rhoEll_ce, LinearMap.comp_apply, rhoU_ce, rhoJ_cf]
  apply Subtype.ext
  ext i
  change q * (ce q 0 0 (reverseCoeff q 0 * 0)
    (q * reverseCoeff q 0 * a.val 0 + 0) 0 ((1 + q^2 * reverseCoeff q 0) * 0)).val i =
    (ce q 0 0 0 (a.val 0) 0 0).val i
  fin_cases i <;> simp [ce, reverseCoeff, hq]
  field_simp

omit [CharP k 2] in
lemma comparison_two :
    (rhoT q).comp (rhoV q) = (q • rhoX q).comp (rhoEll q 1) := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, ← ce_eta q a, rhoV_ce, rhoT_cf,
    LinearMap.comp_apply, LinearMap.smul_apply, rhoEll_ce, rhoX_ce]
  apply Subtype.ext
  ext i
  change (ce q 0 (q * 0) 0 (q * a.val 0) 0 (q * 0)).val i =
    q * (ce q 0 0 0 (1 * a.val 0) 0 0).val i
  fin_cases i <;> simp [ce]

omit [CharP k 2] in
lemma comparison_bottom : (rhoEll q (reverseCoeff q 1)).comp (rhoJ q) = 0 := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, ← cf_eta q a, rhoJ_cf, rhoEll_ce]
  simp [ce_eq_zero]

omit [CharP k 2] in
lemma comparison_top (c : k) : (rhoV q).comp (rhoEll q c) = 0 := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, ← ce_eta q a, rhoEll_ce, rhoV_ce]
  simp [cf_eq_zero]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

def forwardObj : ℤ → ModuleCat (C k q)
  | .ofNat n => resObj q n
  | .negSucc _ => ModuleCat.of _ PUnit

def forwardD : ∀ j : ℤ, forwardObj q (j+1) ⟶ forwardObj q j
  | .ofNat n => resD q n
  | .negSucc 0 => 0
  | .negSucc (_+1) => 0

lemma forwardD_comp (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    forwardD q (j+1) ≫ forwardD q j = 0 := by
  cases j with
  | ofNat n => exact ModuleCat.hom_ext <| LinearMap.ext <|
      (resD_exact q hp n).apply_apply_eq_zero
  | negSucc n =>
    cases n with
    | zero => exact comp_zero
    | succ n => exact comp_zero

def forwardComplex (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ChainComplex (ModuleCat (C k q)) ℤ :=
  ChainComplex.of (forwardObj q) (forwardD q) (forwardD_comp q hp)

def reverseObj : ℤ → ModuleCat (C k q)
  | .ofNat 0 => ModuleCat.of _ (Ce q)
  | .ofNat 1 => ModuleCat.of _ (Ce q)
  | .ofNat 2 => ModuleCat.of _ (Cf q)
  | .ofNat (_+3) => ModuleCat.of _ PUnit
  | .negSucc _ => ModuleCat.of _ (Ce q)

def reverseD : ∀ j : ℤ, reverseObj q (j+1) ⟶ reverseObj q j
  | .ofNat 0 => ModuleCat.ofHom (rhoEll q (reverseCoeff q 0))
  | .ofNat 1 => ModuleCat.ofHom (rhoT q)
  | .ofNat (_+2) => 0
  | .negSucc 0 => ModuleCat.ofHom (rhoEll q (reverseCoeff q 1))
  | .negSucc (n+1) => ModuleCat.ofHom (rhoEll q (reverseCoeff q (n+2)))

lemma reverseD_comp_zero (hq : q ≠ 0) (j : ℤ) :
    reverseD q (j+1) ≫ reverseD q j = 0 := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact ModuleCat.hom_ext <| LinearMap.ext <| (exact_rhoT q hq).apply_apply_eq_zero
    · exact zero_comp
    · exact zero_comp
  | negSucc n =>
    rcases n with _ | _ | n
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp q hq 0
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp q hq 1
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp q hq (n+2)

def reverseComplex (hq : q ≠ 0) : ChainComplex (ModuleCat (C k q)) ℤ :=
  ChainComplex.of (reverseObj q) (reverseD q) (reverseD_comp_zero q hq)

def comparisonComponent : ∀ j, forwardObj q j ⟶ reverseObj q j
  | .ofNat 0 => ModuleCat.ofHom (rhoJ q)
  | .ofNat 1 => ModuleCat.ofHom (q • rhoX q)
  | .ofNat 2 => ModuleCat.ofHom (rhoV q)
  | .ofNat (_+3) => 0
  | .negSucc _ => 0

omit [CharP k 2] in
lemma comparison_comm (hq : q ≠ 0) (j : ℤ) :
    comparisonComponent q (j+1) ≫ reverseD q j =
      forwardD q j ≫ comparisonComponent q j := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact ModuleCat.hom_ext (comparison_one q hq)
    · change ModuleCat.ofHom (rhoV q) ≫ ModuleCat.ofHom (rhoT q) =
        ModuleCat.ofHom (rhoEll q (q^0)) ≫ ModuleCat.ofHom (q • rhoX q)
      simp only [pow_zero]
      exact ModuleCat.hom_ext (comparison_two q)
    · change (0 : ModuleCat.of (C k q) (Ce q) ⟶ ModuleCat.of (C k q) PUnit) ≫ 0 =
        ModuleCat.ofHom (rhoEll q (q^1)) ≫ ModuleCat.ofHom (rhoV q)
      rw [zero_comp]
      exact (ModuleCat.hom_ext (comparison_top q _)).symm
    · change (0 : ModuleCat.of (C k q) (Ce q) ⟶ ModuleCat.of (C k q) PUnit) ≫ 0 = _ ≫ 0
      erw [zero_comp]
  | negSucc n =>
    cases n with
    | zero =>
      change ModuleCat.ofHom (rhoJ q) ≫ ModuleCat.ofHom (rhoEll q (reverseCoeff q 1)) = 0 ≫ 0
      rw [zero_comp]
      exact ModuleCat.hom_ext (comparison_bottom q)
    | succ n =>
      change 0 ≫ _ = 0 ≫ 0
      rw [zero_comp, zero_comp]

def reverseComparison (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    forwardComplex q hp ⟶ reverseComplex q hq where
  f := comparisonComponent q
  comm' i j hij := by
    have h : i = j+1 := by simpa [eq_comm] using hij
    subst i
    change comparisonComponent q (j+1) ≫ ChainComplex.of.d _ (reverseD q) (j+1) j =
      ChainComplex.of.d _ (forwardD q) (j+1) j ≫ comparisonComponent q j
    simp only [ChainComplex.of_d]
    exact comparison_comm q hq j

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [Ring R]

lemma shortComplex_quasiIso_of_cycles {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x-y) :
    ShortComplex.QuasiIso φ := by
  let f : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      change T.g (φ.τ₂ x.val) = 0
      rw [← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply, x.property, map_zero])
  have hf : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap f := by
    rintro x ⟨a,rfl⟩
    refine ⟨φ.τ₁ a, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : S.X₁ ⟶ T.X₂ => t a) φ.comm₁₂
  let fq := Submodule.mapQ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) f hf
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom f
    φH := ModuleCat.ofHom fq
    commi := rfl
    commf' := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun t : S.X₁ ⟶ T.X₂ => t x) φ.comm₁₂).symm
    commπ := rfl }
  rw [γ.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f x) = 0 at hx
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    have hz' : T.f z = φ.τ₂ x.val := congrArg Subtype.val hz
    obtain ⟨a,ha⟩ := hinj x.val x.property ⟨z,hz'⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨a, Subtype.ext ha⟩
  · intro y
    obtain ⟨y,rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x,hx,z,hz⟩ := hsurj y.val y.property
    refine ⟨Submodule.Quotient.mk ⟨x,hx⟩, ?_⟩
    change Submodule.Quotient.mk (f ⟨x,hx⟩) = Submodule.Quotient.mk y
    apply (Submodule.Quotient.eq _).mpr
    exact ⟨z, Subtype.ext hz⟩

lemma shortComplex_cycles_of_quasiIso {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hφ : ShortComplex.QuasiIso φ) :
    (∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) ∧
    (∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x-y) := by
  let f : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      change T.g (φ.τ₂ x.val) = 0
      rw [← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply, x.property, map_zero])
  have hf : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap f := by
    rintro x ⟨a,rfl⟩
    refine ⟨φ.τ₁ a, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : S.X₁ ⟶ T.X₂ => t a) φ.comm₁₂
  let fq := Submodule.mapQ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) f hf
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom f
    φH := ModuleCat.ofHom fq
    commi := rfl
    commf' := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun t : S.X₁ ⟶ T.X₂ => t x) φ.comm₁₂).symm
    commπ := rfl }
  have hbij : Function.Bijective fq := by
    have : IsIso γ.φH := γ.quasiIso_iff.mp hφ
    exact (ConcreteCategory.isIso_iff_bijective γ.φH).mp this
  constructor
  · intro x hx hbd
    have hz : fq (Submodule.Quotient.mk (⟨x,hx⟩ : LinearMap.ker S.g.hom)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      obtain ⟨z,hz⟩ := hbd
      exact ⟨z, Subtype.ext hz⟩
    have hz' := hbij.1 (hz.trans (map_zero fq).symm)
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz'
    exact ⟨z, congrArg Subtype.val hz⟩
  · intro y hy
    obtain ⟨x,hx⟩ := hbij.2 (Submodule.Quotient.mk (⟨y,hy⟩ : LinearMap.ker T.g.hom))
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f x) = Submodule.Quotient.mk ⟨y,hy⟩ at hx
    obtain ⟨z,hz⟩ := (Submodule.Quotient.eq _).mp hx
    exact ⟨x.val, x.property, z, congrArg Subtype.val hz⟩

end Tachikawa



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma comparison_injective_cycles (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (x : Cf q) (h : ∃ z : Ce q, rhoEll q (reverseCoeff q 0) z = rhoJ q x) :
    ∃ a : Ce q, rhoU q a = x := by
  obtain ⟨z,hz⟩ := h
  have he := congrArg (fun a : Ce q => a.val 8) hz
  rw [← ce_eta q z, rhoEll_ce, ← cf_eta q x, rhoJ_cf] at he
  change (1 + q^2 * reverseCoeff q 0) * z.val 7 = x.val 1 at he
  have hzero : 1+q^2*reverseCoeff q 0 = 0 := by
    simp [reverseCoeff, hq, CharTwo.add_self_eq_zero]
  rw [hzero, zero_mul] at he
  apply (exact_augmentation q (by simpa only [pow_one] using hp 1 (by omega)) x).mp
  exact he.symm

lemma comparison_surjective_cycles (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (y : Ce q) (h : rhoEll q (reverseCoeff q 1) y = 0) :
    ∃ x : Cf q, ∃ z : Ce q, rhoEll q (reverseCoeff q 0) z = rhoJ q x-y := by
  rw [← ce_eta q y, rhoEll_ce, ce_eq_zero] at h
  obtain ⟨_, ha, _, hb, _, ht⟩ := h
  have ht' : y.val 7 = 0 := (mul_eq_zero.mp ht).resolve_left
    (reverseCoeff_nonexceptional q hq hp 0)
  have hc : y.val 3 = reverseCoeff q 0 * y.val 2 := by
    rw [← reverseCoeff_step q hq 0]
    have he := eq_neg_of_add_eq_zero_left hb
    simpa only [CharTwo.neg_eq] using he.symm
  have hy := ce_eta q y
  rw [ha,ht',hc] at hy
  refine ⟨cf q (y.val 8) 0 0 0, ce q (y.val 2) 0 (y.val 4) 0 0 0, ?_⟩
  rw [rhoEll_ce, rhoJ_cf]
  conv_rhs => rw [← hy]
  apply Subtype.ext
  ext i
  change (ce q 0 (y.val 2) (reverseCoeff q 0 * y.val 2)
    (q * reverseCoeff q 0 * 0 + y.val 4) 0 ((1+q^2*reverseCoeff q 0)*0)).val i =
    (ce q 0 0 0 0 0 (y.val 8)).val i -
    (ce q 0 (y.val 2) (reverseCoeff q 0 * y.val 2) (y.val 4) 0 (y.val 8)).val i
  fin_cases i <;> simp [ce, CharTwo.neg_eq]

lemma forwardComplex_exactAt (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) : (forwardComplex q hp).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, ChainComplex.of.d _ (forwardD q) (i+1) i x = 0 →
    ∃ y, ChainComplex.of.d _ (forwardD q) (i+1+1) (i+1) y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n => exact fun x hx => (resD_exact q hp n x).mp hx
  | negSucc n =>
    cases n with
    | zero => exact (hj rfl).elim
    | succ n =>
      intro x _
      exact ⟨0, @Subsingleton.elim PUnit inferInstance _ _⟩

lemma reverseComplex_exactAt (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) : (reverseComplex q hq).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, ChainComplex.of.d _ (reverseD q) (i+1) i x = 0 →
    ∃ y, ChainComplex.of.d _ (reverseD q) (i+1+1) (i+1) y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact fun x hx => (exact_rhoT q hq x).mp hx
    · intro x hx
      refine ⟨0, ?_⟩
      exact (rhoT_injective q hq (hx.trans (map_zero (rhoT q)).symm)).symm
    · intro x _
      exact ⟨0, @Subsingleton.elim PUnit inferInstance _ _⟩
  | negSucc n =>
    rcases n with _ | _ | n
    · exact (hj rfl).elim
    · exact fun x hx => (reverseD_exact q hq hp 0 x).mp hx
    · exact fun x hx => (reverseD_exact q hq hp (n+1) x).mp hx

lemma reverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : QuasiIso (reverseComparison q hq hp) := by
  constructor
  intro j
  by_cases hj : j = 0
  · subst j
    rw [quasiIsoAt_iff' _ 1 0 (-1) (by simp) (by simp)]
    apply shortComplex_quasiIso_of_cycles
    · intro x _ hx
      exact comparison_injective_cycles q hq hp x hx
    · intro y hy
      obtain ⟨x,z,hz⟩ := comparison_surjective_cycles q hq hp y hy
      exact ⟨x, rfl, z, hz⟩
  · have hS := forwardComplex_exactAt q hp j hj
    have hT := reverseComplex_exactAt q hq hp j hj
    exact (quasiIsoAt_iff_exactAt (reverseComparison q hq hp) j hS).mpr hT

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma f_mul_t : f q * t q = t q := by rw [f_mul]; rfl

def lambdaT : eC q →ₗ[(C k q)ᵐᵒᵖ] fC q := RightCorner.mulLeft (t q) (f_mul_t q)

lemma lambdaT_ec (a b c d u v : k) :
    lambdaT q (ec q a b c d u v) = fc q 0 a (b+q^2*c) ((1+q)*u) := by
  apply Subtype.ext
  ext i
  change mul q (t q) ![a,0,b,c,d,u,v,0,0,0] i = _
  fin_cases i <;> simp [mul, t, fc]

variable [CharP k 2]

lemma exact_lambdaT (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Exact (lambdaEll q (reverseCoeff q 0)) (lambdaT q) := by
  intro x
  constructor
  · intro h
    rw [← ec_eta q x, lambdaT_ec, fc_eq_zero] at h
    obtain ⟨_,ha,hbc,hu⟩ := h
    have hu' : x.val 5 = 0 := (mul_eq_zero.mp hu).resolve_left (by simpa only [pow_one] using hp 1 (by omega))
    have hc : x.val 3 = reverseCoeff q 0 * x.val 2 := by
      have hb : x.val 2 = q^2*x.val 3 := by
        simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hbc
      rw [hb, reverseCoeff, Nat.zero_add]
      field_simp
    have hz : 1+reverseCoeff q 0 ≠ 0 :=
      one_add_inv_power_ne_zero q hp 2 (by omega)
    refine ⟨ec q (x.val 2) 0 (x.val 4/q) 0 (x.val 6/(1+reverseCoeff q 0)) 0, ?_⟩
    rw [lambdaEll_ec]
    have he := ec_eta q x
    rw [ha,hu',hc] at he
    simpa only [mul_zero, zero_add, mul_div_cancel₀ _ hq, mul_div_cancel₀ _ hz] using he
  · rintro ⟨x,rfl⟩
    rw [← ec_eta q x, lambdaEll_ec, lambdaT_ec, fc_eq_zero]
    simp [reverseCoeff, hq, CharTwo.add_self_eq_zero]

lemma hom_exact_rhoEll_general (hq : q ≠ 0) (z : k)
    (hz : 1+z ≠ 0) (hz' : 1+q*z ≠ 0) : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoEll q z))
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (q*z))) := by
  intro f
  constructor
  · intro hf
    have hh := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
    have hz0 : lambdaEll q (q*z) (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      simpa only [homPrecomp_apply, rhoEll, lambdaEll,
        RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q)
          (ell q (q*z)) (e_mul_ell q _) (ell_mul_e q _), map_zero] using hh
    obtain ⟨a,ha⟩ := (exact_lambdaEll q hq z hz hz' _).mp hz0
    refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q)
      (((RightCorner.homEquiv (e_idempotent q)).symm a).comp (rhoEll q z)) = _
    rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q)
      (ell q z) (e_mul_ell q _) (ell_mul_e q _)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoEll q z (rhoEll q (q*z) x)) = 0
    rw [rhoEll_comp_zero, map_zero]

lemma hom_exact_rhoT (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (reverseCoeff q 0)))
    (homPrecomp (k := k) (Z := C k q) (rhoT q)) := by
  intro f
  constructor
  · intro hf
    have hh := congrArg (RightCorner.homEquiv (f_idempotent q)) hf
    have hz : lambdaT q (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      simpa only [homPrecomp_apply, rhoT, lambdaT,
        RightCorner.homEquiv_precomp (f_idempotent q) (e_idempotent q)
          (t q) (f_mul_t q) (t_mul_e q), map_zero] using hh
    obtain ⟨a,ha⟩ := (exact_lambdaT q hq hp _).mp hz
    refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q)
      (((RightCorner.homEquiv (e_idempotent q)).symm a).comp (rhoEll q (reverseCoeff q 0))) = _
    rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q)
      (ell q _) (e_mul_ell q _) (ell_mul_e q _)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoEll q ((q^2)⁻¹) (rhoT q x)) = 0
    rw [(exact_rhoT q hq).apply_apply_eq_zero, map_zero]

lemma nu_reverseEll_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) : Function.Exact
    (Nakayama.map (k := k) (rhoEll q (reverseCoeff q n)))
    (Nakayama.map (rhoEll q (reverseCoeff q (n+1)))) := by
  rw [← reverseCoeff_step q hq n]
  exact exact_dual _ _ (hom_exact_rhoEll_general q hq _
    (one_add_inv_power_ne_zero q hp (n+1+2) (by omega))
    (by change 1+q*reverseCoeff q (n+1) ≠ 0; rw [reverseCoeff_step q hq n]; exact one_add_inv_power_ne_zero q hp (n+2) (by omega)))

lemma nu_reverseTop_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : Function.Exact
    (Nakayama.map (k := k) (rhoT q))
    (Nakayama.map (rhoEll q (reverseCoeff q 0))) :=
  exact_dual _ _ (hom_exact_rhoT q hq hp)

end Tachikawa.C



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

def fHom : Cf q →ₗ[C k q] C k q := LeftCorner.lift (f q) (f_idempotent q)

omit [CharP k 2] in
lemma homEquiv_fHom : RightCorner.homEquiv (f_idempotent q) (fHom q) = fc q 1 0 0 0 :=
  Subtype.ext (LeftCorner.lift_generator (f_idempotent q) _ _)

omit [CharP k 2] in
lemma fHom_rhoV : (fHom q).comp (rhoV q) = vHom q := by
  apply (RightCorner.homEquiv (e_idempotent q)).injective
  rw [rhoV, RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q)
    (v q) (e_mul_v q) (v_mul_f q), homEquiv_fHom, homEquiv_vHom]
  apply Subtype.ext
  change v q * (fc q 1 0 0 0).val = (ec q 0 0 0 0 0 1).val
  ext i
  change mul q (v q) _ i = _
  fin_cases i <;> simp [mul, v, fc, ec]

def nuTopCycle : Nakayama k (C k q) (Cf q) where
  toFun g := (g (LeftCorner.generator (f_idempotent q))) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharP k 2] in
lemma nuV_nuTwoCycle : Nakayama.map (k := k) (rhoV q) (nuTwoCycle q) = nuTopCycle q := by
  apply LinearMap.ext
  intro g
  have h := RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q)
    (v q) (e_mul_v q) (v_mul_f q) g
  change ((g.comp (rhoV q)) (LeftCorner.generator (e_idempotent q))) 6 = _
  change (RightCorner.homEquiv (e_idempotent q) (g.comp (rhoV q))).val 6 = _
  rw [rhoV, h]
  change mul q (v q) (g (LeftCorner.generator (f_idempotent q))) 6 = _
  simp [mul, v, nuTopCycle]
  rfl

omit [CharP k 2] in
lemma homTop_decompose (hq1 : 1+q ≠ 0) (g : Cf q →ₗ[C k q] C k q) :
    ∃ h : Ce q →ₗ[C k q] C k q,
      g = h.comp (rhoT q) +
        ((RightCorner.homEquiv (f_idempotent q) g).val 1) • fHom q := by
  let a := RightCorner.homEquiv (f_idempotent q) g
  let b := ec q (a.val 7) (a.val 8) 0 0 (a.val 9/(1+q)) 0
  refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm b, ?_⟩
  apply (RightCorner.homEquiv (f_idempotent q)).injective
  rw [map_add]
  change (a : fC q) = _ + _
  have hcomp : RightCorner.homEquiv (f_idempotent q)
      (((RightCorner.homEquiv (e_idempotent q)).symm b).comp (rhoT q)) = lambdaT q b := by
    rw [rhoT, RightCorner.homEquiv_precomp (f_idempotent q) (e_idempotent q)
      (t q) (f_mul_t q) (t_mul_e q), LinearEquiv.apply_symm_apply]
    rfl
  rw [hcomp]
  have hsmul : RightCorner.homEquiv (f_idempotent q) (a.val 1 • fHom q) =
      a.val 1 • fc q 1 0 0 0 := by
    exact (RightCorner.homEquivScalar (k := k) (f_idempotent q)).map_smul _ _ |>.trans
      (congrArg (fun x : fC q => a.val 1 • x) (homEquiv_fHom q))
  rw [hsmul]
  dsimp only [b]
  rw [lambdaT_ec, mul_zero, add_zero, mul_div_cancel₀ _ hq1]
  rw [← fc_eta q a]
  apply Subtype.ext
  ext i
  change (fc q (a.val 1) (a.val 7) (a.val 8) (a.val 9)).val i =
    (fc q 0 (a.val 7) (a.val 8) (a.val 9)).val i + a.val 1 * (fc q 1 0 0 0).val i
  fin_cases i <;> simp [fc]

omit [CharP k 2] in
lemma nuTopCycle_description (hq1 : 1+q ≠ 0) (ψ : Nakayama k (C k q) (Cf q))
    (hψ : Nakayama.map (rhoT q) ψ = 0) : ψ = ψ (fHom q) • nuTopCycle q := by
  apply LinearMap.ext
  intro g
  obtain ⟨h,hg⟩ := homTop_decompose q hq1 g
  have hh : ψ (h.comp (rhoT q)) = 0 := LinearMap.congr_fun hψ h
  conv_lhs => erw [hg, map_add, hh, zero_add, map_smul]
  change (g (LeftCorner.generator (f_idempotent q))) 1 * ψ (fHom q) = ψ (fHom q) * (g (LeftCorner.generator (f_idempotent q))) 1
  exact mul_comm _ _

lemma nuV_cycles_injective (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Ce q))
    (hψ : Nakayama.map (rhoEll q 1) ψ = 0)
    (hV : Nakayama.map (rhoV q) ψ = 0) :
    ∃ ξ, Nakayama.map (rhoEll q q) ξ = ψ := by
  apply (nuTwo_boundary_iff q hq hq1 ψ hψ).mp
  have h := LinearMap.congr_fun hV (fHom q)
  change ψ ((fHom q).comp (rhoV q)) = 0 at h
  rw [fHom_rhoV] at h
  exact h

lemma nuV_cycles_surjective (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Cf q))
    (hψ : Nakayama.map (rhoT q) ψ = 0) :
    ∃ ξ : Nakayama k (C k q) (Ce q),
      Nakayama.map (rhoEll q 1) ξ = 0 ∧ Nakayama.map (rhoV q) ξ = ψ := by
  refine ⟨ψ (fHom q) • nuTwoCycle q, ?_, ?_⟩
  · rw [LinearMap.map_smul_of_tower, nuTwoCycle_closed, smul_zero]
  · rw [LinearMap.map_smul_of_tower, nuV_nuTwoCycle]
    exact (nuTopCycle_description q hq1 ψ hψ).symm

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma nuForward_exactAt (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 2) :
    (Nakayama.complex (k := k) (forwardComplex q hp)).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, Nakayama.map (ChainComplex.of.d _ (forwardD q) (i+1) i).hom x = 0 →
    ∃ y, Nakayama.map (ChainComplex.of.d _ (forwardD q) (i+1+1) (i+1)).hom y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n => exact fun x hx => (nu_resD_exact q hq hp n (by intro hn; subst n; exact hj rfl) x).mp hx
  | negSucc n =>
    cases n with
    | zero => exact fun x _ => nu_rhoU_surjective q x
    | succ n =>
      intro x _
      refine ⟨0, ?_⟩
      exact @Subsingleton.elim ((PUnit →ₗ[C k q] C k q) →ₗ[k] k) inferInstance _ _

lemma nuReverse_exactAt (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 2) :
    (Nakayama.complex (k := k) (reverseComplex q hq)).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, Nakayama.map (ChainComplex.of.d _ (reverseD q) (i+1) i).hom x = 0 →
    ∃ y, Nakayama.map (ChainComplex.of.d _ (reverseD q) (i+1+1) (i+1)).hom y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact fun x hx => (nu_reverseTop_exact q hq hp x).mp hx
    · exact (hj rfl).elim
    · intro x _
      exact ⟨0, @Subsingleton.elim ((PUnit →ₗ[C k q] C k q) →ₗ[k] k) inferInstance _ _⟩
  | negSucc n =>
    rcases n with _ | _ | n
    · exact fun x hx => (nu_reverseEll_exact q hq hp 0 x).mp hx
    · exact fun x hx => (nu_reverseEll_exact q hq hp 1 x).mp hx
    · exact fun x hx => (nu_reverseEll_exact q hq hp (n+2) x).mp hx

lemma nuReverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    QuasiIso (((Nakayama.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).map
      (reverseComparison q hq hp)) := by
  constructor
  intro j
  by_cases hj : j = 2
  · subst j
    rw [quasiIsoAt_iff' _ 3 2 1 (by simp) (by simp)]
    apply shortComplex_quasiIso_of_cycles
    · intro x hx hb
      obtain ⟨z,hz⟩ := hb
      change Nakayama.map (rhoEll q (q^0)) x = 0 at hx
      rw [pow_zero] at hx
      have hV : Nakayama.map (rhoV q) x = 0 := by
        change Nakayama.map (0 : PUnit →ₗ[C k q] Cf q) z = Nakayama.map (rhoV q) x at hz
        erw [Nakayama.map_zero, LinearMap.zero_apply] at hz
        exact hz.symm
      obtain ⟨ξ,hξ⟩ := nuV_cycles_injective q hq (by simpa only [pow_one] using hp 1 (by omega)) x hx hV
      refine ⟨ξ, ?_⟩
      change Nakayama.map (rhoEll q (q^1)) ξ = x
      simpa only [pow_one] using hξ
    · intro y hy
      obtain ⟨x,hx,hV⟩ := nuV_cycles_surjective q (by simpa only [pow_one] using hp 1 (by omega)) y hy
      refine ⟨x, ?_, 0, ?_⟩
      · change Nakayama.map (rhoEll q (q^0)) x = 0
        simpa only [pow_zero] using hx
      · change Nakayama.map (0 : PUnit →ₗ[C k q] Cf q) 0 = Nakayama.map (rhoV q) x - (show Nakayama k (C k q) (Cf q) from y)
        erw [map_zero, hV, sub_self]
  · exact (quasiIsoAt_iff_exactAt _ j (nuForward_exactAt q hq hp j hj)).mpr
      (nuReverse_exactAt q hq hp j hj)

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace TrivialInduction

lemma quasiIso_map {P Q : ChainComplex (ModuleCat R) ℤ} (f : P ⟶ Q)
    (hf : QuasiIso f)
    (hν : QuasiIso (((Nakayama.functor (k := k)).mapHomologicalComplex _).map f)) :
    QuasiIso (((functor (k := k)).mapHomologicalComplex _).map f) := by
  let := hf
  let := hν
  constructor
  intro j
  rw [quasiIsoAt_iff' _ (j+1) j (j-1) (by simp) (by simp)]
  have hf' := shortComplex_cycles_of_quasiIso _
    ((quasiIsoAt_iff' f (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
  have hν' := shortComplex_cycles_of_quasiIso _
    ((quasiIsoAt_iff' (((Nakayama.functor (k := k)).mapHomologicalComplex _).map f)
      (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
  apply shortComplex_quasiIso_of_cycles
  · intro x hx hbd
    obtain ⟨z,hz⟩ := hbd
    obtain ⟨a,ha⟩ := hf'.1 x.1 (congrArg Prod.fst hx) ⟨z.1, congrArg Prod.fst hz⟩
    obtain ⟨b,hb⟩ := hν'.1 x.2 (congrArg Prod.snd hx) ⟨z.2, congrArg Prod.snd hz⟩
    exact ⟨(a,b), Prod.ext ha hb⟩
  · intro y hy
    obtain ⟨a,ha,z,hz⟩ := hf'.2 y.1 (congrArg Prod.fst hy)
    obtain ⟨b,hb,w,hw⟩ := hν'.2 y.2 (congrArg Prod.snd hy)
    exact ⟨(a,b), Prod.ext ha hb, (z,w), Prod.ext hz hw⟩
end TrivialInduction
end Tachikawa



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def inducedReverseComparison (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  ((TrivialInduction.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).map
    (reverseComparison q hq hp)

lemma inducedReverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    QuasiIso (inducedReverseComparison q hq hp) :=
  TrivialInduction.quasiIso_map _ (reverseComparison_quasiIso q hq hp)
    (nuReverseComparison_quasiIso q hq hp)

end Tachikawa.C

end


namespace Tachikawa

instance downIntTensorSigns : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q+1=p) := by
    change q + r + 1 = p + r
    omega
  add_rel p q r (hpq : q+1=p) := by
    change r + q + 1 = r + p
    omega
  ε'_succ := by
    rintro _ q rfl
    change Int.negOnePow q = -Int.negOnePow (q + 1)
    rw [Int.negOnePow_succ, neg_neg]
end Tachikawa



noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k]

lemma zeroDifferential_isIso_of_quasiIso
    {K L : ChainComplex (ModuleCat k) ℤ} (f : K ⟶ L)
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) [QuasiIso f] : IsIso f := by
  have (j : ℤ) : IsIso (f.f j) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hh := shortComplex_cycles_of_quasiIso _
      ((quasiIsoAt_iff' f (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨z,hz⟩ := hh.1 x (by change K.d j (j-1) x = 0; rw [hK]; rfl)
        ⟨0, by change L.d (j+1) j 0 = f.f j x; rw [map_zero]; exact hx.symm⟩
      change K.d (j+1) j z = x at hz
      rw [hK] at hz
      exact hz.symm
    · intro y
      obtain ⟨x,_,z,hz⟩ := hh.2 y (by change L.d j (j-1) y = 0; rw [hL]; rfl)
      refine ⟨x, ?_⟩
      change L.d (j+1) j z = f.f j x - y at hz
      rw [hL] at hz
      exact sub_eq_zero.mp hz.symm
  exact HomologicalComplex.Hom.isIso_of_components f

lemma vectorTensor_quasiIso_int
    {K L M N : ChainComplex (ModuleCat k) ℤ} (f : K ⟶ L) (g : M ⟶ N)
    [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)) (.down ℤ)) := by
  let F := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)
  let ef := VectorSplit.homologyHomotopyEquiv K
  let el := VectorSplit.homologyHomotopyEquiv L
  let em := VectorSplit.homologyHomotopyEquiv M
  let en := VectorSplit.homologyHomotopyEquiv N
  let := ef.quasiIso_inv
  let := el.quasiIso_hom
  let := em.quasiIso_inv
  let := en.quasiIso_hom
  let f' := ef.inv ≫ f ≫ el.hom
  let g' := em.inv ≫ g ≫ en.hom
  have : IsIso f' := zeroDifferential_isIso_of_quasiIso f' (fun _ _ => rfl) (fun _ _ => rfl)
  have : IsIso g' := zeroDifferential_isIso_of_quasiIso g' (fun _ _ => rfl) (fun _ _ => rfl)
  let ei := bifunctorHomotopyEquiv F (.down ℤ) ef.symm em.symm
  let ep := bifunctorHomotopyEquiv F (.down ℤ) el en
  let := ei.quasiIso_hom
  let := ep.quasiIso_hom
  have hh : QuasiIso (ei.hom ≫ mapBifunctorMap f g F (.down ℤ) ≫ ep.hom) := by
    change QuasiIso (mapBifunctorMap ef.inv em.inv F (.down ℤ) ≫
      mapBifunctorMap f g F (.down ℤ) ≫ mapBifunctorMap el.hom en.hom F (.down ℤ))
    rw [bifunctorMap_comp, bifunctorMap_comp]
    change QuasiIso (mapBifunctorMap f' g' F (.down ℤ))
    exact (bifunctorHomotopyEquiv F (.down ℤ) (HomotopyEquiv.ofIso (asIso f')) (HomotopyEquiv.ofIso (asIso g'))).quasiIso_hom
  exact (quasiIso_iff_comp_right _ ep.hom).mp ((quasiIso_iff_comp_left ei.hom _).mp hh)

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℤ} {L L' : ChainComplex (ModuleCat B) ℤ}

lemma quasiIso_int (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (.down ℤ)) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (forgetE k A B)).mp
  rw [← quasiIso_iff_comp_right _ (forgetTotalIso k A B K' L' (.down ℤ)).hom,
    forgetTotalIso_natural]
  have := vectorTensor_quasiIso_int (((forgetA k A).mapHomologicalComplex (.down ℤ)).map f)
    (((forgetB k B).mapHomologicalComplex (.down ℤ)).map g)
  infer_instance

end Tachikawa.OuterTensor



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev forwardJ (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  ((TrivialInduction.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (C.forwardComplex q hp)

abbrev reverseJ (hq : q ≠ 0) :=
  ((TrivialInduction.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (C.reverseComplex q hq)

abbrev forwardJJ (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  mapBifunctor (forwardJ q hp) (forwardJ q hp)
    (OuterTensor.bifunctor k (C.T q) (C.T q)) (.down ℤ)

abbrev reverseJJ (hq : q ≠ 0) :=
  mapBifunctor (reverseJ q hq) (reverseJ q hq)
    (OuterTensor.bifunctor k (C.T q) (C.T q)) (.down ℤ)

def jjReverseComparison (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : forwardJJ q hp ⟶ reverseJJ q hq :=
  mapBifunctorMap (C.inducedReverseComparison q hq hp) (C.inducedReverseComparison q hq hp)
    (OuterTensor.bifunctor k (C.T q) (C.T q)) (.down ℤ)

lemma jjReverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : QuasiIso (jjReverseComparison q hq hp) := by
  let := C.inducedReverseComparison_quasiIso q hq hp
  exact OuterTensor.quasiIso_int k (C.T q) (C.T q) _ _

end Tachikawa.Construction



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma map_id_underlying {M : ModuleCat A} {N N' : ModuleCat B} (g : N ⟶ N') :
    (map (k := k) (𝟙 M) g).restrictScalars k = (g.hom.restrictScalars k).lTensor M := rfl

lemma map_id_right_underlying {M M' : ModuleCat A} {N : ModuleCat B} (f : M ⟶ M') :
    (map (k := k) f (𝟙 N)).restrictScalars k = (f.hom.restrictScalars k).rTensor N := rfl

instance (N : ModuleCat B) : ((bifunctor k A B).flip.obj N).Additive where
  map_add {_X _Y} f f' := ModuleCat.hom_ext (map_add_left f f' (𝟙 N))

lemma exact_map_left (M : ModuleCat A) (S : ShortComplex (ModuleCat B)) (hS : S.Exact) :
    (S.map ((bifunctor k A B).obj M)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact M (show Function.Exact (S.f.hom.restrictScalars k)
    (S.g.hom.restrictScalars k) from hS)

lemma exact_map_right (N : ModuleCat B) (S : ShortComplex (ModuleCat A)) (hS : S.Exact) :
    (S.map ((bifunctor k A B).flip.obj N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact N (show Function.Exact (S.f.hom.restrictScalars k)
    (S.g.hom.restrictScalars k) from hS)

instance (M : ModuleCat A) : PreservesFiniteLimits ((bifunctor k A B).obj M) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  refine ⟨exact_map_left M S hS.exact, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := M)
    (S.f.hom.restrictScalars k) ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

instance (M : ModuleCat A) : PreservesFiniteColimits ((bifunctor k A B).obj M) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  refine ⟨exact_map_left M S hS.exact, ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  exact LinearMap.lTensor_surjective M ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

instance (N : ModuleCat B) : PreservesFiniteLimits ((bifunctor k A B).flip.obj N) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  refine ⟨exact_map_right N S hS.exact, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := N)
    (S.f.hom.restrictScalars k) ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

instance (N : ModuleCat B) : PreservesFiniteColimits ((bifunctor k A B).flip.obj N) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  refine ⟨exact_map_right N S hS.exact, ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  exact LinearMap.rTensor_surjective N ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

instance objFinite (M : ModuleCat.{0} A) (N : ModuleCat.{0} B)
    [FiniteDimensional k M] [FiniteDimensional k N] :
    Module.Finite (A ⊗[k] B) (Obj k A B M N) := by
  have : FiniteDimensional k (Obj k A B M N) := inferInstanceAs (FiniteDimensional k (M ⊗[k] N))
  exact Module.Finite.of_restrictScalars_finite k _ _

lemma isZero_obj_left (M : ModuleCat.{0} A) (N : ModuleCat.{0} B) (h : IsZero M) :
    IsZero (((bifunctor k A B).obj M).obj N) :=
  ((bifunctor k A B).flip.obj N).map_isZero h

lemma isZero_obj_right (M : ModuleCat.{0} A) (N : ModuleCat.{0} B) (h : IsZero N) :
    IsZero (((bifunctor k A B).obj M).obj N) := ((bifunctor k A B).obj M).map_isZero h

lemma total_isZero_above (P : ChainComplex (ModuleCat.{0} A) ℕ)
    (Q : ChainComplex (ModuleCat.{0} B) ℕ) (a b : ℕ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℕ) (hn : a+b < n) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℕ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : a < i
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

lemma total_finite (P : ChainComplex (ModuleCat.{0} A) ℕ)
    (Q : ChainComplex (ModuleCat.{0} B) ℕ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (n : ℕ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℕ)).X n) := by
  let : Finite {ij : ℕ × ℕ // ij.1+ij.2=n} := by
    let f : {ij : ℕ × ℕ // ij.1+ij.2=n} → Fin (n+1) × Fin (n+1) := fun t =>
      (⟨t.val.1, by omega⟩, ⟨t.val.2, by omega⟩)
    exact Finite.of_injective f (by intro x y h; apply Subtype.ext; exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h))
  let F := fun ij : {ij : ℕ × ℕ // ij.1+ij.2=n} =>
    ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let (i : ℕ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℕ) : FiniteDimensional k (Q.X j) := hQ j
  have (t : {ij : ℕ × ℕ // ij.1+ij.2=n}) : Module.Finite (A ⊗[k] B) (F t) := objFinite _ _
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  exact Module.Finite.equiv ((biproduct.isoCoproduct F).symm ≪≫ ModuleCat.biproductIsoPi F).toLinearEquiv.symm

end Tachikawa.OuterTensor



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type} [Ring R] {ι : Type}

def coproductSupportIso (F : ι → ModuleCat R) (p : ι → Prop)
    (hz : ∀ i, ¬p i → IsZero (F i)) : (∐ F) ≅ ∐ (fun i : {i // p i} => F i.val) := by
  classical
  refine {
    hom := Sigma.desc fun i => if h : p i then Sigma.ι (fun i : {i // p i} => F i.val) ⟨i,h⟩ else 0
    inv := Sigma.desc fun i => Sigma.ι F i.val
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc]
    by_cases h : p i
    · simp only [dite_eq_left h, Sigma.ι_comp_desc, Category.comp_id]
    · simp only [dite_eq_right h, zero_comp, Category.comp_id]
      exact (hz i h).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, dite_eq_left i.property, Category.comp_id]

lemma coproduct_finite_of_support (F : ι → ModuleCat R) (p : ι → Prop)
    [Finite {i // p i}] (hz : ∀ i, ¬p i → IsZero (F i))
    (hf : ∀ i, Module.Finite R (F i)) : Module.Finite R (∐ F : ModuleCat R) := by
  let (i : {i // p i}) : Module.Finite R (F i.val) := hf i.val
  let J := fun i : {i // p i} => F i.val
  exact Module.Finite.equiv (((coproductSupportIso F p hz) ≪≫
    (biproduct.isoCoproduct J).symm ≪≫ ModuleCat.biproductIsoPi J).toLinearEquiv.symm)

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)

lemma total_projective_int (hP : ∀ i, Module.Finite A (P.X i))
    (hQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i))
    (pQ : ∀ j, Module.Projective B (Q.X j)) (n : ℤ) :
    Projective ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let (i : ℤ) : Module.Finite A (P.X i) := hP i
  let (j : ℤ) : Module.Finite B (Q.X j) := hQ j
  let (i : ℤ) : Module.Projective A (P.X i) := pP i
  let (j : ℤ) : Module.Projective B (Q.X j) := pQ j
  have (i j : ℤ) : Module.Projective (A ⊗[k] B) (Obj k A B (P.X i) (Q.X j)) :=
    projective k A B _ _
  have (i j : ℤ) : Projective (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    change Projective (ModuleCat.of (A ⊗[k] B) (Obj k A B (P.X i) (Q.X j)))
    infer_instance
  change Projective (∐ fun ij : {ij : ℤ × ℤ // ij.1+ij.2=n} =>
    ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2))
  infer_instance

lemma total_isZero_below_int (a b : ℤ)
    (hP : ∀ i, i < a → IsZero (P.X i)) (hQ : ∀ j, j < b → IsZero (Q.X j))
    (n : ℤ) (hn : n < a+b) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : i < a
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

lemma total_isZero_above_int (a b : ℤ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℤ) (hn : a+b < n) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : a < i
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

lemma total_finite_below_int (a b : ℤ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (zP : ∀ i, i < a → IsZero (P.X i)) (zQ : ∀ j, j < b → IsZero (Q.X j))
    (n : ℤ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=n}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let p : I → Prop := fun ij => a ≤ ij.val.1 ∧ b ≤ ij.val.2
  let : Finite {i // p i} := by
    let f : {i // p i} → Set.Icc a (n-b) := fun i => ⟨i.val.val.1, by
      have h := i.property
      have hi := i.val.property
      dsimp [p] at h
      exact ⟨h.1, by omega⟩⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.val) h
    · have hh := congrArg (fun z => z.val) h
      have hx := x.val.property
      have hy := y.val.property
      change x.val.val.1 = y.val.val.1 at hh
      omega
  let (i : ℤ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℤ) : FiniteDimensional k (Q.X j) := hQ j
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  apply coproduct_finite_of_support F p
  · intro i hi
    by_cases h : a ≤ i.val.1
    · exact isZero_obj_right _ _ (zQ i.val.2 (by dsimp [p] at hi; omega))
    · exact isZero_obj_left _ _ (zP i.val.1 (by omega))
  · intro i
    exact objFinite _ _

lemma total_finite_above_int (a b : ℤ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (zP : ∀ i, a < i → IsZero (P.X i)) (zQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℤ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=n}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let p : I → Prop := fun ij => ij.val.1 ≤ a ∧ ij.val.2 ≤ b
  let : Finite {i // p i} := by
    let f : {i // p i} → Set.Icc (n-b) a := fun i => ⟨i.val.val.1, by
      have h := i.property
      have hi := i.val.property
      dsimp [p] at h
      exact ⟨by omega,h.1⟩⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.val) h
    · have hh := congrArg (fun z => z.val) h
      have hx := x.val.property
      have hy := y.val.property
      change x.val.val.1 = y.val.val.1 at hh
      omega
  let (i : ℤ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℤ) : FiniteDimensional k (Q.X j) := hQ j
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  apply coproduct_finite_of_support F p
  · intro i hi
    by_cases h : i.val.1 ≤ a
    · exact isZero_obj_right _ _ (zQ i.val.2 (by dsimp [p] at hi; omega))
    · exact isZero_obj_left _ _ (zP i.val.1 (by omega))
  · intro i
    exact objFinite _ _

end Tachikawa.OuterTensor

end

end OAI
