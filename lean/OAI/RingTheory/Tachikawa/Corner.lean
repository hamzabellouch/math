import OAI.RingTheory.Tachikawa.Nakayama

namespace OAI


noncomputable section
namespace Tachikawa

def LeftCorner {R : Type*} [Ring R] (p : R) : Submodule R R where
  carrier := {a | a * p = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a * p = a at ha
    change b * p = b at hb
    change (a + b) * p = a + b
    rw [add_mul, ha, hb]
  smul_mem' := by intro a b hb; change (a * b) * p = a * b; rw [mul_assoc, hb]

@[simp] lemma mem_leftCorner {R : Type*} [Ring R] (p a : R) :
    a ∈ LeftCorner p ↔ a * p = a := Iff.rfl

namespace LeftCorner
variable {R : Type*} [Ring R] {p : R} (hp : p * p = p)

def generator : LeftCorner p := ⟨p, hp⟩

def projection : R →ₗ[R] LeftCorner p :=
  (LinearMap.mulRight R p).codRestrict (LeftCorner p) (fun a => by
    change (a * p) * p = a * p
    rw [mul_assoc, hp])

@[simp] lemma projection_apply (a : R) : (projection hp a : R) = a * p := rfl

lemma projection_comp_inclusion : (projection hp).comp (LeftCorner p).subtype = LinearMap.id := by
  ext a
  exact a.property

include hp in
lemma projective : Module.Projective R (LeftCorner p) :=
  Module.Projective.of_split (LeftCorner p).subtype (projection hp) (projection_comp_inclusion hp)

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma hom_apply (f : LeftCorner p →ₗ[R] N) (a : LeftCorner p) :
    f a = (a : R) • f (generator hp) := by
  rw [← f.map_smul]
  congr 1
  apply Subtype.ext
  exact a.property.symm

def lift (n : N) (_hn : p • n = n) : LeftCorner p →ₗ[R] N where
  toFun a := (a : R) • n
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

@[simp] lemma lift_apply (n : N) (hn : p • n = n) (a : LeftCorner p) :
    lift n hn a = (a : R) • n := rfl

@[simp] lemma lift_generator (n : N) (hn : p • n = n) : lift n hn (generator hp) = n := hn

lemma generator_fixed (f : LeftCorner p →ₗ[R] N) : p • f (generator hp) = f (generator hp) := by
  rw [← f.map_smul]
  congr 1
  exact Subtype.ext hp

lemma hom_ext {f g : LeftCorner p →ₗ[R] N} (h : f (generator hp) = g (generator hp)) : f = g := by
  ext a
  calc
    f a = (a : R) • f (generator hp) := hom_apply hp f a
    _ = (a : R) • g (generator hp) := by rw [h]
    _ = g a := (hom_apply hp g a).symm

def mulRight {q : R} (b : R) (hb : b * q = b) : LeftCorner p →ₗ[R] LeftCorner q where
  toFun a := ⟨(a : R) * b, by change ((a : R) * b) * q = (a : R) * b; rw [mul_assoc, hb]⟩
  map_add' a c := Subtype.ext (add_mul _ _ _)
  map_smul' a c := Subtype.ext (mul_assoc _ _ _)

@[simp] lemma mulRight_apply {q : R} (b : R) (hb : b * q = b) (a : LeftCorner p) :
    (mulRight b hb a : R) = (a : R) * b := rfl

end LeftCorner
end Tachikawa

end


namespace Tachikawa

noncomputable section

abbrev GroundField := FractionRing (MvPolynomial (Fin 3) (ZMod 2))

noncomputable def parameter (i : Fin 3) : GroundField :=
  algebraMap (MvPolynomial (Fin 3) (ZMod 2)) GroundField (MvPolynomial.X i)

abbrev q : GroundField := parameter 0
abbrev H₁ : GroundField := parameter 1
abbrev H₂ : GroundField := parameter 2

def C (k : Type*) (_q : k) := Fin 10 → k

namespace C

variable {k : Type*} [Field k] (q : k)

instance : AddCommGroup (C k q) := inferInstanceAs (AddCommGroup (Fin 10 → k))
instance : Module k (C k q) := inferInstanceAs (Module k (Fin 10 → k))

@[simp] lemma add_apply (a b : C k q) (i : Fin 10) : (a + b) i = a i + b i := rfl
@[simp] lemma zero_apply (i : Fin 10) : (0 : C k q) i = 0 := rfl
@[simp] lemma neg_apply (a : C k q) (i : Fin 10) : (-a) i = -a i := rfl
@[simp] lemma smul_apply (a : k) (b : C k q) (i : Fin 10) : (a • b) i = a * b i := rfl

def mul (a b : C k q) : C k q := ![
  a 0 * b 0,
  a 1 * b 1,
  a 0 * b 2 + a 2 * b 0 + q * a 5 * b 7,
  a 0 * b 3 + a 3 * b 0 + a 5 * b 7,
  a 0 * b 4 + a 4 * b 0 + q * a 2 * b 3 + a 3 * b 2 +
    a 5 * b 8 + q * a 6 * b 7,
  a 0 * b 5 + a 5 * b 1,
  a 0 * b 6 + a 6 * b 1 + a 2 * b 5 + a 3 * b 5 + a 5 * b 9,
  a 1 * b 7 + a 7 * b 0,
  a 1 * b 8 + a 8 * b 0 + a 7 * b 2 + q ^ 2 * a 7 * b 3 + q * a 9 * b 7,
  a 1 * b 9 + a 9 * b 1 + (1 + q) * a 7 * b 5]

def unit : C k q := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

omit [Field k] in
@[ext] lemma ext {a b : C k q} (h : ∀ i, a i = b i) : a = b := funext h

lemma mul_assoc (a b c : C k q) : mul q (mul q a b) c = mul q a (mul q b c) := by
  ext i
  fin_cases i <;> simp [mul] <;> ring

lemma unit_mul (a : C k q) : mul q (unit q) a = a := by
  ext i
  fin_cases i <;> simp [mul, unit]

lemma mul_unit (a : C k q) : mul q a (unit q) = a := by
  ext i
  fin_cases i <;> simp [mul, unit]

lemma mul_add (a b c : C k q) : mul q a (b + c) = mul q a b + mul q a c := by
  ext i
  rw [add_apply]
  fin_cases i <;> simp [mul, add_apply] <;> ring

lemma add_mul (a b c : C k q) : mul q (a + b) c = mul q a c + mul q b c := by
  ext i
  rw [add_apply]
  fin_cases i <;> simp [mul, add_apply] <;> ring

instance : Ring (C k q) where
  __ := (inferInstance : AddCommGroup (C k q))
  mul := mul q
  one := unit q
  mul_assoc := mul_assoc q
  one_mul := unit_mul q
  mul_one := mul_unit q
  left_distrib := mul_add q
  right_distrib := add_mul q
  zero_mul a := by
    ext i
    change mul q 0 a i = 0
    fin_cases i <;> simp [mul, zero_apply]
  mul_zero a := by
    ext i
    change mul q a 0 i = 0
    fin_cases i <;> simp [mul, zero_apply]

lemma smul_mul (r : k) (a b : C k q) : (r • a) * b = r • (a * b) := by
  ext i
  change mul q (r • a) b i = (r • mul q a b) i
  rw [smul_apply]
  fin_cases i <;> simp [mul, smul_apply] <;> ring

lemma mul_smul (r : k) (a b : C k q) : a * (r • b) = r • (a * b) := by
  ext i
  change mul q a (r • b) i = (r • mul q a b) i
  rw [smul_apply]
  fin_cases i <;> simp [mul, smul_apply] <;> ring

instance : Algebra k (C k q) := Algebra.ofModule (smul_mul q) (mul_smul q)

instance : FiniteDimensional k (C k q) :=
  inferInstanceAs (FiniteDimensional k (Fin 10 → k))

end C
end
end Tachikawa



noncomputable section
namespace Tachikawa.C

variable {k : Type*} [Field k] (q : k)

def basis : Module.Basis (Fin 10) k (C k q) := Pi.basisFun k (Fin 10)

@[simp] lemma basis_apply (i j : Fin 10) : basis q i j = if j = i then 1 else 0 := by
  change (Pi.basisFun k (Fin 10) i) j = _
  simp [Pi.basisFun_apply, Pi.single_apply]

def f : C k q := ![0,1,0,0,0,0,0,0,0,0]

lemma mul_f (a : C k q) : a * f q = ![0,a 1,0,0,0,a 5,a 6,0,0,a 9] := by
  ext i
  change mul q a (f q) i = _
  fin_cases i <;> simp [mul, f]

lemma trace_left_right_f (a : C k q) :
    LinearMap.trace k (C k q) ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (f q))) =
      2 * a 0 + 2 * a 1 := by
  rw [LinearMap.trace_eq_matrix_trace k (basis q)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  change (∑ i : Fin 10, (a * ((basis q i) * f q)) i) = _
  simp only [mul_f]
  change (∑ i : Fin 10, mul q a ![0,(basis q i) 1,0,0,0,(basis q i) 5,
    (basis q i) 6,0,0,(basis q i) 9] i) = _
  simp [Fin.sum_univ_succ, mul, basis_apply]
  ring

lemma trace_left_right_f_eq_zero [CharP k 2] (a : C k q) :
    LinearMap.trace k (C k q) ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (f q))) = 0 := by
  have hc (r s : k) : 2 * r + 2 * s = 0 := by
    rw [show (2 : k) = 0 from CharP.cast_eq_zero k 2]
    simp only [zero_mul, add_zero]
  exact (trace_left_right_f q a).trans (hc (a 0) (a 1))




def e : C k q := ![1,0,0,0,0,0,0,0,0,0]
def u : C k q := ![0,0,0,0,0,1,0,0,0,0]
def ell (c : k) : C k q := ![0,0,1,c,0,0,0,0,0,0]

lemma mul_e (a : C k q) : a * e q = ![a 0,0,a 2,a 3,a 4,0,0,a 7,a 8,0] := by
  ext i
  change mul q a (e q) i = _
  fin_cases i <;> simp [mul, e]

lemma e_idempotent : e q * e q = e q := by rw [mul_e]; rfl
lemma f_idempotent : f q * f q = f q := by rw [mul_f]; rfl
lemma u_mul_f : u q * f q = u q := by rw [mul_f]; rfl
lemma ell_mul_e (c : k) : ell q c * e q = ell q c := by rw [mul_e]; rfl

abbrev Ce := LeftCorner (e q)
abbrev Cf := LeftCorner (f q)

instance : Module.Projective (C k q) (Ce q) := LeftCorner.projective (e_idempotent q)
instance : Module.Projective (C k q) (Cf q) := LeftCorner.projective (f_idempotent q)

def ce (a b c d t j : k) : Ce q := ⟨![a,0,b,c,d,0,0,t,j,0], by
  exact mul_e q ![a,0,b,c,d,0,0,t,j,0]⟩
def cf (a u v n : k) : Cf q := ⟨![0,a,0,0,0,u,v,0,0,n], by
  exact mul_f q ![0,a,0,0,0,u,v,0,0,n]⟩

lemma ce_eta (a : Ce q) : ce q (a.val 0) (a.val 2) (a.val 3) (a.val 4) (a.val 7) (a.val 8) = a := by
  apply Subtype.ext
  exact (mul_e q a.val).symm.trans a.property

lemma cf_eta (a : Cf q) : cf q (a.val 1) (a.val 5) (a.val 6) (a.val 9) = a := by
  apply Subtype.ext
  exact (mul_f q a.val).symm.trans a.property

@[simp] lemma ce_eq_zero (a b c d t j : k) : ce q a b c d t j = 0 ↔
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ t = 0 ∧ j = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 0, congrFun hv 2, congrFun hv 3, congrFun hv 4,
      congrFun hv 7, congrFun hv 8⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

@[simp] lemma cf_eq_zero (a u v n : k) : cf q a u v n = 0 ↔
    a = 0 ∧ u = 0 ∧ v = 0 ∧ n = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 1, congrFun hv 5, congrFun hv 6, congrFun hv 9⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

def rhoU : Ce q →ₗ[C k q] Cf q := LeftCorner.mulRight (u q) (u_mul_f q)
def rhoEll (c : k) : Ce q →ₗ[C k q] Ce q := LeftCorner.mulRight (ell q c) (ell_mul_e q c)

lemma rhoU_ce (a b c d t j : k) :
    rhoU q (ce q a b c d t j) = cf q 0 a (b + c) ((1 + q) * t) := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (u q) i = _
  fin_cases i <;> simp [mul, u, cf]

lemma rhoEll_ce (z a b c d t j : k) :
    rhoEll q z (ce q a b c d t j) = ce q 0 a (z * a) (q * z * b + c) 0 ((1 + q^2 * z) * t) := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (ell q z) i = _
  fin_cases i <;> simp [mul, ell, ce] <;> ring

end Tachikawa.C

namespace Tachikawa.C
variable {k : Type*} [Field k] [CharP k 2] (q : k)

lemma rhoEll_comp_zero (z : k) (y : Ce q) :
    rhoEll q z (rhoEll q (q*z) y) = 0 := by
  rw [← ce_eta q y, rhoEll_ce, rhoEll_ce]
  simp only [mul_zero, CharTwo.add_self_eq_zero, ce_eq_zero, and_self]

lemma rhoU_comp_zero (y : Ce q) : rhoU q (rhoEll q 1 y) = 0 := by
  rw [← ce_eta q y, rhoEll_ce, rhoU_ce]
  simp only [one_mul, CharTwo.add_self_eq_zero, mul_zero, cf_eq_zero, and_self]

lemma exact_rhoEll (z : k) (hz : 1 + q^2 * z ≠ 0) (hz' : 1 + q^2 * (q*z) ≠ 0) :
    Function.Exact (rhoEll q (q*z)) (rhoEll q z) := by
  intro x
  constructor
  · intro h
    rw [← ce_eta q x, rhoEll_ce, ce_eq_zero] at h
    obtain ⟨_, ha, _, hb, _, ht⟩ := h
    have ht' : x.val 7 = 0 := (mul_eq_zero.mp ht).resolve_left hz
    have hc : x.val 3 = q*z*x.val 2 := by
      have := eq_neg_of_add_eq_zero_left hb
      simpa only [CharTwo.neg_eq] using this.symm
    refine ⟨ce q (x.val 2) 0 (x.val 4) 0 (x.val 8 / (1 + q^2 * (q*z))) 0, ?_⟩
    rw [rhoEll_ce]
    have hx := ce_eta q x
    rw [ha, ht', hc] at hx
    simpa only [mul_zero, zero_add, mul_div_cancel₀ _ hz'] using hx
  · rintro ⟨y, rfl⟩
    exact rhoEll_comp_zero q z y

lemma exact_rhoU (hq : 1 + q ≠ 0) (hq2 : 1 + q^2 ≠ 0) :
    Function.Exact (rhoEll q 1) (rhoU q) := by
  intro x
  constructor
  · intro h
    rw [← ce_eta q x, rhoU_ce, cf_eq_zero] at h
    obtain ⟨_, ha, hbc, ht⟩ := h
    have ht' : x.val 7 = 0 := (mul_eq_zero.mp ht).resolve_left hq
    have hc : x.val 3 = x.val 2 := by
      have := eq_neg_of_add_eq_zero_left hbc
      simpa only [CharTwo.neg_eq] using this.symm
    refine ⟨ce q (x.val 2) 0 (x.val 4) 0 (x.val 8 / (1 + q^2)) 0, ?_⟩
    rw [rhoEll_ce]
    have hx := ce_eta q x
    rw [ha, ht', hc] at hx
    simpa only [mul_zero, zero_add, mul_one, one_mul, mul_div_cancel₀ _ hq2] using hx
  · rintro ⟨y, rfl⟩
    exact rhoU_comp_zero q y

end Tachikawa.C



namespace Tachikawa

def RightCorner {R : Type*} [Ring R] (p : R) : Submodule Rᵐᵒᵖ R where
  carrier := {a | p * a = a}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; change p*(a+b)=a+b; rw [mul_add, ha, hb]
  smul_mem' := by intro a b hb; change p*(b*a.unop)=b*a.unop; rw [← mul_assoc, hb]

@[simp] lemma mem_rightCorner {R : Type*} [Ring R] (p a : R) :
    a ∈ RightCorner p ↔ p*a=a := Iff.rfl

namespace RightCorner
variable {R : Type*} [Ring R] {p : R} (hp : p*p=p)

def generator : RightCorner p := ⟨p,hp⟩
def projection : R →ₗ[Rᵐᵒᵖ] RightCorner p where
  toFun a := ⟨p*a, by change p*(p*a)=p*a; rw [← mul_assoc, hp]⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' a b := Subtype.ext (mul_assoc _ _ _).symm

lemma projection_comp_inclusion : (projection hp).comp (RightCorner p).subtype = LinearMap.id := by
  ext a
  exact a.property

include hp in
lemma projective : Module.Projective Rᵐᵒᵖ (RightCorner p) := by
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv
    (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_split (RightCorner p).subtype (projection hp) (projection_comp_inclusion hp)

def homEquiv : (LeftCorner p →ₗ[R] R) ≃ₗ[Rᵐᵒᵖ] RightCorner p where
  toFun f := ⟨f (LeftCorner.generator hp), LeftCorner.generator_fixed hp f⟩
  invFun a := LeftCorner.lift a.val a.property
  left_inv _f := LeftCorner.hom_ext hp (LeftCorner.lift_generator hp _ _)
  right_inv _a := Subtype.ext (LeftCorner.lift_generator hp _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma homEquiv_apply (f : LeftCorner p →ₗ[R] R) :
    (homEquiv hp f : R) = f (LeftCorner.generator hp) := rfl

def mulLeft {q : R} (b : R) (hb : q*b=b) : RightCorner p →ₗ[Rᵐᵒᵖ] RightCorner q where
  toFun a := ⟨b*(a:R), by change q*(b*(a:R))=b*(a:R); rw [← mul_assoc, hb]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _).symm

@[simp] lemma mulLeft_apply {q : R} (b : R) (hb : q*b=b) (a : RightCorner p) :
    (mulLeft b hb a : R) = b*(a:R) := rfl

lemma homEquiv_precomp {q : R} (hq : q*q=q) (b : R) (hpb : p*b=b) (hbq : b*q=b)
    (f : LeftCorner q →ₗ[R] R) :
    homEquiv hp (f.comp (LeftCorner.mulRight b hbq)) = mulLeft b hpb (homEquiv hq f) := by
  apply Subtype.ext
  change f ⟨p*b, _⟩ = b * f (LeftCorner.generator hq)
  rw [LeftCorner.hom_apply hq]
  change (p*b) * f (LeftCorner.generator hq) = _
  rw [hpb]

end RightCorner
end Tachikawa



namespace Tachikawa.RightCorner
variable {R : Type*} [Ring R] {p : R}
variable {N : Type*} [AddCommGroup N] [Module Rᵐᵒᵖ N]

def lift (n : N) (_hn : MulOpposite.op p • n = n) : RightCorner p →ₗ[Rᵐᵒᵖ] N where
  toFun a := MulOpposite.op a.val • n
  map_add' a b := by
    change MulOpposite.op (a.val + b.val) • n = MulOpposite.op a.val • n + MulOpposite.op b.val • n
    rw [MulOpposite.op_add, add_smul]
  map_smul' a b := by
    change MulOpposite.op (b.val * a.unop) • n = a • MulOpposite.op b.val • n
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

end Tachikawa.RightCorner

namespace Tachikawa.C
variable {k : Type} [Field k] (q : k)

lemma e_mul (a : C k q) : e q * a = ![a 0,0,a 2,a 3,a 4,a 5,a 6,0,0,0] := by
  ext i
  change mul q (e q) a i = _
  fin_cases i <;> simp [mul, e]

lemma f_mul (a : C k q) : f q * a = ![0,a 1,0,0,0,0,0,a 7,a 8,a 9] := by
  ext i
  change mul q (f q) a i = _
  fin_cases i <;> simp [mul, f]

lemma e_mul_u : e q * u q = u q := by rw [e_mul]; rfl
lemma e_mul_ell (c : k) : e q * ell q c = ell q c := by rw [e_mul]; rfl

abbrev eC := RightCorner (e q)
abbrev fC := RightCorner (f q)

instance : Module.Projective (C k q)ᵐᵒᵖ (eC q) := RightCorner.projective (e_idempotent q)
instance : Module.Projective (C k q)ᵐᵒᵖ (fC q) := RightCorner.projective (f_idempotent q)

def ec (a b c d u v : k) : eC q := ⟨![a,0,b,c,d,u,v,0,0,0], by
  exact e_mul q ![a,0,b,c,d,u,v,0,0,0]⟩
def fc (a t j n : k) : fC q := ⟨![0,a,0,0,0,0,0,t,j,n], by
  exact f_mul q ![0,a,0,0,0,0,0,t,j,n]⟩

lemma ec_eta (a : eC q) : ec q (a.val 0) (a.val 2) (a.val 3) (a.val 4) (a.val 5) (a.val 6) = a := by
  apply Subtype.ext
  exact (e_mul q a.val).symm.trans a.property

lemma fc_eta (a : fC q) : fc q (a.val 1) (a.val 7) (a.val 8) (a.val 9) = a := by
  apply Subtype.ext
  exact (f_mul q a.val).symm.trans a.property

@[simp] lemma ec_eq_zero (a b c d u v : k) : ec q a b c d u v = 0 ↔
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 0, congrFun hv 2, congrFun hv 3, congrFun hv 4,
      congrFun hv 5, congrFun hv 6⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

@[simp] lemma fc_eq_zero (a t j n : k) : fc q a t j n = 0 ↔
    a = 0 ∧ t = 0 ∧ j = 0 ∧ n = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 1, congrFun hv 7, congrFun hv 8, congrFun hv 9⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

def lambdaU : fC q →ₗ[(C k q)ᵐᵒᵖ] eC q := RightCorner.mulLeft (u q) (e_mul_u q)
def lambdaEll (c : k) : eC q →ₗ[(C k q)ᵐᵒᵖ] eC q :=
  RightCorner.mulLeft (ell q c) (e_mul_ell q c)

lemma lambdaU_fc (a t j n : k) :
    lambdaU q (fc q a t j n) = ec q 0 (q*t) t j a n := by
  apply Subtype.ext
  ext i
  change mul q (u q) ![0,a,0,0,0,0,0,t,j,n] i = _
  fin_cases i <;> simp [mul, u, ec]

lemma lambdaEll_ec (z a b c d u v : k) :
    lambdaEll q z (ec q a b c d u v) = ec q 0 a (z*a) (z*b+q*c) 0 ((1+z)*u) := by
  apply Subtype.ext
  ext i
  change mul q (ell q z) ![a,0,b,c,d,u,v,0,0,0] i = _
  fin_cases i <;> simp [mul, ell, ec] <;> ring

lemma lambdaU_injective : Function.Injective (lambdaU q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  rw [← fc_eta q x, lambdaU_fc, ec_eq_zero] at hx
  obtain ⟨_, _, ht, hj, ha, hn⟩ := hx
  rw [← fc_eta q x, fc_eq_zero]
  exact ⟨ha, ht, hj, hn⟩

variable [CharP k 2]

lemma exact_lambdaU : Function.Exact (lambdaU q) (lambdaEll q 1) := by
  intro x
  constructor
  · intro hh
    rw [← ec_eta q x, lambdaEll_ec, ec_eq_zero] at hh
    obtain ⟨_, ha, _, hbc, _, _⟩ := hh
    have hb : x.val 2 = q*x.val 3 := by
      have he := eq_neg_of_add_eq_zero_left hbc
      simpa only [one_mul, CharTwo.neg_eq] using he
    refine ⟨fc q (x.val 5) (x.val 3) (x.val 4) (x.val 6), ?_⟩
    rw [lambdaU_fc]
    have hx := ec_eta q x
    rw [ha, hb] at hx
    exact hx
  · rintro ⟨z, rfl⟩
    rw [← fc_eta q z, lambdaU_fc, lambdaEll_ec, ec_eq_zero]
    simp only [mul_zero, one_mul, CharTwo.add_self_eq_zero, zero_mul, and_self]

lemma exact_lambdaEll (hq : q ≠ 0) (z : k) (hz : 1+z ≠ 0) (hz' : 1+q*z ≠ 0) :
    Function.Exact (lambdaEll q z) (lambdaEll q (q*z)) := by
  intro x
  constructor
  · intro hh
    rw [← ec_eta q x, lambdaEll_ec, ec_eq_zero] at hh
    obtain ⟨_, ha, _, hbc, _, hu⟩ := hh
    have hu' : x.val 5 = 0 := (mul_eq_zero.mp hu).resolve_left hz'
    have hc : x.val 3 = z*x.val 2 := by
      have he : q * (z*x.val 2 + x.val 3) = 0 := by
        simpa only [_root_.mul_assoc, _root_.mul_add] using hbc
      have he' := (mul_eq_zero.mp he).resolve_left hq
      simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right he')
    refine ⟨ec q (x.val 2) 0 (x.val 4/q) 0 (x.val 6/(1+z)) 0, ?_⟩
    rw [lambdaEll_ec]
    have hx := ec_eta q x
    rw [ha, hu', hc] at hx
    simpa only [mul_zero, zero_add, mul_div_cancel₀ _ hq, mul_div_cancel₀ _ hz] using hx
  · rintro ⟨y, rfl⟩
    rw [← ec_eta q y, lambdaEll_ec, lambdaEll_ec, ec_eq_zero]
    simp only [mul_zero, and_true, true_and]
    rw [_root_.mul_assoc, CharTwo.add_self_eq_zero]

end Tachikawa.C



namespace Tachikawa
open scoped TensorProduct

variable {k : Type*} [Field k] (q : k)

abbrev B := (C k q) ⊗[k] (C k q)

def pf : B q := C.f q ⊗ₜ[k] C.f q

lemma trace_left_right_pf [CharP k 2] (a : B q) :
    LinearMap.trace k (B q) ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (pf q))) = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    have he : (LinearMap.mulLeft k (a ⊗ₜ[k] b)).comp (LinearMap.mulRight k (pf q)) =
        TensorProduct.map
          ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (C.f q)))
          ((LinearMap.mulLeft k b).comp (LinearMap.mulRight k (C.f q))) := by
      ext x y
      simp [pf, Algebra.TensorProduct.tmul_mul_tmul]
    rw [he, LinearMap.trace_tensorProduct']
    rw [C.trace_left_right_f_eq_zero]
    simp
  | add a b ha hb =>
    have he : (LinearMap.mulLeft k (a + b)).comp (LinearMap.mulRight k (pf q)) =
        (LinearMap.mulLeft k a).comp (LinearMap.mulRight k (pf q)) +
        (LinearMap.mulLeft k b).comp (LinearMap.mulRight k (pf q)) := by
      ext x
      simp [add_mul]
    rw [he, map_add, ha, hb, add_zero]

end Tachikawa



namespace Tachikawa

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R]

omit [FiniteDimensional k R] in
lemma end_expansion {ι : Type*} [Fintype ι] (e : Module.Basis ι k R)
    (F : R →ₗ[k] R) :
    F = ∑ i, (e.coord i).smulRight (F (e i)) := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have h := congrArg F (e.sum_repr x)
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using h.symm

lemma outer_to_dual_formula
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (F : R →ₗ[k] R),
      β (F.comp (LinearMap.mulRight k a)) = (β F).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (F : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp F) = (β F).comp (LinearMap.mulLeft k a)) :
    ∃ b : R, ∀ (φ : Module.Dual k R) (c p : R),
      β (φ.smulRight c) p = φ (b * c * p) := by
  let t : Module.Dual k R →ₗ[k] (R →ₗ[k] R) := LinearMap.smulRightₗ.flip 1
  let η : Module.Dual k R →ₗ[k] Module.Dual k R := β.comp t
  let b : R := (Module.evalEquiv k R).symm ((LinearMap.applyₗ (1 : R)).comp η)
  have hb (φ : Module.Dual k R) : φ b = β (φ.smulRight 1) 1 := by
    exact Module.apply_evalEquiv_symm_apply k R φ _
  have ht (φ : Module.Dual k R) (p : R) : β (φ.smulRight 1) p = φ (b * p) := by
    have h := congrArg (fun g : Module.Dual k R => g 1) (hleft p (φ.smulRight 1))
    have he : (φ.smulRight (1 : R)).comp (LinearMap.mulRight k p) =
        (φ.comp (LinearMap.mulRight k p)).smulRight 1 := by
      ext x
      rfl
    rw [he] at h
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul] at h
    rw [← hb] at h
    exact h.symm
  refine ⟨b, ?_⟩
  intro φ c p
  have he : (LinearMap.mulRight k c).comp (φ.smulRight (1 : R)) = φ.smulRight c := by
    ext x
    simp
  have h := congrArg (fun g : Module.Dual k R => g p) (hright c (φ.smulRight 1))
  rw [he] at h
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
  rw [h, ht, mul_assoc]

omit [FiniteDimensional k R] in

lemma outer_central_is_mulLeft (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k a) = (LinearMap.mulRight k a).comp F) :
    F = LinearMap.mulLeft k (F 1) := by
  ext x
  have h := congrArg (fun g : R →ₗ[k] R => g 1) (hF x)
  simpa using h

lemma outer_factorization_trace
    (F : R →ₗ[k] R)
    (hF : ∀ a : R, F.comp (LinearMap.mulRight k a) = (LinearMap.mulRight k a).comp F)
    (β : (R →ₗ[k] R) →ₗ[k] Module.Dual k R)
    (hleft : ∀ (a : R) (G : R →ₗ[k] R),
      β (G.comp (LinearMap.mulRight k a)) = (β G).comp (LinearMap.mulRight k a))
    (hright : ∀ (a : R) (G : R →ₗ[k] R),
      β ((LinearMap.mulRight k a).comp G) = (β G).comp (LinearMap.mulLeft k a)) :
    ∃ d : R, ∀ p : R, β F p =
      LinearMap.trace k R ((LinearMap.mulLeft k d).comp (LinearMap.mulRight k p)) := by
  classical
  obtain ⟨b, hb⟩ := outer_to_dual_formula β hleft hright
  refine ⟨b * F 1, ?_⟩
  intro p
  let e := Module.finBasis k R
  conv_lhs => rw [end_expansion e F]
  simp only [map_sum, LinearMap.sum_apply, hb]
  rw [LinearMap.trace_eq_matrix_trace k e]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  have hFi : F (e i) = F 1 * e i := by
    rw [outer_central_is_mulLeft F hF]
    simp
  simp only [Module.Basis.coord_apply, hFi, mul_assoc]

end Tachikawa



namespace Tachikawa
open scoped TensorProduct
variable {k : Type*} [Field k] (q : k)

namespace C

def character : C k q →ₐ[k] k where
  toFun a := a 1
  map_one' := rfl
  map_mul' a b := rfl
  map_zero' := rfl
  map_add' a b := rfl
  commutes' r := by
    change (r • C.unit q) 1 = r
    rw [C.smul_apply]
    simp [C.unit]

@[simp] lemma character_f : character q (f q) = 1 := rfl
end C

def characterB : B q →ₐ[k] k := Algebra.TensorProduct.productMap (C.character q) (C.character q)

@[simp] lemma characterB_pf : characterB q (pf q) = 1 := by
  simp [characterB, pf, Algebra.TensorProduct.productMap]

def characterMapB : B q →ₗ[k] Module.Dual k (B q) :=
  (characterB q).toLinearMap.smulRight (characterB q).toLinearMap

lemma characterMapB_left (a b : B q) : characterMapB q (a * b) =
    (characterMapB q b).comp (LinearMap.mulRight k a) := by
  ext c
  simp [characterMapB, mul_comm, mul_left_comm]

lemma characterMapB_right (a b : B q) : characterMapB q (a * b) =
    (characterMapB q a).comp (LinearMap.mulLeft k b) := by
  ext c
  simp [characterMapB, mul_assoc]

lemma characterMapB_one_pf : characterMapB q 1 (pf q) = 1 := by
  simp [characterMapB]

variable [CharP k 2]

lemma ordinary_factorization_pf_zero
    (α : B q →ₗ[k] (B q →ₗ[k] B q))
    (hαleft : ∀ a b : B q, α (a * b) = (α b).comp (LinearMap.mulRight k a))
    (hαright : ∀ a b : B q, α (a * b) = (LinearMap.mulRight k b).comp (α a))
    (β : (B q →ₗ[k] B q) →ₗ[k] Module.Dual k (B q))
    (hβleft : ∀ (a : B q) (F : B q →ₗ[k] B q),
      β (F.comp (LinearMap.mulRight k a)) = (β F).comp (LinearMap.mulRight k a))
    (hβright : ∀ (a : B q) (F : B q →ₗ[k] B q),
      β ((LinearMap.mulRight k a).comp F) = (β F).comp (LinearMap.mulLeft k a)) :
    β (α 1) (pf q) = 0 := by
  have hα : ∀ a : B q, (α 1).comp (LinearMap.mulRight k a) =
      (LinearMap.mulRight k a).comp (α 1) := by
    intro a
    rw [← hαleft, ← hαright, mul_one, one_mul]
  obtain ⟨d, hd⟩ := outer_factorization_trace (α 1) hα β hβleft hβright
  rw [hd, trace_left_right_pf]

lemma characterMapB_not_finite_sum
    {ι : Type*} [Fintype ι]
    (α : ι → B q →ₗ[k] (B q →ₗ[k] B q))
    (hαleft : ∀ i a b, α i (a * b) = (α i b).comp (LinearMap.mulRight k a))
    (hαright : ∀ i a b, α i (a * b) = (LinearMap.mulRight k b).comp (α i a))
    (β : ι → (B q →ₗ[k] B q) →ₗ[k] Module.Dual k (B q))
    (hβleft : ∀ i a F,
      β i (F.comp (LinearMap.mulRight k a)) = (β i F).comp (LinearMap.mulRight k a))
    (hβright : ∀ i a F,
      β i ((LinearMap.mulRight k a).comp F) = (β i F).comp (LinearMap.mulLeft k a)) :
    (∑ i, (β i).comp (α i)) ≠ characterMapB q := by
  classical
  intro h
  have he := congrArg (fun f : B q →ₗ[k] Module.Dual k (B q) => f 1 (pf q)) h
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, characterMapB_one_pf] at he
  have hz : (∑ i, β i (α i 1) (pf q)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact ordinary_factorization_pf_zero q (α i) (hαleft i) (hαright i)
      (β i) (hβleft i) (hβright i)
  exact zero_ne_one (hz.symm.trans he)

end Tachikawa



namespace Tachikawa.C
variable {k : Type*} [Field k] (q : k)

def Simple (_q : k) := k
instance : AddCommGroup (Simple q) := inferInstanceAs (AddCommGroup k)
instance : Module k (Simple q) := inferInstanceAs (Module k k)
instance : Module (C k q) (Simple q) := Module.compHom (Simple q) (character q).toRingHom
instance : IsScalarTower k (C k q) (Simple q) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change (character q (algebraMap k (C k q) r)) • x = r • x
    rw [AlgHom.commutes]
    rfl
instance : FiniteDimensional k (Simple q) := inferInstanceAs (FiniteDimensional k k)

@[simp] lemma simple_smul (a : C k q) (x : Simple q) : a • x = (a 1 : k) • x := rfl

@[simp] lemma e_smul_simple (x : Simple q) : e q • x = 0 := by
  change (0 : k) • x = 0
  exact zero_smul k x

@[simp] lemma f_smul_simple (x : Simple q) : f q • x = x := by
  change (1 : k) • x = x
  exact one_smul k x

def augmentation : Cf q →ₗ[C k q] Simple q where
  toFun a := a.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma augmentation_cf (a u v n : k) : augmentation q (cf q a u v n) = a := rfl

lemma augmentation_surjective : Function.Surjective (augmentation q) :=
  fun x => ⟨cf q x 0 0 0, rfl⟩

lemma augmentation_rhoU : (augmentation q).comp (rhoU q) = 0 := by
  ext x
  rw [LinearMap.comp_apply, ← ce_eta q x, rhoU_ce]
  rfl

lemma exact_augmentation (hq : 1+q ≠ 0) : Function.Exact (rhoU q) (augmentation q) := by
  intro x
  constructor
  · intro h
    refine ⟨ce q (x.val 5) (x.val 6) 0 0 (x.val 9 / (1+q)) 0, ?_⟩
    rw [rhoU_ce]
    have hx := cf_eta q x
    change x.val 1 = 0 at h
    rw [h] at hx
    simpa only [add_zero, mul_div_cancel₀ _ hq] using hx
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (augmentation_rhoU q) y

lemma homCeSimple_zero (F : Ce q →ₗ[C k q] Simple q) : F = 0 := by
  apply LeftCorner.hom_ext (e_idempotent q)
  have h := LeftCorner.generator_fixed (e_idempotent q) F
  rw [e_smul_simple] at h
  exact h.symm

instance : Subsingleton (Ce q →ₗ[C k q] Simple q) :=
  ⟨fun F G => (homCeSimple_zero q F).trans (homCeSimple_zero q G).symm⟩

end Tachikawa.C



namespace Tachikawa
lemma parameter_ne_zero (i : Fin 3) : parameter i ≠ 0 := by
  intro h
  apply (MvPolynomial.X_ne_zero i : (MvPolynomial.X i : MvPolynomial (Fin 3) (ZMod 2)) ≠ 0)
  apply IsFractionRing.injective (MvPolynomial (Fin 3) (ZMod 2)) GroundField
  rw [map_zero]; exact h

lemma parameter_pow_ne_one (i : Fin 3) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ 1 := by
  intro h
  have h' : (MvPolynomial.X i : MvPolynomial (Fin 3) (ZMod 2)) ^ n = 1 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 3) (ZMod 2)) GroundField
    simpa [parameter] using h
  rw [MvPolynomial.X_pow_eq_monomial] at h'
  have he := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i n)) h'
  simp [MvPolynomial.coeff_one, hn.ne', eq_comm] at he

lemma parameter_pow_ne (i j : Fin 3) (hij : i ≠ j) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ parameter j ^ n := by
  intro h
  have h' : (MvPolynomial.X i : MvPolynomial (Fin 3) (ZMod 2)) ^ n =
      MvPolynomial.X j ^ n := by
    apply IsFractionRing.injective (MvPolynomial (Fin 3) (ZMod 2)) GroundField
    simpa [parameter] using h
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial] at h'
  have hmon := (MvPolynomial.monomial_left_inj (by decide : (1 : ZMod 2) ≠ 0)).mp h'
  have hval := congrFun (congrArg DFunLike.coe hmon) i
  simp [hij, hn.ne'] at hval

lemma one_add_parameter_pow_ne_zero (i : Fin 3) (n : ℕ) (hn : 0 < n) :
    1 + parameter i ^ n ≠ 0 := by
  intro h
  have hp : parameter i ^ n = 1 := by
    have := eq_neg_of_add_eq_zero_left h
    simpa only [CharTwo.neg_eq] using this.symm
  exact parameter_pow_ne_one i n hn hp

end Tachikawa



namespace Tachikawa.C
open CategoryTheory
variable {k : Type*} [Field k] [CharP k 2] (q : k)

def resObj : ℕ → ModuleCat (C k q)
  | 0 => ModuleCat.of (C k q) (Cf q)
  | _+1 => ModuleCat.of (C k q) (Ce q)

def resD : ∀ n, resObj q (n+1) ⟶ resObj q n
  | 0 => ModuleCat.ofHom (rhoU q)
  | n+1 => ModuleCat.ofHom (rhoEll q (q^n))

lemma resD_exact (hq : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Function.Exact (resD q (n+1)) (resD q n) := by
  cases n with
  | zero =>
    change Function.Exact (rhoEll q (q^0)) (rhoU q)
    simpa only [pow_zero] using exact_rhoU q (by simpa only [pow_one] using hq 1 (by omega))
      (hq 2 (by omega))
  | succ n =>
    change Function.Exact (rhoEll q (q^(n+1))) (rhoEll q (q^n))
    rw [pow_succ']
    apply exact_rhoEll
    · rw [← pow_add]
      exact hq (2+n) (by omega)
    · rw [← pow_succ', ← pow_add]
      exact hq (2+(n+1)) (by omega)

def projectiveResolution (hq : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution (ModuleCat.of (C k q) (Simple q)) :=
  resolutionOfExact _ (resObj q) (resD q) (ModuleCat.ofHom (augmentation q))
    (resD_exact q hq) (exact_augmentation q (by simpa only [pow_one] using hq 1 (by omega)))
    (augmentation_surjective q) (fun n => by cases n <;> dsimp [resObj] <;> infer_instance)

lemma simple_positive_ext (hq : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : 0 < n) :
    Subsingleton (Abelian.Ext (ModuleCat.of (C k q) (Simple q))
      (ModuleCat.of (C k q) (Simple q)) n) := by
  let P := projectiveResolution q hq
  have hzero (α : Abelian.Ext (ModuleCat.of (C k q) (Simple q))
      (ModuleCat.of (C k q) (Simple q)) n) : α = 0 := by
    obtain ⟨F, hF, rfl⟩ := P.extMk_surjective α (n+1) rfl
    have hmap : F = 0 := by
      cases n with
      | zero => omega
      | succ n =>
        apply ModuleCat.hom_ext
        exact homCeSimple_zero q F.hom
    subst F
    exact P.extMk_zero _ _
  exact ⟨fun α β => (hzero α).trans (hzero β).symm⟩

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def RightSimple (_q : k) := k
instance : AddCommGroup (RightSimple q) := inferInstanceAs (AddCommGroup k)
instance : Module k (RightSimple q) := inferInstanceAs (Module k k)
def rightCharacter : (C k q)ᵐᵒᵖ →+* k where
  toFun a := character q a.unop
  map_zero' := map_zero (character q)
  map_one' := map_one (character q)
  map_add' a b := map_add (character q) a.unop b.unop
  map_mul' a b := by
    change character q (b.unop * a.unop) = character q a.unop * character q b.unop
    rw [map_mul, mul_comm]
instance : Module (C k q)ᵐᵒᵖ (RightSimple q) :=
  Module.compHom (RightSimple q) (rightCharacter q)

omit [CharP k 2] in
@[simp] lemma rightSimple_smul (a : (C k q)ᵐᵒᵖ) (x : RightSimple q) :
    a • x = (a.unop 1 : k) • x := rfl

lemma dualTwoCycle_coords (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (a : LinearMap.ker (lambdaEll q q)) :
    a.val.val 0 = 0 ∧ a.val.val 3 = a.val.val 2 ∧ a.val.val 5 = 0 := by
  have h : lambdaEll q q a.val = 0 := a.property
  rw [← ec_eta q a.val, lambdaEll_ec, ec_eq_zero] at h
  obtain ⟨_, h0, _, h23, _, h5⟩ := h
  refine ⟨h0, ?_, (mul_eq_zero.mp h5).resolve_left hq1⟩
  have h23' : a.val.val 2 + a.val.val 3 = 0 := by
    apply (mul_eq_zero.mp _).resolve_left hq
    simpa only [_root_.mul_add] using h23
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h23'

def dualTwoAug (hq : q ≠ 0) (hq1 : 1+q ≠ 0) :
    LinearMap.ker (lambdaEll q q) →ₗ[(C k q)ᵐᵒᵖ] RightSimple q where
  toFun a := a.val.val 6
  map_add' _ _ := rfl
  map_smul' a x := by
    obtain ⟨h0,h3,h5⟩ := dualTwoCycle_coords q hq hq1 x
    change (x.val.val * a.unop) 6 = a.unop 1 * x.val.val 6
    change x.val.val 0 * a.unop 6 + x.val.val 6 * a.unop 1 +
      x.val.val 2 * a.unop 5 + x.val.val 3 * a.unop 5 +
      x.val.val 5 * a.unop 9 = _
    rw [h0,h3,h5]
    simp only [zero_mul, zero_add, add_zero]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, mul_comm]

def dualTwoBoundary : eC q →ₗ[(C k q)ᵐᵒᵖ] LinearMap.ker (lambdaEll q q) :=
  (lambdaEll q 1).codRestrict _ (fun x => by
    change lambdaEll q q (lambdaEll q 1 x) = 0
    rw [← ec_eta q x, lambdaEll_ec, lambdaEll_ec, ec_eq_zero]
    simp [CharTwo.add_self_eq_zero])

lemma dualTwoAug_surjective (hq : q ≠ 0) (hq1 : 1+q ≠ 0) :
    Function.Surjective (dualTwoAug q hq hq1) := by
  intro x
  change ∃ y, dualTwoAug q hq hq1 y = x
  refine ⟨⟨ec q 0 0 0 0 0 (show k from x), ?_⟩, rfl⟩
  change lambdaEll q q _ = 0
  rw [lambdaEll_ec, ec_eq_zero]
  simp

lemma exact_dualTwoAug (hq : q ≠ 0) (hq1 : 1+q ≠ 0) :
    Function.Exact (dualTwoBoundary q) (dualTwoAug q hq hq1) := by
  intro x
  constructor
  · intro hx
    obtain ⟨h0,h3,h5⟩ := dualTwoCycle_coords q hq hq1 x
    change x.val.val 6 = 0 at hx
    refine ⟨ec q (x.val.val 2) (x.val.val 4) 0 0 0 0, ?_⟩
    apply Subtype.ext
    change lambdaEll q 1 _ = x.val
    rw [lambdaEll_ec]
    have he := ec_eta q x.val
    rw [h0,h3,h5,hx] at he
    simpa only [one_mul, mul_zero, add_zero] using he
  · rintro ⟨y, hy⟩
    rw [← hy]
    change (lambdaEll q 1 y).val 6 = 0
    rw [← ec_eta q y, lambdaEll_ec]
    change (1+1)*y.val 5 = 0
    rw [CharTwo.add_self_eq_zero, zero_mul]

local instance : HasQuotient (LinearMap.ker (lambdaEll q q))
    (Submodule (C k q)ᵐᵒᵖ (LinearMap.ker (lambdaEll q q))) :=
  @Submodule.hasQuotient (C k q)ᵐᵒᵖ (LinearMap.ker (lambdaEll q q))
    inferInstance inferInstance inferInstance

def dualTwoCohomologyEquiv (hq : q ≠ 0) (hq1 : 1+q ≠ 0) :
    ((LinearMap.ker (lambdaEll q q) : Type) ⧸ LinearMap.range (dualTwoBoundary q)) ≃ₗ[(C k q)ᵐᵒᵖ]
      RightSimple q := by
  have h : LinearMap.range (dualTwoBoundary q) = LinearMap.ker (dualTwoAug q hq hq1) := by
    ext x
    exact (exact_dualTwoAug q hq hq1 x).symm
  exact (Submodule.quotEquivOfEq _ _ h).trans
    ((dualTwoAug q hq hq1).quotKerEquivOfSurjective (dualTwoAug_surjective q hq hq1))

lemma dualComplex_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Function.Exact (lambdaEll q (q^(n+1))) (lambdaEll q (q^(n+2))) := by
  have he : q^(n+2) = q*q^(n+1) := pow_succ' q (n+1)
  rw [he]
  exact exact_lambdaEll q hq (q^(n+1)) (hp _ (by omega)) (by
    rw [← pow_succ']
    exact hp _ (by omega))

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma hom_rhoU_injective : Function.Injective (homPrecomp (k := k) (Z := C k q) (rhoU q)) := by
  intro f g h
  apply (RightCorner.homEquiv (f_idempotent q)).injective
  apply lambdaU_injective q
  have hh := congrArg (RightCorner.homEquiv (e_idempotent q)) h
  simpa only [homPrecomp_apply, rhoU, lambdaU,
    RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q) (u q) (e_mul_u q) (u_mul_f q)] using hh

lemma hom_exact_rhoU : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoU q))
    (homPrecomp (k := k) (Z := C k q) (rhoEll q 1)) := by
  intro f
  constructor
  · intro hf
    have hz : lambdaEll q 1 (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      have h := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
      simpa only [homPrecomp_apply, rhoEll, lambdaEll,
        RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q 1) (e_mul_ell q 1) (ell_mul_e q 1), map_zero] using h
    obtain ⟨a,ha⟩ := (exact_lambdaU q _).mp hz
    refine ⟨(RightCorner.homEquiv (f_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q) (((RightCorner.homEquiv (f_idempotent q)).symm a).comp (rhoU q)) = _
    rw [rhoU, RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q) (u q) (e_mul_u q) (u_mul_f q)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaU, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoU q (rhoEll q 1 x)) = 0
    rw [rhoU_comp_zero, map_zero]

lemma hom_exact_rhoEll (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+1))))
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+2)))) := by
  intro f
  constructor
  · intro hf
    have hz : lambdaEll q (q^(n+2)) (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      have h := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
      simpa only [homPrecomp_apply, rhoEll, lambdaEll,
        RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q (q^(n+2)))
          (e_mul_ell q _) (ell_mul_e q _), map_zero] using h
    obtain ⟨a,ha⟩ := (dualComplex_exact q hq hp n _).mp hz
    refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q) (((RightCorner.homEquiv (e_idempotent q)).symm a).comp (rhoEll q (q^(n+1)))) = _
    rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q (q^(n+1)))
      (e_mul_ell q _) (ell_mul_e q _)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaU, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoEll q (q^(n+1)) (rhoEll q (q^(n+2)) x)) = 0
    rw [pow_succ' q (n+1), rhoEll_comp_zero, map_zero]

omit [CharP k 2] in
lemma nu_rhoU_surjective : Function.Surjective (Nakayama.map (k := k) (rhoU q)) :=
  LinearMap.dualMap_surjective_of_injective (hom_rhoU_injective q)

lemma nu_resD_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n ≠ 1) :
    Function.Exact (Nakayama.map (k := k) (resD q (n+1)).hom) (Nakayama.map (resD q n).hom) := by
  cases n with
  | zero =>
    change Function.Exact (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^0))).dualMap
      (homPrecomp (k := k) (Z := C k q) (rhoU q)).dualMap
    rw [pow_zero]
    exact exact_dual _ _ (hom_exact_rhoU q)
  | succ n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      change Function.Exact (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+2)))).dualMap
        (homPrecomp (k := k) (Z := C k q) (rhoEll q (q^(n+1)))).dualMap
      exact exact_dual _ _ (hom_exact_rhoEll q hq hp n)

end Tachikawa.C

end

end OAI
