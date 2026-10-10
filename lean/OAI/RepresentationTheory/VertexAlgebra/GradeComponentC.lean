import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.VacuumMemNegative

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
section Algebraic
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
namespace CFTTypeVOA
variable (A : CFTTypeVOA V)
theorem gradeComponent_c2_mem (d : ℕ) {a : V} (ha : a ∈ A.toVertexAlgebra.c2) :
    A.gradeComponent d a ∈ A.homogeneousC2 d := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    exact A.gradeComponent_c2Product_mem d a b
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add] using (A.homogeneousC2 d).add_mem hx hy
  | smul z x _ hx =>
    simpa only [map_smul] using (A.homogeneousC2 d).smul_mem z hx

 

theorem homogeneousC2_eq (d : ℕ) :
    A.homogeneousC2 d = A.toVertexAlgebra.c2 ⊓ A.grade d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨e, f, a, b, ha, hb, he, rfl⟩
    exact ⟨A.mode_neg_two_mem_c2 a b,
      A.mode_mem_grade ha hb (-2) (by omega)⟩
  · intro a ha
    simpa only [A.gradeComponent_of_mem ha.2] using A.gradeComponent_c2_mem d ha.1

 

theorem negativeWord_mem_grade {S : ℕ → Set V}
    (hS : ∀ d, ∀ a ∈ S d, a ∈ A.grade d)
    {t w : ℕ} {a : V} (ha : A.NegativeWord S t w a) : a ∈ A.grade w := by
  induction ha with
  | vacuum =>
    rw [A.grade_zero]
    exact Submodule.mem_span_singleton_self _
  | @cons d t w a b ha hb n ih =>
    exact A.mode_mem_grade (hS d a ha) ih (-1 - n) (by omega)

 

def homogeneousNegativeFiltration (S : ℕ → Set V) (t d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {a | ∃ k ≤ t, A.NegativeWord S k d a}

 

theorem gradeComponent_negativeFiltration_mem {S : ℕ → Set V}
    (hS : ∀ d, ∀ a ∈ S d, a ∈ A.grade d) (t d : ℕ) {a : V}
    (ha : a ∈ A.negativeFiltration S t) :
    A.gradeComponent d a ∈ A.homogeneousNegativeFiltration S t d := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, hk, w, ha⟩ := ha
    have hg := A.negativeWord_mem_grade hS ha
    by_cases he : w = d
    · subst w
      rw [A.gradeComponent_of_mem hg]
      exact Submodule.subset_span ⟨k, hk, ha⟩
    · rw [A.gradeComponent_of_mem_ne he hg]
      exact Submodule.zero_mem _
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul z a _ ha => simpa only [map_smul] using Submodule.smul_mem _ z ha

 

theorem homogeneousNegativeFiltration_eq {S : ℕ → Set V}
    (hS : ∀ d, ∀ a ∈ S d, a ∈ A.grade d) (t d : ℕ) :
    A.homogeneousNegativeFiltration S t d = A.negativeFiltration S t ⊓ A.grade d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨k, hk, ha⟩
    exact ⟨Submodule.subset_span ⟨k, hk, d, ha⟩, A.negativeWord_mem_grade hS ha⟩
  · intro a ha
    simpa only [A.gradeComponent_of_mem ha.2] using
      A.gradeComponent_negativeFiltration_mem hS t d ha.1

 

theorem generatorFiltration_le_negativeFiltration {S : ℕ → Set V}
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ a ∈ A.grade d)
    (hgen : ∀ d, A.grade d ≤ A.generatorFiltration S d) :
    ∀ t, A.generatorFiltration S t ≤ A.negativeFiltration S t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    apply Submodule.span_le.mpr
    rintro x ⟨k, hkt, hx⟩
    change x ∈ A.negativeFiltration S t
    cases hx with
    | vacuum => exact A.vacuum_mem_negativeFiltration S t
    | @cons d k a b ha hb n =>
      have hda := hS d a ha
      have hk : k < t := by omega
      have hbF : b ∈ A.negativeFiltration S k :=
        ih k hk (A.modeWord_mem_generatorFiltration hb)
      by_cases hn : n < 0
      · have he : n = -1 - ((-n - 1).toNat : ℤ) := by omega
        rw [he]
        exact A.negativeFiltration_mono S hkt
          (A.negative_generator_mode_mem ha hbF (-n - 1).toNat)
      · have hn0 : 0 ≤ n := by omega
        clear hb
        induction hbF using Submodule.span_induction with
        | mem b hbF =>
          obtain ⟨r, hr, w, hword⟩ := hbF
          cases hword with
          | vacuum => rw [A.creation_truncation a n hn0]; exact Submodule.zero_mem _
          | @cons e r w b c hbg hc q =>
            have hdb := hS e b hbg
            rw [eq_add_of_sub_eq (A.mode_commutator a b c n (-1 - q))]
            apply Submodule.add_mem
            · apply finsum_induction (fun x => x ∈ A.negativeFiltration S t)
                (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
              intro j
              apply Submodule.smul_mem
              by_cases hneg : (e : ℤ) + d - j - 1 < 0
              · rw [A.mode_eq_zero_of_negative_energy hda.2 hdb.2 j hneg, mode_zero]
                simp
              · let p := ((e : ℤ) + d - j - 1).toNat
                have hp : (p : ℤ) = e + d - j - 1 := by dsimp [p]; omega
                have hstate : mode A.fields a j b ∈ A.grade p :=
                  A.mode_mem_grade hda.2 hdb.2 j hp
                have hact := A.generatorFiltration_mode_mem (hgen p hstate)
                  (A.modeWord_mem_generatorFiltration hc.modeWord) (n + (-1 - q) - j)
                have hless : p + r < t := by omega
                exact A.negativeFiltration_mono S hless.le (ih (p + r) hless hact)
            · have hact := A.generator_mode_mem ha
                (A.modeWord_mem_generatorFiltration hc.modeWord) n
              have hless : d + r < t := by omega
              have h := A.negative_generator_mode_mem hbg (ih (d + r) hless hact) q
              exact A.negativeFiltration_mono S (by omega : e + (d + r) ≤ t) h
        | zero => simp
        | add b c _ _ hb hc => simpa only [map_add] using Submodule.add_mem _ hb hc
        | smul z b _ hb => simpa only [map_smul] using Submodule.smul_mem _ z hb

 

theorem generatorFiltration_eq_negativeFiltration {S : ℕ → Set V}
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ a ∈ A.grade d)
    (hgen : ∀ d, A.grade d ≤ A.generatorFiltration S d) (t : ℕ) :
    A.generatorFiltration S t = A.negativeFiltration S t :=
  le_antisymm (A.generatorFiltration_le_negativeFiltration hS hgen t)
    (A.negativeFiltration_le S t)

 
theorem virasoro_mem_grade {e k : ℕ} {b : V} (hb : b ∈ A.grade e)
    (m : ℤ) (hk : (k : ℤ) = e - m) : A.virasoroMode m b ∈ A.grade k := by
  apply A.mode_mem_grade A.conformal_mem hb (m + 1)
  omega

 
theorem virasoro_eq_zero_of_lt {e : ℕ} {b : V} (hb : b ∈ A.grade e)
    (m : ℤ) (hm : (e : ℤ) < m) : A.virasoroMode m b = 0 := by
  apply A.mode_eq_zero_of_negative_energy A.conformal_mem hb (m + 1)
  omega

 

theorem virasoro_neg_one_eq_translation :
    A.virasoroMode (-1) = A.toVertexAlgebra.translation := by
  exact A.conformal_translation

 

theorem translation_mem_generatorFiltration {S : ℕ → Set V} {t : ℕ} {a : V}
    (ha : a ∈ A.generatorFiltration S t) :
    A.virasoroMode (-1) a ∈ A.generatorFiltration S t := by
  rw [A.virasoro_neg_one_eq_translation]
  exact A.generatorFiltration_mode_mem ha (A.vacuum_mem_generatorFiltration S 0) (-2)

 

theorem homogeneousC2_le_generatorFiltration {S : ℕ → Set V} (d : ℕ)
    (hprev : ∀ e < d, A.grade e ≤ A.generatorFiltration S e) :
    A.homogeneousC2 d ≤ A.generatorFiltration S (d - 1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨e, f, a, b, ha, hb, hweight, rfl⟩
  change mode A.fields a (-2) b ∈ A.generatorFiltration S (d - 1)
  have h := A.generatorFiltration_mode_mem (hprev e (by omega) ha)
    (hprev f (by omega) hb) (-2)
  simpa only [show e + f = d - 1 by omega] using h

 
theorem energyShift_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    A.energyShift a = (1 + (d : ℂ)) • a := by
  simp only [energyShift, LinearMap.add_apply, Module.End.one_apply,
    A.virasoro_zero_on_grade ha, add_smul, one_smul]

 
theorem energyShift_pow_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) (k : ℕ) :
    (A.energyShift ^ k) a = (1 + (d : ℂ)) ^ k • a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, A.energyShift_on_grade ha,
      map_smul, ih, smul_smul, pow_succ]
    congr 1
    ring

 
def IsPrimary (a : V) : Prop := ∀ n : ℕ, 0 < n → A.virasoroMode n a = 0

 

inductive PrimaryDescendant : ℕ → V → Prop
  | primary {d : ℕ} {a : V} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) :
      PrimaryDescendant d a
  | raise {d : ℕ} {a : V} (ha : PrimaryDescendant d a) {n : ℕ} (hn : 0 < n) :
      PrimaryDescendant (d + n) (A.virasoroMode (-(n : ℤ)) a)

 
def primaryDescendantSpan : Submodule ℂ V :=
  Submodule.span ℂ {a | ∃ d, A.PrimaryDescendant d a}

theorem PrimaryDescendant.mem_grade {d : ℕ} {a : V} (ha : A.PrimaryDescendant d a) :
    a ∈ A.grade d := by
  induction ha with
  | primary ha _ => exact ha
  | @raise d a ha n hn ih => exact A.virasoro_mem_grade ih (-(n : ℤ)) (by omega)

theorem primary_mem_primaryDescendantSpan {d : ℕ} {a : V}
    (ha : a ∈ A.grade d) (hp : A.IsPrimary a) : a ∈ A.primaryDescendantSpan :=
  Submodule.subset_span ⟨d, PrimaryDescendant.primary ha hp⟩

theorem virasoro_mem_primaryDescendantSpan {a : V} (ha : a ∈ A.primaryDescendantSpan)
    {n : ℕ} (hn : 0 < n) : A.virasoroMode (-(n : ℤ)) a ∈ A.primaryDescendantSpan := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨d, hd⟩ := ha
    exact Submodule.subset_span ⟨d + n, PrimaryDescendant.raise hd hn⟩
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul z a _ ha => simpa only [map_smul] using Submodule.smul_mem _ z ha

 

def lowerVirasoroSpace (d : ℕ) : Submodule ℂ V :=
  ⨆ n : Fin d, (A.grade (d - (n.val + 1))).map (A.virasoroMode (-(n.val + 1 : ℤ)))

theorem lowerVirasoroSpace_le_grade (d : ℕ) : A.lowerVirasoroSpace d ≤ A.grade d := by
  apply iSup_le
  intro n x hx
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  exact A.virasoro_mem_grade ha (-(n.val + 1 : ℤ)) (by have := n.isLt; omega)

theorem virasoro_mem_lowerVirasoroSpace {d n : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    {a : V} (ha : a ∈ A.grade (d - n)) :
    A.virasoroMode (-(n : ℤ)) a ∈ A.lowerVirasoroSpace d := by
  let i : Fin d := ⟨n - 1, by omega⟩
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have hei : (i.val + 1 : ℤ) = n := by omega
  apply Submodule.mem_iSup_of_mem i
  rw [hi, hei]
  exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

 

def zeroModeOnGrade {d : ℕ} {a : V} (ha : a ∈ A.grade d) (h : ℕ) :
    Module.End ℂ (A.grade h) :=
  (A.physicalMode a d 0).restrict (fun b hb =>
    A.mode_mem_grade ha hb ((0 : ℤ) + d - 1) (by omega))

@[simp]
theorem zeroModeOnGrade_apply {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    (h : ℕ) (b : A.grade h) :
    (A.zeroModeOnGrade ha h b : V) = A.physicalMode a d 0 b := rfl

 

def gradedTraceCoefficient {d : ℕ} {a : V} (ha : a ∈ A.grade d) (h : ℕ) : ℂ :=
  LinearMap.trace ℂ (A.grade h) (A.zeroModeOnGrade ha h)

 

def OrdinaryOnePointConvergence : Prop :=
  ∀ d : ℕ, ∀ a : V, ∀ ha : a ∈ A.grade d, ∀ q : ℝ, 0 < q → q < 1 →
    Summable (fun h : ℕ => (q : ℂ) ^ h * A.gradedTraceCoefficient ha h)

 
theorem normalProduct_mem_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    mode A.fields a (-1) a ∈ A.grade (2 * d) :=
  A.mode_mem_grade ha ha (-1) (by omega)

 
def normalProductOnGrade {d : ℕ} {a : V} (ha : a ∈ A.grade d) (h : ℕ) :
    Module.End ℂ (A.grade h) := A.zeroModeOnGrade (A.normalProduct_mem_grade ha) h

@[simp]
theorem normalProductOnGrade_apply {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    (h : ℕ) (b : A.grade h) :
    (A.normalProductOnGrade ha h b : V) =
      mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b := by
  simp only [normalProductOnGrade, zeroModeOnGrade_apply, physicalMode, Nat.cast_mul,
    Nat.cast_ofNat, zero_add]

 

def normalProductTrace {d : ℕ} {a : V} (ha : a ∈ A.grade d) (h : ℕ) : ℝ :=
  (LinearMap.trace ℂ (A.grade h) (A.normalProductOnGrade ha h)).re

 

def IsAdmissible {W : Type v} [AddCommGroup W] [Module ℂ W]
    (M : WeakModule A.toVertexAlgebra W) : Prop :=
  ∃ G : ℤ → Submodule ℂ W,
    DirectSum.IsInternal G ∧ (∀ k : ℤ, k < 0 → G k = ⊥) ∧
      ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n k : ℤ, ∀ x ∈ G k,
        mode M.fields a n x ∈ G (k + d - n - 1)

 

def IsRational : Prop :=
  ∀ (W : Type v) [AddCommGroup W] [Module ℂ W]
    (M : WeakModule A.toVertexAlgebra W),
    A.IsAdmissible M → M.CompletelyReducible

end CFTTypeVOA

end Algebraic

 

theorem re_trace_nonneg_of_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (T : Module.End ℂ E)
    (hT : ∀ x : E, 0 ≤ (inner ℂ (T x) x).re) :
    0 ≤ (LinearMap.trace ℂ E T).re := by
  classical
  rw [T.trace_eq_sum_inner (stdOrthonormalBasis ℂ E)]
  simp only [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have he : (inner ℂ ((stdOrthonormalBasis ℂ E) i) (T ((stdOrthonormalBasis ℂ E) i))).re =
      (inner ℂ (T ((stdOrthonormalBasis ℂ E) i)) ((stdOrthonormalBasis ℂ E) i)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  exact hT ((stdOrthonormalBasis ℂ E) i)

 

theorem quadratic_le_re_trace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (T : Module.End ℂ E)
    (hT : ∀ x : E, 0 ≤ (inner ℂ (T x) x).re) (x : E) (hx : ‖x‖ = 1) :
    (inner ℂ (T x) x).re ≤ (LinearMap.trace ℂ E T).re := by
  classical
  have ho : Orthonormal ℂ (Subtype.val : ({x} : Set E) → E) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have hi : (i : E) = x := Set.mem_singleton_iff.mp i.property
    simpa only [hi] using hx
  obtain ⟨s, b, hs, hb⟩ := ho.exists_orthonormalBasis_extension
  let i : s := ⟨x, hs (Set.mem_singleton x)⟩
  have hbi : b i = x := by rw [hb]
  rw [T.trace_eq_sum_inner b]
  simp only [Complex.re_sum]
  have hpos (j : s) : 0 ≤ (inner ℂ (b j) (T (b j))).re := by
    have he : (inner ℂ (b j) (T (b j))).re = (inner ℂ (T (b j)) (b j)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [he]
    exact hT (b j)
  have hle := Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
  rw [hbi] at hle
  have he : (inner ℂ (T x) x).re = (inner ℂ x (T x)).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  exact hle

namespace CFTTypeVOA

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

def PolynomialEnergyBound (a : V) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p k : ℕ, ∀ (n : ℤ) (b : V),
    ‖mode A.fields a n b‖ ≤ C * (1 + |(n : ℝ)|) ^ p * ‖(A.energyShift ^ k) b‖

 

def PolynomialEnergyBounds : Prop := ∀ a : V, A.PolynomialEnergyBound a

 

theorem vacuum_energyBound : A.PolynomialEnergyBound A.vacuum := by
  refine ⟨1, by norm_num, 0, 0, ?_⟩
  intro n b
  rw [A.vacuum_mode]
  split_ifs <;> simp

 

theorem energyShift_pow_norm_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) (k : ℕ) :
    ‖(A.energyShift ^ k) a‖ = (1 + (d : ℝ)) ^ k * ‖a‖ := by
  rw [A.energyShift_pow_on_grade ha, norm_smul, norm_pow]
  congr 2
  have h : (1 + (d : ℂ)) = ((1 + (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

 

def modeBlock (a : V) (d h k : ℕ) : A.grade h →L[ℂ] V := by
  let := A.grade_finite h
  exact LinearMap.toContinuousLinearMap
    ((A.physicalMode a d ((h : ℤ) - k)).domRestrict (A.grade h))

@[simp]
theorem modeBlock_apply (a : V) (d h k : ℕ) (c : A.grade h) :
    A.modeBlock a d h k c = A.physicalMode a d ((h : ℤ) - k) c := rfl

 

def BlockControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ h ≤ N, ∀ k ≤ N, ∀ c ∈ A.grade h,
    ‖A.physicalMode a d ((h : ℤ) - k) c‖ ≤ K * ‖c‖

theorem blockControl_mono {a : V} {d N : ℕ} {K L : ℝ}
    (H : A.BlockControl a d N K) (hKL : K ≤ L) : A.BlockControl a d N L := by
  intro h hh k hk c hc
  exact (H h hh k hk c hc).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem blockControl_zero (d N : ℕ) : A.BlockControl 0 d N 0 := by
  intro h hh k hk c hc
  simp [physicalMode]

theorem blockControl_add {a b : V} {d N : ℕ} {K L : ℝ}
    (ha : A.BlockControl a d N K) (hb : A.BlockControl b d N L) :
    A.BlockControl (a + b) d N (K + L) := by
  intro h hh k hk c hc
  change ‖(mode A.fields (a + b) _) c‖ ≤ _
  rw [mode_add, LinearMap.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (ha h hh k hk c hc) (hb h hh k hk c hc))

theorem blockControl_smul {a : V} {d N : ℕ} {K : ℝ}
    (ha : A.BlockControl a d N K) (z : ℂ) :
    A.BlockControl (z • a) d N (‖z‖ * K) := by
  intro h hh k hk c hc
  change ‖(mode A.fields (z • a) _) c‖ ≤ _
  rw [mode_smul, LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (ha h hh k hk c hc) (norm_nonneg _)

 

def correctionMass (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)

theorem correctionMass_nonneg (d : ℕ) : 0 ≤ correctionMass d := by
  unfold correctionMass
  positivity

 

theorem normalProduct_blockControl {a b : V} {d e N : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    {K L R : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : A.BlockControl a d N K) (Hb : A.BlockControl b e N L)
    (Hsing : ∀ j < d - 1, A.BlockControl (mode A.fields a j b) (d + e - j - 1) N R) :
    A.BlockControl (mode A.fields a (-1) b) (d + e) N
      (((2 : ℝ) * N + 1) * K * L + correctionMass d * R) := by
  classical
  intro h hh k hk c hc
  let f : ℕ → V := fun j => A.physicalMode a d (-1 - j)
    (A.physicalMode b e ((h : ℤ) - k + 1 + j) c)
  let g : ℕ → V := fun j => A.physicalMode b e ((h : ℤ) - k - j)
    (A.physicalMode a d j c)
  let r : ℕ → ℕ → V := fun i j => (i.choose j : ℂ) •
    mode A.fields (mode A.fields a j b) ((h : ℤ) - k + d + e - 2 - j) c
  have hf (j : ℕ) (hj : j ∈ Finset.range k) : ‖f j‖ ≤ K * L * ‖c‖ := by
    simp only [Finset.mem_range] at hj
    let l := k - 1 - j
    have hl : l ≤ N := by dsimp [l]; omega
    have hidx : (h : ℤ) - l = (h : ℤ) - k + 1 + j := by dsimp [l]; omega
    have hidx' : (l : ℤ) - k = -1 - j := by dsimp [l]; omega
    have hx : A.physicalMode b e ((h : ℤ) - k + 1 + j) c ∈ A.grade l :=
      A.mode_mem_grade hb hc _ (by dsimp [l]; omega)
    have H₁ := Ha l hl k hk _ hx
    have H₂ := Hb h hh l hl c hc
    rw [hidx'] at H₁
    rw [hidx] at H₂
    calc
      ‖f j‖ ≤ K * ‖A.physicalMode b e ((h : ℤ) - k + 1 + j) c‖ := H₁
      _ ≤ K * (L * ‖c‖) := mul_le_mul_of_nonneg_left H₂ hK
      _ = _ := by ring
  have hg (j : ℕ) (hj : j ∈ Finset.range (h + 1)) : ‖g j‖ ≤ K * L * ‖c‖ := by
    simp only [Finset.mem_range] at hj
    let l := h - j
    have hl : l ≤ N := by dsimp [l]; omega
    have hidx : (h : ℤ) - l = j := by dsimp [l]; omega
    have hidx' : (l : ℤ) - k = (h : ℤ) - k - j := by dsimp [l]; omega
    have hx : A.physicalMode a d j c ∈ A.grade l :=
      A.mode_mem_grade ha hc _ (by dsimp [l]; omega)
    have H₁ := Hb l hl k hk _ hx
    have H₂ := Ha h hh l hl c hc
    rw [hidx'] at H₁
    rw [hidx] at H₂
    calc
      ‖g j‖ ≤ L * ‖A.physicalMode a d j c‖ := H₁
      _ ≤ L * (K * ‖c‖) := mul_le_mul_of_nonneg_left H₂ hL
      _ = _ := by ring
  have hr (i : ℕ) (hi : i ∈ Finset.range (d - 1))
      (j : ℕ) (hj : j ∈ Finset.range (i + 1)) : ‖r i j‖ ≤ (i.choose j : ℝ) * R * ‖c‖ := by
    simp only [Finset.mem_range] at hi hj
    have hjs : j < d - 1 := by omega
    have H := Hsing j hjs h hh k hk c hc
    have he : (h : ℤ) - k + (d + e - j - 1 : ℕ) - 1 =
        (h : ℤ) - k + d + e - 2 - j := by omega
    simp only [physicalMode, he] at H
    dsimp only [r]
    rw [norm_smul, Complex.norm_natCast, mul_assoc]
    exact mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)
  have hfs : ‖∑ j ∈ Finset.range k, f j‖ ≤ (k : ℝ) * (K * L * ‖c‖) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      norm_sum_le_of_le (Finset.range k) hf
  have hgs : ‖∑ j ∈ Finset.range (h + 1), g j‖ ≤ ((h : ℝ) + 1) * (K * L * ‖c‖) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      norm_sum_le_of_le (Finset.range (h + 1)) hg
  have hrs : ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j‖ ≤
      correctionMass d * R * ‖c‖ := by
    have H := norm_sum_le_of_le (Finset.range (d - 1)) (fun i hi =>
      norm_sum_le_of_le (Finset.range (i + 1)) (hr i hi))
    simpa only [correctionMass, Finset.sum_mul] using H
  rw [A.physical_normal_product_on_grade ha hb hc hd k]
  change ‖(∑ j ∈ Finset.range k, f j) + (∑ j ∈ Finset.range (h + 1), g j) -
    (∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j)‖ ≤ _
  calc
    _ ≤ ‖∑ j ∈ Finset.range k, f j‖ + ‖∑ j ∈ Finset.range (h + 1), g j‖ +
        ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (k : ℝ) * (K * L * ‖c‖) + ((h : ℝ) + 1) * (K * L * ‖c‖) +
        correctionMass d * R * ‖c‖ := add_le_add (add_le_add hfs hgs) hrs
    _ = ((h : ℝ) + k + 1) * (K * L * ‖c‖) + correctionMass d * R * ‖c‖ := by ring
    _ ≤ ((2 : ℝ) * N + 1) * (K * L * ‖c‖) + correctionMass d * R * ‖c‖ := by
      have hcount : (h : ℝ) + k + 1 ≤ (2 : ℝ) * N + 1 := by
        exact_mod_cast (show h + k + 1 ≤ 2 * N + 1 by omega)
      gcongr
    _ = _ := by ring
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
