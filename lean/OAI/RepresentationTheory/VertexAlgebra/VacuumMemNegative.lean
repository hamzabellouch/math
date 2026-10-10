import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.FiniteSums

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
section Algebraic
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
namespace VertexAlgebra
variable (A : VertexAlgebra V)
theorem vacuum_mem_negativeFiltration (S : ℕ → Set V) (t : ℕ) :
    A.vacuum ∈ A.negativeFiltration S t :=
  Submodule.subset_span ⟨0, Nat.zero_le _, 0, NegativeWord.vacuum⟩

 

theorem negative_generator_mode_mem {S : ℕ → Set V} {d t : ℕ} {a b : V}
    (ha : a ∈ S d) (hb : b ∈ A.negativeFiltration S t) (n : ℕ) :
    mode A.fields a (-1 - n) b ∈ A.negativeFiltration S (d + t) := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨k, hk, w, hb⟩ := hb
    exact Submodule.subset_span ⟨d + k, Nat.add_le_add_left hk d,
      d + w + n, NegativeWord.cons ha hb n⟩
  | zero => simp
  | add b c _ _ hb hc => simpa only [map_add] using Submodule.add_mem _ hb hc
  | smul z b _ hb => simpa only [map_smul] using Submodule.smul_mem _ z hb

 
def translation : Module.End ℂ V where
  toFun a := mode A.fields a (-2) A.vacuum
  map_add' a b := by simp [mode]
  map_smul' z a := by simp [mode]

 
def c2 : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ a b : V, x = mode A.fields a (-2) b}

 
theorem mode_neg_two_mem_c2 (a b : V) : mode A.fields a (-2) b ∈ A.c2 := by
  exact Submodule.subset_span ⟨a, b, rfl⟩

 
def C2Cofinite : Prop := FiniteDimensional ℂ (V ⧸ A.c2)

 
def IsIdeal (I : Submodule ℂ V) : Prop :=
  (∀ a : V, ∀ n : ℤ, ∀ x ∈ I, mode A.fields a n x ∈ I) ∧
  ∀ x ∈ I, A.translation x ∈ I

 
def IsSimple : Prop :=
  A.vacuum ≠ 0 ∧ ∀ I : Submodule ℂ V, A.IsIdeal I → I = ⊥ ∨ I = ⊤

end VertexAlgebra

 

def ModuleJacobiIdentity {W : Type v} [AddCommGroup W] [Module ℂ W]
    (A : VertexAlgebra V) (Y : StateField V W) : Prop :=
  ∀ (a b : V) (c : W) (m n k : ℤ),
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      mode Y (mode A.fields a (n + j) b) (m + k - j) c) =
    ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * Ring.choose (n : ℂ) j) •
      (mode Y a (m + n - j) (mode Y b (k + j) c) -
        (-1 : ℂ) ^ n • mode Y b (n + k - j) (mode Y a (m + j) c))

 

structure WeakModule (A : VertexAlgebra V) (W : Type v)
    [AddCommGroup W] [Module ℂ W] where
  fields : StateField V W
  vacuum_mode : ∀ n : ℤ, mode fields A.vacuum n = if n = -1 then 1 else 0
  jacobi : ModuleJacobiIdentity A fields

namespace WeakModule

variable {W : Type v} [AddCommGroup W] [Module ℂ W]
    {A : VertexAlgebra V} (M : WeakModule A W)

 
def IsInvariant (I : Submodule ℂ W) : Prop :=
  ∀ a : V, ∀ n : ℤ, ∀ x ∈ I, mode M.fields a n x ∈ I

 
def CompletelyReducible : Prop :=
  ∀ I : Submodule ℂ W, M.IsInvariant I →
    ∃ J : Submodule ℂ W, M.IsInvariant J ∧ IsCompl I J

 

theorem mode_commutator (a b : V) (c : W) (m k : ℤ) :
    mode M.fields a m (mode M.fields b k c) -
      mode M.fields b k (mode M.fields a m c) =
    ∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      mode M.fields (mode A.fields a j b) (m + k - j) c := by
  have h := M.jacobi a b c m 0 k
  have hz (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 := by
    rw [← Nat.cast_zero, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj), Nat.cast_zero]
  conv_rhs at h =>
    rw [finsum_eq_single _ 0 (by
      intro j hj
      simp only [Int.cast_zero, hz j hj, mul_zero, zero_smul])]
  simpa using h.symm

end WeakModule

 

structure CFTTypeVOA (V : Type u) [AddCommGroup V] [Module ℂ V]
    extends VertexAlgebra V where
  conformalVector : V
  centralCharge : ℂ
  grade : ℕ → Submodule ℂ V
  grading_internal : DirectSum.IsInternal grade
  grade_finite : ∀ d, FiniteDimensional ℂ (grade d)
  vacuum_ne_zero : vacuum ≠ 0
  grade_zero : grade 0 = ℂ ∙ vacuum
  conformal_mem : conformalVector ∈ grade 2
  conformal_energy : ∀ d, ∀ a ∈ grade d,
    mode fields conformalVector 1 a = (d : ℂ) • a
  conformal_translation : mode fields conformalVector 0 = toVertexAlgebra.translation
  translation_covariance : ∀ a : V, ∀ n : ℤ,
    mode fields (toVertexAlgebra.translation a) n =
      (-(n : ℂ)) • mode fields a (n - 1)
  virasoro : ∀ m n : ℤ,
    (mode fields conformalVector (m + 1)).comp (mode fields conformalVector (n + 1)) -
      (mode fields conformalVector (n + 1)).comp (mode fields conformalVector (m + 1)) =
    ((m - n : ℤ) : ℂ) • mode fields conformalVector (m + n + 1) +
      (if m + n = 0 then (centralCharge / 12) * ((m : ℂ)^3 - m) else 0) •
        (1 : Module.End ℂ V)

namespace CFTTypeVOA

variable (A : CFTTypeVOA V)

 
def virasoroMode (m : ℤ) : Module.End ℂ V :=
  mode A.fields A.conformalVector (m + 1)

 
def physicalMode (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ V :=
  mode A.fields a (m + d - 1)

 
def energyShift : Module.End ℂ V := 1 + A.virasoroMode 0

 
def IsQuasiPrimary (a : V) : Prop := A.virasoroMode 1 a = 0

 

def gradingEquiv : V ≃ₗ[ℂ] DirectSum ℕ (fun d => A.grade d) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap A.grade) A.grading_internal).symm

 
def gradeComponent (d : ℕ) : Module.End ℂ V :=
  (A.grade d).subtype.comp ((DirectSum.component ℂ ℕ (fun d => A.grade d) d).comp
    A.gradingEquiv.toLinearMap)

@[simp]
theorem gradeComponent_apply (d : ℕ) (a : V) :
    A.gradeComponent d a = (A.gradingEquiv a d : V) := rfl

theorem gradeComponent_mem (d : ℕ) (a : V) : A.gradeComponent d a ∈ A.grade d :=
  (A.gradingEquiv a d).property

theorem gradeComponent_of_mem {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    A.gradeComponent d a = a := by
  exact congrArg Subtype.val (A.grading_internal.ofBijective_coeLinearMap_of_mem ha)

theorem gradeComponent_of_mem_ne {d e : ℕ} (hde : e ≠ d) {a : V}
    (ha : a ∈ A.grade e) : A.gradeComponent d a = 0 := by
  exact congrArg Subtype.val
    (A.grading_internal.ofBijective_coeLinearMap_of_mem_ne hde ha)

 
def gradeSupport (a : V) : Finset ℕ := by
  classical
  exact (A.gradingEquiv a).support

 
theorem sum_gradeComponents (a : V) :
    ∑ d ∈ A.gradeSupport a, A.gradeComponent d a = a := by
  classical
  change ∑ d ∈ (A.gradingEquiv a).support, A.gradeComponent d a = a
  calc
    _ = DirectSum.coeLinearMap A.grade
        (∑ d ∈ (A.gradingEquiv a).support,
          DirectSum.of (fun d => A.grade d) d (A.gradingEquiv a d)) := by
      simp only [map_sum, DirectSum.coeLinearMap_of, gradeComponent_apply]
    _ = DirectSum.coeLinearMap A.grade (A.gradingEquiv a) := by
      rw [DirectSum.sum_support_of]
    _ = a := (LinearEquiv.ofBijective (DirectSum.coeLinearMap A.grade)
      A.grading_internal).apply_symm_apply a

 

theorem homogeneous_induction {P : V → Prop} (h0 : P 0)
    (hh : ∀ d : ℕ, ∀ a ∈ A.grade d, P a)
    (hadd : ∀ a b : V, P a → P b → P (a + b)) (a : V) : P a := by
  let : DirectSum.Decomposition A.grade := A.grading_internal.chooseDecomposition
  exact DirectSum.Decomposition.inductionOn A.grade h0
    (fun {d} x => hh d x x.property) hadd a

 
theorem virasoro_commutator (m n : ℤ) (a : V) :
    A.virasoroMode m (A.virasoroMode n a) -
      A.virasoroMode n (A.virasoroMode m a) =
    ((m - n : ℤ) : ℂ) • A.virasoroMode (m + n) a +
      (if m + n = 0 then (A.centralCharge / 12) * ((m : ℂ)^3 - m) else 0) • a := by
  have h := congrArg (fun T : Module.End ℂ V => T a) (A.virasoro m n)
  simpa only [virasoroMode, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply] using h

 
theorem virasoro_vacuum (m : ℤ) (hm : -1 ≤ m) :
    A.virasoroMode m A.vacuum = 0 := by
  exact A.creation_truncation A.conformalVector (m + 1) (by omega)

 
theorem conformal_eq_virasoro_vacuum :
    A.conformalVector = A.virasoroMode (-2) A.vacuum := by
  exact (A.creation A.conformalVector).symm

 
theorem conformal_quasiPrimary : A.IsQuasiPrimary A.conformalVector := by
  have h := A.virasoro_commutator 1 (-2) A.vacuum
  have h₁ := A.virasoro_vacuum 1 (by omega)
  have h₂ := A.virasoro_vacuum (-1) (by omega)
  norm_num at h
  rw [h₁, map_zero, sub_zero, h₂, smul_zero] at h
  simpa only [IsQuasiPrimary, A.conformal_eq_virasoro_vacuum] using h

 
theorem virasoro_two_conformal :
    A.virasoroMode 2 A.conformalVector = (A.centralCharge / 2) • A.vacuum := by
  have h := A.virasoro_commutator 2 (-2) A.vacuum
  have h₂ := A.virasoro_vacuum 2 (by omega)
  have h₀ := A.virasoro_vacuum 0 (by omega)
  norm_num at h
  rw [h₂, map_zero, sub_zero, h₀, smul_zero, zero_add] at h
  rw [← A.conformal_eq_virasoro_vacuum] at h
  convert h using 1
  congr 1
  ring

 
theorem physicalMode_conformal (m : ℤ) :
    A.physicalMode A.conformalVector 2 m = A.virasoroMode m := by
  unfold physicalMode virasoroMode
  congr 1
  omega

 
theorem virasoro_zero_on_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    A.virasoroMode 0 a = (d : ℂ) • a := A.conformal_energy d a ha

 
theorem gradeComponent_energy (d : ℕ) (a : V) :
    A.gradeComponent d (A.virasoroMode 0 a) = (d : ℂ) • A.gradeComponent d a := by
  apply A.homogeneous_induction (P := fun a =>
    A.gradeComponent d (A.virasoroMode 0 a) = (d : ℂ) • A.gradeComponent d a)
  · simp
  · intro e b hb
    rw [A.virasoro_zero_on_grade hb, map_smul]
    by_cases he : e = d
    · subst e
      rfl
    · rw [A.gradeComponent_of_mem_ne he hb]
      simp
  · intro b c hb hc
    simp only [map_add, smul_add, hb, hc]

 
theorem gradeComponent_eigenvalue {a : V} {z : ℂ}
    (ha : A.virasoroMode 0 a = z • a) (d : ℕ) (hd : (d : ℂ) ≠ z) :
    A.gradeComponent d a = 0 := by
  have h := congrArg (A.gradeComponent d) ha
  rw [A.gradeComponent_energy, map_smul] at h
  have h' : ((d : ℂ) - z) • A.gradeComponent d a = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hd)

 
theorem mem_grade_of_energy {d : ℕ} {a : V}
    (ha : A.virasoroMode 0 a = (d : ℂ) • a) : a ∈ A.grade d := by
  classical
  rw [← A.sum_gradeComponents a]
  apply Submodule.sum_mem
  intro e _
  by_cases he : e = d
  · subst e
    exact A.gradeComponent_mem d a
  · rw [A.gradeComponent_eigenvalue ha e (by exact_mod_cast he)]
    exact (A.grade d).zero_mem

 
theorem eq_zero_of_energy_not_grade {a : V} {z : ℂ}
    (ha : A.virasoroMode 0 a = z • a) (hz : ∀ d : ℕ, (d : ℂ) ≠ z) : a = 0 := by
  classical
  rw [← A.sum_gradeComponents a]
  apply Finset.sum_eq_zero
  intro d _
  exact A.gradeComponent_eigenvalue ha d (hz d)

 

theorem energy_mode_commutator_general (a : V) (n : ℤ) (b : V) :
    A.virasoroMode 0 (mode A.fields a n b) -
      mode A.fields a n (A.virasoroMode 0 b) =
        (-((n : ℂ) + 1)) • mode A.fields a n b +
          mode A.fields (A.virasoroMode 0 a) n b := by
  classical
  have h := A.toVertexAlgebra.mode_commutator A.conformalVector a b 1 n
  have hz (j : ℕ) (hj : 2 ≤ j) : Ring.choose (1 : ℂ) j = 0 := by
    rw [← Nat.cast_one, Ring.choose_natCast,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 2) (by
    intro j hj
    by_contra hj'
    have hj'' : 2 ≤ j := by
      simp only [Finset.mem_coe, Finset.mem_range] at hj'
      omega
    exact hj (by simp [hz j hj'']))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, Ring.choose_zero_right, Ring.choose_one_right,
    one_smul, Int.sub_zero] at h
  rw [A.conformal_translation, A.translation_covariance] at h
  simp only [LinearMap.smul_apply] at h
  have hi : 1 + n - 1 = n := by omega
  simp only [hi, Int.cast_one, one_smul, Int.cast_add] at h
  convert h using 1
  · rfl
  · simp only [virasoroMode, zero_add, add_comm]

 

theorem energy_mode_commutator {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    (n : ℤ) (b : V) :
    A.virasoroMode 0 (mode A.fields a n b) -
      mode A.fields a n (A.virasoroMode 0 b) =
        ((d : ℂ) - n - 1) • mode A.fields a n b := by
  rw [A.energy_mode_commutator_general, A.virasoro_zero_on_grade ha,
    mode_smul, LinearMap.smul_apply, ← add_smul]
  congr 1
  ring

 

theorem energy_preserves_c2 :
    A.toVertexAlgebra.c2 ≤ (A.toVertexAlgebra.c2).comap (A.virasoroMode 0) := by
  intro x hx
  change A.virasoroMode 0 x ∈ A.toVertexAlgebra.c2
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun z x _ hx => ?_) hx
  · obtain ⟨a, b, rfl⟩ := hx
    have he := A.energy_mode_commutator_general a (-2) b
    rw [sub_eq_iff_eq_add] at he
    rw [he]
    exact (A.toVertexAlgebra.c2).add_mem
      ((A.toVertexAlgebra.c2).add_mem
        ((A.toVertexAlgebra.c2).smul_mem _ (A.mode_neg_two_mem_c2 a b))
        (A.mode_neg_two_mem_c2 _ b)) (A.mode_neg_two_mem_c2 a _)
  · simp
  · simpa only [map_add] using (A.toVertexAlgebra.c2).add_mem hx hy
  · simpa only [map_smul] using (A.toVertexAlgebra.c2).smul_mem z hx

 
def c2Energy : Module.End ℂ (V ⧸ A.toVertexAlgebra.c2) :=
  (A.toVertexAlgebra.c2).mapQ A.toVertexAlgebra.c2
    (A.virasoroMode 0) A.energy_preserves_c2

 

theorem exists_c2_weight_cutoff (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ d : ℕ, D < d → A.grade d ≤ A.toVertexAlgebra.c2 := by
  let : FiniteDimensional ℂ (V ⧸ A.toVertexAlgebra.c2) := hc
  have hs : Set.Finite {d : ℕ | A.c2Energy.HasEigenvalue (d : ℂ)} :=
    A.c2Energy.finite_hasEigenvalue.preimage (by
      intro d _ e _ h
      exact_mod_cast h)
  obtain ⟨D, hD⟩ := hs.bddAbove
  refine ⟨max 2 D, le_max_left _ _, fun d hd a ha => ?_⟩
  by_contra hn
  have hq : (A.toVertexAlgebra.c2).mkQ a ≠ 0 := by
    simpa only [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hn
  have he : A.c2Energy.HasEigenvalue (d : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hq⟩
    rw [Module.End.mem_eigenspace_iff]
    change (A.toVertexAlgebra.c2).mkQ (A.virasoroMode 0 a) =
      (d : ℂ) • (A.toVertexAlgebra.c2).mkQ a
    rw [A.virasoro_zero_on_grade ha, map_smul]
  have hb : d ≤ D := hD he
  omega

 

theorem mode_energy_eigenvalue {d e : ℕ} {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (n : ℤ) :
    A.virasoroMode 0 (mode A.fields a n b) =
      ((e : ℂ) + d - n - 1) • mode A.fields a n b := by
  have h := A.energy_mode_commutator ha n b
  rw [A.virasoro_zero_on_grade hb, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← add_smul]
  congr 1
  ring

 

theorem mode_mem_grade {d e k : ℕ} {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (n : ℤ)
    (hk : (k : ℤ) = e + d - n - 1) : mode A.fields a n b ∈ A.grade k := by
  apply A.mem_grade_of_energy
  rw [A.mode_energy_eigenvalue ha hb]
  congr 1
  exact_mod_cast hk.symm

 

theorem mode_eq_zero_of_negative_energy {d e : ℕ} {a b : V}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (n : ℤ)
    (hn : (e : ℤ) + d - n - 1 < 0) : mode A.fields a n b = 0 := by
  apply A.eq_zero_of_energy_not_grade (A.mode_energy_eigenvalue ha hb n)
  intro k h
  have hh : (k : ℤ) = (e : ℤ) + d - n - 1 := by exact_mod_cast h
  omega

 

theorem physical_normal_product_resplit (a b c : V) (d e : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    A.physicalMode (mode A.fields a (-1) b) (d + e) m c =
      (∑ᶠ j : ℕ, A.physicalMode a d (-1 - j)
        (A.physicalMode b e (m + 1 + j) c)) +
      (∑ᶠ j : ℕ, A.physicalMode b e (m - j)
        (A.physicalMode a d j c)) -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode A.fields (mode A.fields a j b)
          (m + d + e - 2 - j) c := by
  have h := A.mode_normal_product_resplit a b c (m + d + e - 1) (d - 1)
  simp only [Nat.cast_sub hd, Nat.cast_one] at h
  simp_rw [A.mode_commutator_nat] at h
  have E₁ (j : ℕ) : (d : ℤ) - 1 - 1 - j = -1 - j + d - 1 := by omega
  have E₂ (j : ℕ) : m + d + e - 1 - ((d : ℤ) - 1) + j = m + 1 + j + e - 1 := by omega
  have E₃ (j : ℕ) : m + d + e - 1 - 1 - ((d : ℤ) - 1) - j = m - j + e - 1 := by omega
  have E₄ (j : ℕ) : (d : ℤ) - 1 + j = (j : ℤ) + d - 1 := by omega
  have E₅ (i j : ℕ) : (i : ℤ) + (m + d + e - 1 - 1 - i) - j = m + d + e - 2 - j := by omega
  simp_rw [E₁, E₂, E₃, E₄, E₅] at h
  simpa only [physicalMode, Nat.cast_add, ← add_assoc] using h

 

theorem physical_normal_product_on_grade {a b c : V} {d e h : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hc : c ∈ A.grade h)
    (hd : 1 ≤ d) (k : ℕ) :
    A.physicalMode (mode A.fields a (-1) b) (d + e) ((h : ℤ) - k) c =
      (∑ j ∈ Finset.range k, A.physicalMode a d (-1 - j)
        (A.physicalMode b e ((h : ℤ) - k + 1 + j) c)) +
      (∑ j ∈ Finset.range (h + 1), A.physicalMode b e ((h : ℤ) - k - j)
        (A.physicalMode a d j c)) -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode A.fields (mode A.fields a j b)
          ((h : ℤ) - k + d + e - 2 - j) c := by
  classical
  rw [A.physical_normal_product_resplit a b c d e hd ((h : ℤ) - k)]
  have hL : Function.support (fun j : ℕ => A.physicalMode a d (-1 - j)
      (A.physicalMode b e ((h : ℤ) - k + 1 + j) c)) ⊆
      (Finset.range k : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra he
    apply hj
    change A.physicalMode a d (-1 - j) (mode A.fields b _ c) = 0
    rw [A.mode_eq_zero_of_negative_energy hb hc _ (by omega), map_zero]
  have hR : Function.support (fun j : ℕ => A.physicalMode b e ((h : ℤ) - k - j)
      (A.physicalMode a d j c)) ⊆ (Finset.range (h + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra he
    apply hj
    change A.physicalMode b e ((h : ℤ) - k - j) (mode A.fields a _ c) = 0
    rw [A.mode_eq_zero_of_negative_energy ha hc _ (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hR]

 

def homogeneousC2 (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ (e f : ℕ) (a b : V),
    a ∈ A.grade e ∧ b ∈ A.grade f ∧ e + f + 1 = d ∧
      x = mode A.fields a (-2) b}

 

theorem gradeComponent_c2Product_mem (d : ℕ) (a b : V) :
    A.gradeComponent d (mode A.fields a (-2) b) ∈ A.homogeneousC2 d := by
  revert b
  refine A.homogeneous_induction
    (P := fun a => ∀ b : V,
      A.gradeComponent d (mode A.fields a (-2) b) ∈ A.homogeneousC2 d) ?_ ?_ ?_ a
  · intro b
    simp
  · intro e a ha b
    refine A.homogeneous_induction
      (P := fun b => A.gradeComponent d (mode A.fields a (-2) b) ∈ A.homogeneousC2 d)
      ?_ ?_ ?_ b
    · simp
    · intro f b hb
      have hg : mode A.fields a (-2) b ∈ A.grade (e + f + 1) :=
        A.mode_mem_grade ha hb (-2) (by omega)
      by_cases he : e + f + 1 = d
      · rw [A.gradeComponent_of_mem (he ▸ hg)]
        exact Submodule.subset_span ⟨e, f, a, b, ha, hb, he, rfl⟩
      · rw [A.gradeComponent_of_mem_ne he hg]
        exact (A.homogeneousC2 d).zero_mem
    · intro b c hb hc
      simpa only [map_add] using (A.homogeneousC2 d).add_mem hb hc
  · intro a a' ha ha' b
    simpa only [mode_add, LinearMap.add_apply, map_add] using
      (A.homogeneousC2 d).add_mem (ha b) (ha' b)
end CFTTypeVOA
end Algebraic
end StronglyRationalVOA

end

end OAI
