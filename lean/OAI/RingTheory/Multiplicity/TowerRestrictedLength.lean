import Mathlib
import OAI.RingTheory.Multiplicity.CoefficientFieldLocalSection

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
attribute [local instance] Classical.propDecidable
namespace Lech.NormalizedLength.Tower
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {P C : Type u} [CommRing P] [CommRing C]
  (T : Tower P) (f : P →+* C)

 

lemma restrictedLength_zero_of_ranges {ι : Type v} {M : ModuleCat.{u} C}
    (G : ι → ModuleCat.{u} C) (φ : ∀ i, G i ⟶ M)
    (hG : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (G i)) = 0)
    (hspan : (⨆ i, ((ModuleCat.restrictScalars f).map (φ i)).hom.range) = ⊤) :
    T.length ((ModuleCat.restrictScalars f).obj M) = 0 := by
  classical
  let U := fun i => ((ModuleCat.restrictScalars f).map (φ i)).hom.range
  have hU : ∀ i, T.length (U i) = 0 := fun i =>
    le_antisymm ((T.length_range_le _).trans_eq (hG i)) bot_le
  have ht := T.length_iSup_eq_zero U hU
  rw [show (⨆ i, U i) = ⊤ from hspan,T.length_top] at ht
  exact ht

lemma restrictedLength_directSum_zero {ι : Type u}
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (hG : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (G i))) = 0) :
    T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (⨁ i, G i))) = 0 := by
  classical
  apply T.restrictedLength_zero_of_ranges f (fun i => ModuleCat.of C (G i))
    (fun i => ModuleCat.ofHom (DirectSum.lof C ι G i)) hG
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of i x => exact Submodule.mem_iSup_of_mem i ⟨x,rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ hx hy

lemma restrictedLength_directLimit_zero {ι : Type u} [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (g : ∀ i j, i ≤ j → G i →ₗ[C] G j)
    (hG : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (G i))) = 0) :
    T.length ((ModuleCat.restrictScalars f).obj
      (ModuleCat.of C (Module.DirectLimit G g))) = 0 := by
  classical
  apply T.restrictedLength_zero_of_ranges f (fun i => ModuleCat.of C (G i))
    (fun i => ModuleCat.ofHom (Module.DirectLimit.of C ι G g i)) hG
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨i,y,hy⟩ := Module.DirectLimit.exists_of (show Module.DirectLimit G g from x)
  exact Submodule.mem_iSup_of_mem i ⟨y,hy⟩

lemma restrictedLength_iSup_zero {ι : Type v} {M : Type u}
    [AddCommGroup M] [Module C M] (U : ι → Submodule C M)
    (hU : ∀ i, T.length ((ModuleCat.restrictScalars f).obj (ModuleCat.of C (U i))) = 0) :
    T.length ((ModuleCat.restrictScalars f).obj
      (ModuleCat.of C (⨆ i, U i : Submodule C M))) = 0 := by
  classical
  let : Algebra P C := f.toAlgebra
  let : Module P M := Module.compHom M f
  let : IsScalarTower P C M := ⟨fun a b x => by
    change (f a*b) • x = f a • b • x
    exact mul_smul _ _ _⟩
  have hz := T.length_iSup_eq_zero (fun i => (U i).restrictScalars P) (by
    intro i
    exact hU i)
  rw [← Submodule.restrictScalars_iSup P U] at hz
  exact hz
end Lech.NormalizedLength.Tower


namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal DirectSum
universe u
 

namespace AllModuleLength
variable {C : Type u} [CommRing C] (ell : AllModuleLength C)
 

end AllModuleLength
end Lech


namespace Lech.NormalizedLength.Tower
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal DirectSum
universe u
variable {P C : Type u} [CommRing P] [CommRing C]
  (T : Tower P) (f : P →+* C)

 

noncomputable def allModuleLength (r : ℝ≥0∞) (hr : r ≠ 0) : Lech.AllModuleLength C where
  value M := r*T.length ((ModuleCat.restrictScalars f).obj M)
  zero h := by
    have hz := (T.torsionLength f ⊥).zero h
    change T.length ((ModuleCat.restrictScalars f).obj _) = 0 at hz
    rw [hz,mul_zero]
  additive h := by
    have ha := (T.torsionLength f ⊥).additive h ⟨1,by simp⟩
    change T.length ((ModuleCat.restrictScalars f).obj _) =
      T.length ((ModuleCat.restrictScalars f).obj _) +
        T.length ((ModuleCat.restrictScalars f).obj _) at ha
    rw [ha,mul_add]
  directSum_zero := by
    intro ι G _ _ hG
    have hz := T.restrictedLength_directSum_zero f G
      (fun i => (mul_eq_zero.mp (hG i)).resolve_left hr)
    rw [hz,mul_zero]
  iSup_zero := by
    intro ι M _ _ U hU
    have hz := T.restrictedLength_iSup_zero f U
      (fun i => (mul_eq_zero.mp (hU i)).resolve_left hr)
    rw [hz,mul_zero]
  directLimit_zero := by
    intro ι _ _ _ G _ _ g hG
    have hz := T.restrictedLength_directLimit_zero f G g
      (fun i => (mul_eq_zero.mp (hG i)).resolve_left hr)
    rw [hz,mul_zero]
end Lech.NormalizedLength.Tower


namespace Lech.CharP
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

 
def parameterIdeal {h : ℕ} (z : Fin h → D) (a : ℕ) : Ideal D :=
  Ideal.span (Set.range fun j => z j^a)

 

theorem exists_length (hh : 0 < Lech.dimension D) :
    ∃ ell : Lech.AllModuleLength (PerfectClosure D p),
      (∀ (H : Ideal D), H.radical = maximalIdeal D →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
          atTop (𝓝 (ell.value (ModuleCat.of (PerfectClosure D p)
            ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))))) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
        ∀ a : ℕ, 0 < a →
          ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
            (parameterIdeal D z a).map (PerfectClosure.of D p))) =
              (a : ℝ≥0∞)^(Lech.dimension D) *
                ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) ∧
      (∀ (ys : List D), ys.length = Lech.dimension D →
        (entryIdeal ys).radical = maximalIdeal D → ∀ i : ℤ, i < 0 →
          ell.value ((unit (ys.map (PerfectClosure.of D p))).homology i) = 0) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
          0 < Lech.Primary.multiplicity (Ideal.span (Set.range z))) := by
  obtain ⟨h,ψ,hψ,hfin,hloc,hres,hd⟩ :=
    Lech.Normalization.exists_finite_powerSeries_normalization D p
  have hdim : Lech.dimension D = h := by
    have hd' := Lech.dimension_cast D
    rw [hd] at hd'
    exact_mod_cast hd'
  let k := ResidueField D
  let : CharP k p := CharP.of_ringHom_of_ne_zero (residue D) p
    (Nat.Prime.ne_zero Fact.out)
  let A := MvPowerSeries (Fin h) k
  let C := PerfectClosure D p
  let P := PerfectClosure A p
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := hfin
  let : IsLocalHom (algebraMap A D) := hloc
  have hf : Function.Injective (algebraMap A D) := hψ
  have hres' : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hres b
    refine ⟨residue A a,?_⟩
    rw [ResidueField.algebraMap_residue]
    exact ha
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hf
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := Module.Finite.of_isLocalization A D A⁰
  obtain ⟨r,hr,hlim⟩ :=
    Lech.SeparableOrder.exists_normalization_frobenius_limit h k D p K L hf hres'
  let ell := (regularTower (Fin h) k p).allModuleLength (algebraMap P C) r
    (by exact_mod_cast (Nat.ne_of_gt hr))
  let φ := Lech.CoefficientField.localSection D p
  have hφ : Function.Surjective ((residue D).comp φ) :=
    fun a => ⟨a,Lech.CoefficientField.localSection_rightInverse D p a⟩
  refine ⟨ell,?_,?_,?_,?_⟩
  · intro H hH
    rw [hdim]
    exact hlim H hH
  · intro z hz a ha
    have hprim : (parameterIdeal D z a).radical = maximalIdeal D :=
      (Lech.Normalization.radical_span_powers z a (Nat.ne_of_gt ha)).trans hz
    have ht := hlim (parameterIdeal D z a) hprim
    have hp := Lech.Normalization.parameter_frobenius_multiplicity_enn
      (Lech.dimension D) hh rfl φ hφ z hz a ha p
    have hp' : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (D ⧸ (parameterIdeal D z a).map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 ((a : ℝ≥0∞)^(Lech.dimension D) *
          ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
      convert hp using 1
      ext n
      apply congrArg (fun b : ℝ≥0∞ => b *
        (Module.length D (D ⧸ (parameterIdeal D z a).map (iterateFrobenius D p n))).toENNReal)
      rw [hdim]
    exact tendsto_nhds_unique ht hp'
  · intro ys hlen hys i hi
    have hz := Lech.SeparableOrder.normalizedLength_parameter_koszul
      h k D p K L ys (hlen.trans hdim) hys i hi
    change (r : ℝ≥0∞) * _ = 0
    change (regularTower (Fin h) k p).length _ = 0 at hz
    rw [hz,mul_zero]
  · intro z hz
    exact Lech.Normalization.parameter_multiplicity_pos
      (Lech.dimension D) hh rfl φ hφ z hz
end Lech.CharP


namespace Lech.HilbertKunz
open Filter
open scoped Topology
variable (D : Type*) [CommRing D] [IsLocalRing D] (p : ℕ) [ExpChar D p]
 
noncomputable def normalizedColength (H : Ideal D) (n : ℕ) : ℝ :=
  ((Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toNat : ℝ) /
    (p : ℝ)^(n*Lech.dimension D)
 
noncomputable def multiplicity (H : Ideal D) : ℝ :=
  limUnder atTop (normalizedColength D p H)
end Lech.HilbertKunz


namespace Lech.CharP
open Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

omit [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] [PerfectRing (ResidueField D) p] in
lemma frobeniusIdeal_radical (H : Ideal D) (n : ℕ) :
    (H.map (iterateFrobenius D p n)).radical = H.radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change x^(p^n) ∈ H
    exact H.pow_mem_of_mem hx _ (pow_pos (Nat.Prime.pos Fact.out) n)
  · apply Ideal.radical_le_radical_iff.mpr
    intro x hx
    exact ⟨p^n,Ideal.mem_map_of_mem (iterateFrobenius D p n) hx⟩

omit [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] in
lemma entryIdeal_ofFn {h : ℕ} (z : Fin h → D) :
    entryIdeal (List.ofFn z) = Ideal.span (Set.range z) := by
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_ofPred_eq,List.mem_ofFn,Set.mem_range]

omit [IsDomain D] [IsAdicComplete (maximalIdeal D) D]
  [PerfectRing (ResidueField D) p] in
lemma quotient_finite_of_parameters
    (ell : Lech.AllModuleLength (PerfectClosure D p))
    (hparam : ∀ (z : Fin (Lech.dimension D) → D),
      (Ideal.span (Set.range z)).radical = maximalIdeal D → ∀ a : ℕ, 0 < a →
        ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
          (parameterIdeal D z a).map (PerfectClosure.of D p))) =
            (a : ℝ≥0∞)^(Lech.dimension D) *
              ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z))))
    (H : Ideal D) (hH : H.radical = maximalIdeal D) :
    ell.value (ModuleCat.of (PerfectClosure D p)
      ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p))) ≠ ⊤ := by
  obtain ⟨h,z,_hz,hzprim,hd⟩ := Lech.Normalization.exists_parameters D
  have hdim : Lech.dimension D = h := by
    have h := Lech.dimension_cast D
    rw [hd] at h
    exact_mod_cast h
  subst h
  let Q := Ideal.span (Set.range z)
  have hQH : Q ≤ H.radical := by rw [hH,← hzprim]; exact Ideal.le_radical
  obtain ⟨b,hb⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hQH
    (IsNoetherian.noetherian Q)
  have hpow : parameterIdeal D z (b+1) ≤ H := by
    apply le_trans (b := Q^(b+1))
    · apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) (b+1)
    · exact (Ideal.pow_le_pow_right (Nat.le_succ b)).trans hb
  have hle := ell.quotient_mono _ _ (Ideal.map_mono (f := PerfectClosure.of D p) hpow)
  rw [hparam z hzprim (b+1) (Nat.succ_pos b)] at hle
  exact ne_top_of_le_ne_top (by finiteness) hle

omit [IsDomain D] [IsAdicComplete (maximalIdeal D) D]
  [PerfectRing (ResidueField D) p] in
lemma hilbertKunz_limit_of_length (ell : Lech.AllModuleLength (PerfectClosure D p))
    (H : Ideal D) (hH : H.radical = maximalIdeal D)
    (hfinite : ell.value (ModuleCat.of (PerfectClosure D p)
      ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p))) ≠ ⊤)
    (ht : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 (ell.value (ModuleCat.of (PerfectClosure D p)
          ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))))) :
    Tendsto (Lech.HilbertKunz.normalizedColength D p H) atTop
      (𝓝 ((ell.value (ModuleCat.of (PerfectClosure D p)
        ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))).toReal)) := by
  have hh := (ENNReal.tendsto_toReal hfinite).comp ht
  apply hh.congr
  intro n
  have hf := Lech.Primary.length_ne_top (H.map (iterateFrobenius D p n))
    ((frobeniusIdeal_radical H n).trans hH) 1
  rw [pow_one] at hf
  dsimp only [Function.comp_def,Lech.HilbertKunz.normalizedColength]
  rw [← ENat.natCast_toNat hf]
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_pow,div_eq_mul_inv,mul_comm]

 

theorem length_inputs (hh : 0 < Lech.dimension D) :
    ∃ ell : Lech.AllModuleLength (PerfectClosure D p),
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
        ∀ a : ℕ, 0 < a →
          ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
            (parameterIdeal D z a).map (PerfectClosure.of D p))) =
              (a : ℝ≥0∞)^(Lech.dimension D) *
                ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
        ∀ a : ℕ, 0 < a → ∀ i : ℤ, i < 0 →
          ell.value ((unit ((List.ofFn (fun j => z j^a)).map
            (PerfectClosure.of D p))).homology i) = 0) ∧
      (∀ (H : Ideal D), H.radical = maximalIdeal D →
        Tendsto (Lech.HilbertKunz.normalizedColength D p H) atTop
          (𝓝 (Lech.HilbertKunz.multiplicity D p H)) ∧
        ell.value (ModuleCat.of (PerfectClosure D p)
          ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p))) =
            ENNReal.ofReal (Lech.HilbertKunz.multiplicity D p H)) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
          0 < Lech.Primary.multiplicity (Ideal.span (Set.range z))) := by
  obtain ⟨ell,hlim,hparam,hkos,hpos⟩ := exists_length D p hh
  refine ⟨ell,hparam,?_,?_,hpos⟩
  · intro z hz a ha i hi
    apply hkos _ (by simp) _ i hi
    rw [entryIdeal_ofFn]
    exact (Lech.Normalization.radical_span_powers z a (Nat.ne_of_gt ha)).trans hz
  · intro H hH
    have hf := quotient_finite_of_parameters ell hparam H hH
    have ht := hilbertKunz_limit_of_length ell H hH hf (hlim H hH)
    have he : Lech.HilbertKunz.multiplicity D p H = _ := ht.limUnder_eq
    refine ⟨?_,?_⟩
    · rwa [he]
    · rw [he,ENNReal.ofReal_toReal hf]
end Lech.CharP
end
end

end OAI
