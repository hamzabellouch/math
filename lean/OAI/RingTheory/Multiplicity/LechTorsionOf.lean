import Mathlib
import OAI.RingTheory.Multiplicity.IdealGradedRing

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech
open CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
variable {R : Type u} [CommRing R]
lemma torsion_of_quotient_scalar (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    powerTorsion I (ModuleCat.of R M) := by
  refine ⟨1, ?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  intro m
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r m]
  change (Ideal.Quotient.mk I r) • m = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

namespace SourceGraded
variable (I : Ideal R) {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomialMap_smul (r : R ⧸ I) (a : MvPolynomial (Fin h) (R ⧸ I)) :
    IdealGraded.polynomialMap I z hz (r • a) =
      r • IdealGraded.polynomialMap I z hz a := by
  exact (aeval (IdealGraded.generator I z hz) :
    MvPolynomial (Fin h) (R ⧸ I) →ₐ[R ⧸ I] IdealGraded.Ring I).toLinearMap.map_smul r a

noncomputable def degreeMap (n : ℕ) :
    homogeneousSubmodule (Fin h) (R ⧸ I) n →ₗ[R ⧸ I] IdealGraded.grade I n :=
  Homogeneous.gradedMap (R := R ⧸ I) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (homogeneousSubmodule (Fin h) (R ⧸ I)) (IdealGraded.grade I)
    (IdealGraded.polynomialMap I z hz) (polynomialMap_smul I z hz) n

lemma degreeMap_surjective (n : ℕ) : Function.Surjective (degreeMap I z hz n) := by
  unfold degreeMap
  exact Homogeneous.gradedMap_surjective (R := R ⧸ I)
    (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I)
    (homogeneousSubmodule (Fin h) (R ⧸ I)) (IdealGraded.grade I)
    (IdealGraded.polynomialMap I z hz) (polynomialMap_smul I z hz)
    (IdealGraded.polynomialMap_surjective I z hz) n

variable (ell : TorsionLength I)
lemma polynomial_piece_value (h n : ℕ) :
    ell.value (ModuleCat.of R (homogeneousSubmodule (Fin h) (R ⧸ I) n)) =
      h.multichoose n • ell.value (ModuleCat.of R (R ⧸ I)) := by
  have ht := powerTorsion_pi_small (I := I) (M := R ⧸ I)
    (Grading.MonomialIndex h n) powerTorsion_quotient
  have e : homogeneousSubmodule (Fin h) (R ⧸ I) n ≃ₗ[R]
      (Grading.MonomialIndex h n → R ⧸ I) :=
    (Grading.homogeneousEquiv (R ⧸ I) h n).restrictScalars R
  have he := ell.value_linearEquiv (M := homogeneousSubmodule (Fin h) (R ⧸ I) n)
    (N := Grading.MonomialIndex h n → R ⧸ I) e ht
  exact he.trans ((ell.value_fintype_small powerTorsion_quotient
    (Grading.MonomialIndex h n)).trans (by rw [Grading.index_card]))

include hz in
lemma associated_piece_value
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R (IdealGraded.grade I n)) =
      h.multichoose n • ell.value (ModuleCat.of R (R ⧸ I)) := by
  have ht : powerTorsion I (ModuleCat.of R (IdealGraded.grade I n)) :=
    torsion_of_quotient_scalar I (IdealGraded.grade I n)
  have he := ell.value_linearEquiv (M := IdealGraded.Piece I n)
    (N := IdealGraded.grade I n) ((IdealGraded.pieceEquiv I n).restrictScalars R) ht
  rw [← he]
  subst I
  have hpiece := congrArg₂ (fun (P Q : Ideal R) =>
    ell.value (ModuleCat.of R (P ⧸ Submodule.comap P.subtype Q)))
    (sup_bot_eq (Ideal.span (Set.range z) ^ n))
    (sup_bot_eq (Ideal.span (Set.range z) ^ (n + 1)))
  exact hpiece.symm.trans (MonomialSpanning.ordinary_piece_value z ell hh hmu ha n)

local instance kernel_addCommGroup (n : ℕ) :
    AddCommGroup ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.addCommGroup (R := R)
    (M := homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker
local instance kernel_module (n : ℕ) :
    Module R ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.module (R := R)
    (M := homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker

include hz in
 

lemma degree_kernel_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R ((degreeMap I z hz n).restrictScalars R).ker) = 0 := by
  apply ell.kernel_zero_of_surjective_value_eq
    (M := homogeneousSubmodule (Fin h) (R ⧸ I) n) (N := IdealGraded.grade I n)
    ((degreeMap I z hz n).restrictScalars R)
    (degreeMap_surjective I z hz n) (torsion_of_quotient_scalar I _)
  · rw [associated_piece_value I z hz ell hh hmu ha n, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hmu
  · rw [polynomial_piece_value I ell h n, associated_piece_value I z hz ell hh hmu ha n]
end SourceGraded
end Lech

attribute [local instance] Classical.propDecidable
namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal DirectSum
universe u
 

structure AllModuleLength (C : Type u) [CommRing C] where
  value : ModuleCat.{u} C → ℝ≥0∞
  zero : ∀ {M}, IsZero M → value M = 0
  additive : ∀ {S : ShortComplex (ModuleCat.{u} C)}, S.ShortExact →
    value S.X₂ = value S.X₁ + value S.X₃
  directSum_zero : ∀ {ι : Type u} (G : ι → Type u) [∀ i, AddCommGroup (G i)]
    [∀ i, Module C (G i)],
    (∀ i, value (ModuleCat.of C (G i)) = 0) → value (ModuleCat.of C (⨁ i, G i)) = 0
  iSup_zero : ∀ {ι M : Type u} [AddCommGroup M] [Module C M]
    (U : ι → Submodule C M),
    (∀ i, value (ModuleCat.of C (U i)) = 0) →
      value (ModuleCat.of C (⨆ i, U i : Submodule C M)) = 0
  directLimit_zero : ∀ {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Module C (G i)]
    (g : ∀ i j, i ≤ j → G i →ₗ[C] G j),
    (∀ i, value (ModuleCat.of C (G i)) = 0) →
      value (ModuleCat.of C (Module.DirectLimit G g)) = 0

namespace AllModuleLength
variable {C : Type u} [CommRing C] (ell : AllModuleLength C)
 
def torsionLength (I : Ideal C) : TorsionLength I where
  value := ell.value
  zero := ell.zero
  additive h _ := ell.additive h

lemma quotient_mono (I J : Ideal C) (hIJ : I ≤ J) :
    ell.value (ModuleCat.of C (C ⧸ J)) ≤ ell.value (ModuleCat.of C (C ⧸ I)) := by
  let f := I.mapQ J LinearMap.id hIJ
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a,rfl⟩ := J.mkQ_surjective x
    exact ⟨I.mkQ a,rfl⟩
  let : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  exact (ell.torsionLength ⊥).le_of_epi (ModuleCat.ofHom f) ⟨1,by simp⟩
end AllModuleLength
end Lech


namespace Lech.AllModuleLength
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
universe u
variable {C : Type u} [CommRing C] (ell : AllModuleLength C)

lemma value_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] (e : M ≃ₗ[C] N) :
    ell.value (ModuleCat.of C M) = ell.value (ModuleCat.of C N) := by
  apply le_antisymm
  · have : Mono (ModuleCat.ofHom e.toLinearMap) := (ModuleCat.mono_iff_injective _).mpr e.injective
    exact (ell.torsionLength ⊥).le_of_mono (ModuleCat.ofHom e.toLinearMap) ⟨1,by simp⟩
  · have : Mono (ModuleCat.ofHom e.symm.toLinearMap) := (ModuleCat.mono_iff_injective _).mpr e.symm.injective
    exact (ell.torsionLength ⊥).le_of_mono (ModuleCat.ofHom e.symm.toLinearMap) ⟨1,by simp⟩

lemma zero_of_surjective {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] (f : M →ₗ[C] N) (hf : Function.Surjective f)
    (hM : ell.value (ModuleCat.of C M) = 0) : ell.value (ModuleCat.of C N) = 0 := by
  have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  exact le_antisymm (hM ▸ (ell.torsionLength ⊥).le_of_epi (ModuleCat.ofHom f) ⟨1,by simp⟩) bot_le

lemma zero_of_injective {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] (f : M →ₗ[C] N) (hf : Function.Injective f)
    (hN : ell.value (ModuleCat.of C N) = 0) : ell.value (ModuleCat.of C M) = 0 := by
  have : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
  exact le_antisymm (hN ▸ (ell.torsionLength ⊥).le_of_mono (ModuleCat.ofHom f) ⟨1,by simp⟩) bot_le

lemma zero_of_ranges {ι M : Type u} [AddCommGroup M] [Module C M]
    {N : ι → Type u} [∀ i, AddCommGroup (N i)] [∀ i, Module C (N i)]
    (f : ∀ i, N i →ₗ[C] M) (hN : ∀ i, ell.value (ModuleCat.of C (N i))=0)
    (hspan : (⨆ i, (f i).range) = ⊤) : ell.value (ModuleCat.of C M)=0 := by
  have hz := ell.iSup_zero (fun i => (f i).range)
    (fun i => ell.zero_of_surjective (f i).rangeRestrict (f i).surjective_rangeRestrict (hN i))
  rw [hspan] at hz
  rw [ell.value_eq_of_linearEquiv (Submodule.topEquiv : (⊤ : Submodule C M) ≃ₗ[C] M)] at hz
  exact hz

lemma zero_of_decomposition {ι M : Type u} [DecidableEq ι] [AddCommGroup M] [Module C M]
    (G : ι → Submodule C M) [DirectSum.Decomposition G]
    (hG : ∀ i, ell.value (ModuleCat.of C (G i))=0) : ell.value (ModuleCat.of C M)=0 := by
  rw [ell.value_eq_of_linearEquiv (DirectSum.decomposeLinearEquiv G)]
  exact ell.directSum_zero (fun i => G i) hG

variable {A M N : Type u} [CommRing A] [Algebra C A]
  [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower C A M]
  [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
 

lemma tensor_zero_right (hN : ell.value (ModuleCat.of C N)=0) :
    ell.value (ModuleCat.of C (M ⊗[A] N))=0 := by
  let f (m : M) : N →ₗ[C] M ⊗[A] N := (TensorProduct.mk A M N m).restrictScalars C
  apply ell.zero_of_ranges f (fun _ => hN)
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact (le_iSup (fun m => (f m).range) m) ⟨n,rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

lemma tensor_zero_left (hM : ell.value (ModuleCat.of C M)=0) :
    ell.value (ModuleCat.of C (M ⊗[A] N))=0 := by
  rw [ell.value_eq_of_linearEquiv ((TensorProduct.comm A M N).restrictScalars C)]
  exact ell.tensor_zero_right hM

variable {P : Type u} [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower C A P]
 

lemma localized_zero (S : Submonoid A) (f : N →ₗ[A] P) [IsLocalizedModule S f]
    (hN : ell.value (ModuleCat.of C N)=0) : ell.value (ModuleCat.of C P)=0 := by
  let g (s : S) : N →ₗ[C] P :=
    { toFun := fun n => IsLocalizedModule.mk' f n s
      map_add' := fun a b => IsLocalizedModule.mk'_add f a b s
      map_smul' := fun c a => IsLocalizedModule.mk'_smul f c a s }
  apply ell.zero_of_ranges g (fun _ => hN)
  apply top_unique
  intro x _
  obtain ⟨⟨n,s⟩,rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  exact (le_iSup (fun s => (g s).range) s) ⟨n,rfl⟩
end Lech.AllModuleLength


namespace Lech.Homogeneous
open HomogeneousLocalization CategoryTheory CategoryTheory.Limits
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra C B]
  (G : ℕ → Submodule C A) (H : ℕ → Submodule C B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : C) (a : A), g (r • a) = r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d) (ell : AllModuleLength C)
attribute [local instance] awayAddCommGroup
attribute [local irreducible] awayMap gradedMap kernelFraction
include hf in
 

lemma away_kernel_length_zero
    (hker : ∀ n, ell.value (ModuleCat.of C (gradedMap G H g hg n).ker)=0) :
    ell.value (ModuleCat.of C (awayMap G H g hg f).ker)=0 := by
  let P := (ell.torsionLength ⊥).zeroClass
  have hz : P (ModuleCat.of C (awayMap G H g hg f).ker) := by
    apply kernel_property G H g hg hf P
    · intro n
      exact ⟨⟨1,by simp⟩, hker n⟩
    · intro U hU
      refine ⟨⟨1,by simp⟩, ?_⟩
      have hz := ell.iSup_zero (fun n : ULift.{u} ℕ => U n.down)
        (fun n => (hU n.down).2)
      have he : (⨆ n : ULift.{u} ℕ, U n.down) = ⨆ n : ℕ, U n := by
        simp only [iSup_ulift]
      rw [he] at hz
      exact hz
  exact hz.2
end Lech.Homogeneous


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev sourceGrade (h n : ℕ) : Submodule R (MvPolynomial (Fin h) (R ⧸ I)) :=
  (homogeneousSubmodule (Fin h) (R ⧸ I) n).restrictScalars R
abbrev targetGrade (n : ℕ) : Submodule R (IdealGraded.Ring I) :=
  (IdealGraded.grade I n).restrictScalars R
instance source_graded (h : ℕ) : GradedAlgebra (sourceGrade I h) := inferInstanceAs
  (GradedAlgebra (fun n => (homogeneousSubmodule (Fin h) (R ⧸ I) n).restrictScalars R))
instance target_graded : GradedAlgebra (targetGrade I) := inferInstanceAs
  (GradedAlgebra (fun n => (IdealGraded.grade I n).restrictScalars R))

abbrev mapR : sourceGrade I h →+*ᵍ targetGrade I where
  toRingHom := (IdealGraded.polynomialMap I z hz).toRingHom
  map_mem := Graded.map_mem (IdealGraded.polynomialMap I z hz)

lemma mapR_smul (r : R) (a : MvPolynomial (Fin h) (R ⧸ I)) :
    mapR I z hz (r • a) = r • mapR I z hz a := by
  change IdealGraded.polynomialMap I z hz (r • a) =
    r • IdealGraded.polynomialMap I z hz a
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r a,
    ← IsScalarTower.algebraMap_smul (R ⧸ I) r (IdealGraded.polynomialMap I z hz a)]
  exact polynomialMap_smul I z hz _ _

lemma mapR_surjective : Function.Surjective (mapR I z hz) :=
  IdealGraded.polynomialMap_surjective I z hz

abbrev gradedMapR (n : ℕ) : sourceGrade I h n →ₗ[R] targetGrade I n :=
  Homogeneous.gradedMap (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) n

attribute [local instance] Homogeneous.awayAddCommGroup
def chartMapR (f : MvPolynomial (Fin h) (R ⧸ I)) :=
  Homogeneous.awayMap (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) f

local instance gradedKernelAdd (n : ℕ) : AddCommGroup (gradedMapR I z hz n).ker :=
  Submodule.addCommGroup (R := R) (M := sourceGrade I h n) (gradedMapR I z hz n).ker
local instance gradedKernelModule (n : ℕ) : Module R (gradedMapR I z hz n).ker :=
  Submodule.module (R := R) (M := sourceGrade I h n) (gradedMapR I z hz n).ker
variable (ell : AllModuleLength R)
attribute [local instance] kernel_addCommGroup kernel_module

include hz in
lemma mapR_degree_kernel_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R (gradedMapR I z hz n).ker)=0 := by
  let e : (gradedMapR I z hz n).ker ≃ₗ[R]
      ((degreeMap I z hz n).restrictScalars R).ker :=
    { toFun := fun x => ⟨⟨x.val.val, by simpa only [sourceGrade, Submodule.restrictScalars_mem] using x.val.property⟩, by
        apply Subtype.ext
        have hx := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
        change IdealGraded.polynomialMap I z hz x.val.val = 0 at hx ⊢
        exact hx⟩
      invFun := fun x => ⟨⟨x.val.val, by simpa only [sourceGrade, Submodule.restrictScalars_mem] using x.val.property⟩, by
        apply Subtype.ext
        have hx := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
        change IdealGraded.polynomialMap I z hz x.val.val = 0 at hx ⊢
        exact hx⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  have he := (ell.torsionLength ⊥).value_linearEquiv e ⟨1,by simp⟩
  exact he.trans (degree_kernel_zero I z hz (ell.torsionLength I) hh hmu ha n)

include hz in
 

lemma chart_kernel_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I)))
    {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f ∈ sourceGrade I h d) :
    ell.value (ModuleCat.of R (chartMapR I z hz f).ker)=0 := by
  unfold chartMapR
  apply Homogeneous.away_kernel_length_zero (C := R) (A := MvPolynomial (Fin h) (R ⧸ I))
      (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) hf ell
  intro n
  exact mapR_degree_kernel_zero I z hz ell hh hmu ha n

include hz in
lemma chart_surjective {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ}
    (hf : f ∈ sourceGrade I h d) : Function.Surjective (chartMapR I z hz f) := by
  unfold chartMapR
  apply Homogeneous.awayMap_surjective (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
      (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) hf
  exact mapR_surjective I z hz
end Lech.SourceGraded


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
 
def exponents : AddSubmonoid (Fin h → ℤ) where
  carrier := {e | ∀ i, i ∉ s → 0 ≤ e i}
  zero_mem' := by simp
  add_mem' := by
    intro e f he hf i hi
    exact add_nonneg (he i hi) (hf i hi)
abbrev Poly := AddMonoidAlgebra R (Fin h → ℕ)
abbrev Laurent := AddMonoidAlgebra R (exponents s)
def fromNat : (Fin h → ℕ) →+ exponents s where
  toFun a := ⟨fun i => (a i : ℤ),fun _ _ => Int.natCast_nonneg _⟩
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp
lemma fromNat_injective : Function.Injective (fromNat s) := by
  intro a b hab
  funext i
  exact Int.natCast_inj.mp (congrArg (fun e : exponents s => e.val i) hab)
def toLaurent : Poly R (h := h) →+* Laurent R s :=
  mapDomainRingHom R (fromNat s)
instance : Algebra (Poly R (h := h)) (Laurent R s) := (toLaurent R s).toAlgebra
@[simp] lemma algebraMap_single (a : Fin h → ℕ) (r : R) :
    algebraMap (Poly R (h := h)) (Laurent R s) (single a r) = single (fromNat s a) r := by
  exact mapDomain_single
lemma toLaurent_injective : Function.Injective (algebraMap (Poly R (h := h)) (Laurent R s)) :=
  mapDomain_injective (fromNat_injective s)
def indicator : Fin h → ℕ := fun i => if i ∈ s then 1 else 0
def denominator : Poly R (h := h) := single (indicator s) 1
def negativeIndicator : exponents s :=
  ⟨fun i => -(indicator s i : ℤ),by intro i hi; simp [indicator,hi]⟩
lemma indicator_add_negative : fromNat s (indicator s) + negativeIndicator s = 0 := by
  ext i
  simp [fromNat,negativeIndicator]
lemma denominator_unit : IsUnit (algebraMap (Poly R (h := h)) (Laurent R s) (denominator R s)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨single (negativeIndicator s) 1,?_⟩
  rw [denominator,algebraMap_single,single_mul_single,indicator_add_negative]
  simp only [mul_one]
  exact AddMonoidAlgebra.one_def.symm
 

lemma clear_exponent (e : exponents s) :
    ∃ (n : ℕ) (a : Fin h → ℕ), e + fromNat s (n • indicator s) = fromNat s a := by
  let n := Finset.univ.sup (fun i => (-e.val i).toNat)
  have hb (i : Fin h) : (-e.val i).toNat ≤ n := Finset.le_sup (f := fun i => (-e.val i).toNat) (Finset.mem_univ i)
  have hpos (i : Fin h) : 0 ≤ e.val i + (n : ℤ) * (indicator s i : ℤ) := by
    by_cases hi : i ∈ s
    · simp only [indicator,ite_eq_left hi,Nat.cast_one,mul_one]
      have := hb i
      omega
    · simpa only [indicator,ite_eq_right hi,Nat.cast_zero,mul_zero,add_zero] using e.property i hi
  refine ⟨n,fun i => (e.val i + (n : ℤ) * (indicator s i : ℤ)).toNat,?_⟩
  ext i
  change e.val i + ((n • indicator s) i : ℤ) =
    ((e.val i + (n : ℤ) * (indicator s i : ℤ)).toNat : ℤ)
  rw [Int.toNat_of_nonneg (hpos i)]
  simp [Pi.smul_apply]
lemma clear_single (e : exponents s) (r : R) : ∃ (n : ℕ) (a : Poly R (h := h)),
    single e r * algebraMap (Poly R (h := h)) (Laurent R s) ((denominator R s)^n) =
      algebraMap (Poly R (h := h)) (Laurent R s) a := by
  obtain ⟨n,a,ha⟩ := clear_exponent s e
  refine ⟨n,single a r,?_⟩
  rw [denominator,single_pow,one_pow,algebraMap_single,single_mul_single,ha,mul_one,
    algebraMap_single]
lemma clear_denominators (x : Laurent R s) : ∃ (n : ℕ) (a : Poly R (h := h)),
    x * algebraMap (Poly R (h := h)) (Laurent R s) ((denominator R s)^n) =
      algebraMap (Poly R (h := h)) (Laurent R s) a := by
  obtain ⟨f,rfl⟩ := coeffAddEquiv.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0,0,by simp⟩
  | single e r => exact clear_single R s e r
  | add f g hf hg =>
    obtain ⟨n,a,ha⟩ := hf
    obtain ⟨m,b,hb⟩ := hg
    change ofCoeff f * _ = _ at ha
    change ofCoeff g * _ = _ at hb
    refine ⟨n+m,a*(denominator R s)^m + b*(denominator R s)^n,?_⟩
    change (ofCoeff f + ofCoeff g) * _ = _
    rw [pow_add,map_mul,add_mul,map_add,map_mul,map_mul]
    calc
      _ = (ofCoeff f * algebraMap _ _ ((denominator R s)^n)) *
          algebraMap _ _ ((denominator R s)^m) +
          (ofCoeff g * algebraMap _ _ ((denominator R s)^m)) *
          algebraMap _ _ ((denominator R s)^n) := by ring
      _ = _ := by rw [ha,hb]
 

instance localization : IsLocalization.Away (denominator R s) (Laurent R s) := by
  apply (isLocalization_iff (Submonoid.powers (denominator R s)) (Laurent R s)).mpr
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,n,rfl⟩
    rw [map_pow]
    exact (denominator_unit R s).pow n
  · intro x
    obtain ⟨n,a,ha⟩ := clear_denominators R s x
    exact ⟨⟨a,⟨(denominator R s)^n,n,rfl⟩⟩,ha⟩
  · intro a b hab
    exact ⟨1,by simpa using toLaurent_injective R s hab⟩


def polynomialEquiv : MvPolynomial (Fin h) R ≃ₐ[R] Poly R (h := h) :=
  AddMonoidAlgebra.domCongr R R
    (Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin h)).toAddEquiv
@[simp] lemma polynomialEquiv_X (i : Fin h) :
    polynomialEquiv R (MvPolynomial.X i) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  change (AddMonoidAlgebra.domCongr R R _) (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.domCongr_single]
  congr 1
  ext j
  simp [Finsupp.single_apply,Pi.single_apply,eq_comm]
lemma polynomialEquiv_denominator :
    polynomialEquiv R (∏ i ∈ s, MvPolynomial.X i) = denominator R s := by
  classical
  rw [map_prod]
  simp_rw [polynomialEquiv_X]
  rw [AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one,denominator]
  congr 1
  ext i
  simp [indicator,Pi.single_apply]

def exponentInclusion {s t : Finset (Fin h)} (hst : s ⊆ t) : exponents s →+ exponents t where
  toFun e := ⟨e.val,fun i hi => e.property i (fun his => hi (hst his))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def restrict {s t : Finset (Fin h)} (hst : s ⊆ t) : Laurent R s →+* Laurent R t :=
  mapDomainRingHom R (exponentInclusion hst)
@[simp] lemma restrict_single {s t : Finset (Fin h)} (hst : s ⊆ t)
    (e : exponents s) (a : R) :
    restrict R hst (single e a) = single (exponentInclusion hst e) a := mapDomain_single
lemma restrict_injective {s t : Finset (Fin h)} (hst : s ⊆ t) :
    Function.Injective (restrict R hst) :=
  mapDomain_injective (fun _ _ he => Subtype.ext
    (congrArg (fun e : exponents t => e.val) he))
lemma restrict_comp {s t v : Finset (Fin h)} (hst : s ⊆ t) (htv : t ⊆ v) :
    (restrict R htv).comp (restrict R hst) = restrict R (hst.trans htv) := by
  apply RingHom.coe_addMonoidHom_injective
  apply AddMonoidAlgebra.addMonoidHom_ext
  intro e a
  change restrict R htv (restrict R hst (single e a)) = restrict R _ (single e a)
  rw [restrict_single,restrict_single,restrict_single]
  rfl
lemma restrict_algebraMap {s t : Finset (Fin h)} (hst : s ⊆ t) (a : Poly R (h := h)) :
    restrict R hst (algebraMap _ _ a) = algebraMap _ _ a := by
  have he : (restrict R hst).comp (algebraMap (Poly R (h := h)) (Laurent R s)) =
      algebraMap (Poly R (h := h)) (Laurent R t) := by
    apply RingHom.coe_addMonoidHom_injective
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro e c
    change restrict R hst (algebraMap _ _ (single e c)) = algebraMap _ _ (single e c)
    rw [algebraMap_single,restrict_single,algebraMap_single]
    rfl
  exact RingHom.congr_fun he a

def degree (e : exponents s) : ℤ := ∑ i, e.val i
 
def homogeneous (t : ℤ) : Submodule R (Laurent R s) :=
  (Finsupp.supported R R {e : exponents s | degree s e = t}).comap
    (coeffLinearEquiv R).toLinearMap

def homogeneousCoefficients (t : ℤ) :
    homogeneous R s t ≃ₗ[R] Finsupp.supported R R {e : exponents s | degree s e = t} where
  toFun a := ⟨(coeffLinearEquiv R) a.val,a.property⟩
  invFun a := ⟨(coeffLinearEquiv R).symm a.val,by
    unfold homogeneous
    apply Submodule.mem_comap.mpr
    simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using a.property⟩
  left_inv a := Subtype.ext (LinearEquiv.symm_apply_apply (coeffLinearEquiv R) a.val)
  right_inv a := Subtype.ext (LinearEquiv.apply_symm_apply (coeffLinearEquiv R) a.val)
  map_add' a b := Subtype.ext (map_add (coeffLinearEquiv R) a.val b.val)
  map_smul' r a := Subtype.ext (map_smul (coeffLinearEquiv R) r a.val)
 

def homogeneousEquiv (t : ℤ) : homogeneous R s t ≃ₗ[R]
    ({e : exponents s // degree s e = t} →₀ R) :=
  (homogeneousCoefficients R s t).trans (Finsupp.supportedEquivFinsupp _)
end Lech.PartialLaurent

end

end OAI
