import Mathlib
import OAI.RingTheory.Multiplicity.LechTorsionOf
import OAI.RingTheory.Multiplicity.TorsionZeroStability

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
lemma powerTorsion_submodule {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hT : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R N) := by
  obtain ⟨a,ha⟩ := hT
  exact ⟨a,ha.trans (N.subtype.annihilator_le_of_injective N.injective_subtype)⟩
end Lech

namespace Lech.Homogeneous
open HomogeneousLocalization CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
attribute [local instance] awayAddCommGroup

lemma away_torsion (I : Ideal R) {f : A} {d : ℕ} (hf : f ∈ G d)
    (hT : powerTorsion I (ModuleCat.of R A)) :
    powerTorsion I (ModuleCat.of R (Away G f)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective G hf x
  let c : G (j*d) := ⟨b,by simpa only [nsmul_eq_mul,Nat.cast_id] using hb⟩
  change r • fraction G hf j c=0
  rw [←map_smul]
  have hc : r • c=0 := Subtype.ext (Module.mem_annihilator.mp (ha hr) b)
  rw [hc,map_zero]

variable (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d) (I : Ideal R) (ell : TorsionLength I)
attribute [local irreducible] awayMap gradedMap kernelFraction
include hf in
lemma away_kernel_zero_torsion (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R A))
    (hker : ∀ n,ell.value (ModuleCat.of R (gradedMap G H g hg n).ker)=0) :
    ell.value (ModuleCat.of R (awayMap G H g hg f).ker)=0 := by
  have htK : powerTorsion I (ModuleCat.of R (awayMap G H g hg f).ker) :=
    powerTorsion_submodule I _ (away_torsion G I hf hT)
  have hz : ell.zeroClass (ModuleCat.of R (awayMap G H g hg f).ker) := by
    apply kernel_property G H g hg hf ell.zeroClass
    · intro n
      exact ⟨powerTorsion_submodule I _ (powerTorsion_submodule I (G n) hT),hker n⟩
    · intro U hU
      refine ⟨powerTorsion_submodule I _ htK,?_⟩
      have hh := ell.iSup_zero_torsion hds (fun n : ULift.{u} ℕ => U n.down) htK
        (fun n => (hU n.down).2)
      have he : (⨆ n : ULift.{u} ℕ,U n.down) = ⨆ n : ℕ,U n := by
        simp only [iSup_ulift]
      rw [he] at hh
      exact hh
  exact hz.2
end Lech.Homogeneous

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

private local instance torsionGradedKernelAdd (n : ℕ) : AddCommGroup (gradedMapR I z hz n).ker :=
  Submodule.addCommGroup (R:=R) (M:=sourceGrade I h n) (gradedMapR I z hz n).ker
private local instance torsionGradedKernelModule (n : ℕ) : Module R (gradedMapR I z hz n).ker :=
  Submodule.module (R:=R) (M:=sourceGrade I h n) (gradedMapR I z hz n).ker
private local instance degreeKernelAdd (n : ℕ) : AddCommGroup ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.addCommGroup (R:=R) (M:=homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker
private local instance degreeKernelModule (n : ℕ) : Module R ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.module (R:=R) (M:=homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker

include hz in
lemma mapR_degree_kernel_zero_torsion
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^h • ell.value (ModuleCat.of R (R ⧸ I))) (n : ℕ) :
    ell.value (ModuleCat.of R (gradedMapR I z hz n).ker)=0 := by
  let e : (gradedMapR I z hz n).ker ≃ₗ[R]
      ((degreeMap I z hz n).restrictScalars R).ker :=
    { toFun := fun x => ⟨⟨x.val.val,by simpa only [sourceGrade,Submodule.restrictScalars_mem] using x.val.property⟩,by
        apply Subtype.ext
        have hx := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
        change IdealGraded.polynomialMap I z hz x.val.val=0 at hx ⊢
        exact hx⟩
      invFun := fun x => ⟨⟨x.val.val,by simpa only [sourceGrade,Submodule.restrictScalars_mem] using x.val.property⟩,by
        apply Subtype.ext
        have hx := congrArg Subtype.val (LinearMap.mem_ker.mp x.property)
        change IdealGraded.polynomialMap I z hz x.val.val=0 at hx ⊢
        exact hx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT := powerTorsion_submodule I ((degreeMap I z hz n).restrictScalars R).ker
    (torsion_of_quotient_scalar I (homogeneousSubmodule (Fin h) (R ⧸ I) n))
  exact (ell.value_linearEquiv e hT).trans (degree_kernel_zero I z hz ell hh hmu ha n)

lemma chart_kernel_zero_torsion (hds : ell.DirectSumZero)
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f ∈ sourceGrade I h d) :
    ell.value (ModuleCat.of R (chartMapR I z hz f).ker)=0 := by
  unfold chartMapR
  apply Homogeneous.away_kernel_zero_torsion (R:=R) (A:=MvPolynomial (Fin h) (R ⧸ I))
    (B:=IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) hf I ell hds
    (torsion_of_quotient_scalar I (MvPolynomial (Fin h) (R ⧸ I)))
  exact mapR_degree_kernel_zero_torsion I z hz ell hh hmu ha

end Lech.SourceGraded

end

end OAI
