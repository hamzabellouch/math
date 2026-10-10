import Mathlib
import OAI.RingTheory.Multiplicity.SignedCechBicRow
import OAI.RingTheory.Multiplicity.TorsionChartKernel

namespace OAI

noncomputable section
namespace Lech.TwistedLocalization
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)

include hf in
lemma piece_torsion (I : Ideal R) (hT : powerTorsion I (ModuleCat.of R A)) (t : ℕ) :
    powerTorsion I (ModuleCat.of R (piece G (f:=f) (d:=d) t)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  obtain ⟨n,b,hb⟩ := exists_fraction G hf t x
  change r • (x : Localization.Away f)=0
  rw [←hb,←map_smul]
  have hz : r • b=0 := Subtype.ext (Module.mem_annihilator.mp (ha hr) b)
  rw [hz,map_zero]

variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
  (I : Ideal R) (ell : TorsionLength I)
def gradedKernelEquiv (n : ℕ) :
    (gradedMap G H g hg n).ker ≃ₗ[R] (Homogeneous.gradedMap G H g hg n).ker where
  toFun x := ⟨x.val,by exact x.property⟩
  invFun x := ⟨x.val,by exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

attribute [local instance] kernelAdd kernelModule
attribute [local irreducible] pieceMap gradedMap kernelFraction
omit [GradedAlgebra H] in
include hf in
lemma kernel_zeroClass (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R A))
    (hker : ∀ n,ell.value (ModuleCat.of R (Homogeneous.gradedMap G H g hg n).ker)=0) (t : ℕ) :
    ell.zeroClass (ModuleCat.of R (pieceMap G hf H g hg t).ker) := by
  have htK : powerTorsion I (ModuleCat.of R (pieceMap G hf H g hg t).ker) :=
    powerTorsion_submodule I _ (piece_torsion G hf I hT t)
  apply kernel_property G hf H g hg t ell.zeroClass
  · intro n
    exact ell.zeroClass.prop_of_iso (gradedKernelEquiv G H g hg n).symm.toModuleIso
      ⟨powerTorsion_submodule I _ (powerTorsion_submodule I (G n) hT),hker n⟩
  · intro U hU
    refine ⟨powerTorsion_submodule I _ htK,?_⟩
    have hh := ell.iSup_zero_torsion hds (fun n : ULift.{u} ℕ => U n.down) htK
      (fun n => (hU n.down).2)
    have he : (⨆ n : ULift.{u} ℕ,U n.down) = ⨆ n : ℕ,U n := by
      simp only [iSup_ulift]
    rw [he] at hh
    exact hh
end Lech.TwistedLocalization

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
  (hds : ell.DirectSumZero) (hh : 0<h)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
      a^h • ell.value (ModuleCat.of R (R ⧸ I)))
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap
  TwistedLocalization.gradedMap ImageCech.mapTerm IdealGraded.polynomialMap

include hz hds hh hmu ha in
lemma twist_kernel_zeroClass
    {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f∈sourceGrade I h d) (t : ℕ) :
    ell.zeroClass (ModuleCat.of R (twistMapR I z hz hf t).ker) := by
  unfold twistMapR
  apply TwistedLocalization.kernel_zeroClass _ hf _ _ _ I ell hds
    (torsion_of_quotient_scalar I (MvPolynomial (Fin h) (R ⧸ I)))
  exact mapR_degree_kernel_zero_torsion I z hz ell hh hmu ha

include hz hds hh hmu ha in
lemma exceptionalCech_homology_zeroClass (t n : ℕ) :
    ell.zeroClass ((exceptionalCech I z hz t).homology n) := by
  apply RestrictedPolynomialImageCech.homology_mem (R:=R) (S:=R ⧸ I) (B:=IdealGraded.Ring I)
    (targetGrade I) (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz) ell.zeroClass t _ hh n
  intro s
  unfold ImageCech.mapTerm
  exact twist_kernel_zeroClass I z hz ell hds hh hmu ha
    (GradedChart.denominator_mem (sourceGrade I h) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X (R ⧸ I)) s) t

include hds hh hmu ha in
lemma finiteThickening_homology_zeroClass (t M n : ℕ) :
    ell.zeroClass ((finiteThickening I z hz t M).homology n) := by
  induction M with
  | zero =>
      have hi : Epi (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t 0)) := by
        simpa only [FilteredCech.inclusion_refl] using
          (inferInstance : Epi (𝟙 (FilteredCech.complex I z (coordinate_mem I z hz) t)))
      unfold finiteThickening
      exact ell.zeroClass.prop_of_isZero
        ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map_isZero
          (isZero_cokernel_of_epi (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t 0))))
  | succ M ih =>
      have hl := cokernel_homology_property_of_shortExact ell.zeroClass
        (filteredLayerSequence_shortExact I z hz (t+M)) n
        (exceptionalCech_homology_zeroClass I z hz ell hds hh hmu ha (t+M) n)
      have hc := cokernel_comp_homology_property ell.zeroClass
        (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ (t+M)))
        (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t M)) n hl ih
      rw [FilteredCech.inclusion_comp] at hc
      exact hc

variable [Nontrivial R]
include hds hh hmu ha in
lemma finiteThickening_totalTensor_zeroClass (t M : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j,Module.Free R (F.X j)) (hfinite : ∀ j,Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (i : ℤ) :
    ell.zeroClass (((TensorTotal.functor
      ((finiteThickening I z hz t M).extend ComplexShape.embeddingUpNat)).obj F).homology i) := by
  have hK := homology_property_extendUpNat ell.zeroClass (finiteThickening I z hz t M)
    (finiteThickening_homology_zeroClass I z hz ell hds hh hmu ha t M)
  exact TensorTotal.homology_property_of_bounded_free _ ell.zeroClass hK F hfree hfinite m N hb i

include hds hh hmu ha in
lemma thickeningComparison_isoModSerre_torsion
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j,Module.Free R (F.X j)) (hfinite : ∀ j,Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (M : ℕ) (i : ℤ) :
    ell.zeroClass.isoModSerre (thickeningComparison I z hz F M i) := by
  apply ell.zeroClass.isoModSerre.comp_mem
  · exact ell.zeroClass.isoModSerre_of_isIso
      ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
        (thickeningTensorBottomIso I z hz F M)).inv
  · apply TensorTotal.bottomComparison_isoModSerre
    intro j
    exact finiteThickening_totalTensor_zeroClass I z hz ell hds hh hmu ha 0 M F hfree hfinite m N hb j
end Lech.SourceGraded

end

end OAI
