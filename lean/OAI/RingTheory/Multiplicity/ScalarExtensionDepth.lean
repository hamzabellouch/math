import Mathlib
import OAI.RingTheory.Multiplicity.DuttaFrobeniusShift
import OAI.RingTheory.Multiplicity.LocalContractibility

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma extendScalars_range_le (φ : R →+* S) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (I : Ideal R) (J : Ideal S)
    (hf : f.hom.range ≤ I • (⊤ : Submodule R N)) (hI : I.map φ ≤ J) :
    ((ModuleCat.extendScalars φ).map f).hom.range ≤
      J • (⊤ : Submodule S ((ModuleCat.extendScalars φ).obj N)) := by
  let := φ.toAlgebra
  let P : Submodule S (S ⊗[R] N) := J • ⊤
  have hgen (x : N) (hx : x ∈ I • (⊤ : Submodule R N)) : (1:S) ⊗ₜ[R] x ∈ P := by
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      rw [TensorProduct.tmul_smul]
      change φ r • ((1:S) ⊗ₜ[R] y) ∈ P
      exact Submodule.smul_mem_smul (hI (Ideal.mem_map_of_mem φ hr)) Submodule.mem_top
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact P.add_mem hx hy
  change (f.hom.baseChange S).range ≤ P
  rintro _ ⟨x,rfl⟩
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change s ⊗ₜ[R] f m ∈ P
    have hh := P.smul_mem s (hgen (f m) (hf (LinearMap.mem_range_self f.hom m)))
    simpa only [TensorProduct.smul_tmul',smul_eq_mul,mul_one] using hh
  | add x y hx hy =>
    rw [map_add]
    exact P.add_mem hx hy

lemma frobenius_minimal_depth [IsLocalRing R] [IsNoetherianRing R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hm : IsMinimalComplex F) (n : ℕ) :
    ∀ i : ℤ,((frobeniusComplex R p n F).d i (i+1)).hom.range ≤
      (IsLocalRing.maximalIdeal R)^(p^n) •
        (⊤ : Submodule R ((frobeniusComplex R p n F).X (i+1))) := by
  intro i
  apply extendScalars_range_le (iterateFrobenius R p n) (F.d i (i+1)) _ _ (hm i)
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change r^(p^n) ∈ (IsLocalRing.maximalIdeal R)^(p^n)
  exact Ideal.pow_mem_pow hr _

lemma acyclic_of_unit_nullhomotopy (F : CochainComplex (ModuleCat.{u} S) ℤ)
    (x : S) (hx : IsUnit x) (H : Homotopy (x • 𝟙 F) 0) : F.Acyclic := by
  obtain ⟨u,rfl⟩ := hx
  apply acyclic_of_contractible F
  simpa only [smul_smul,Units.inv_mul,one_smul,smul_zero] using H.smul (↑(u⁻¹):S)

lemma baseChange_map_smul [Algebra R S] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : R) :
    (baseChangeFunctor R S).map (x • f) =
      algebraMap R S x • (baseChangeFunctor R S).map f := by
  apply ModuleCat.hom_ext
  change (x • f.hom).baseChange S = algebraMap R S x • f.hom.baseChange S
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext
  ext s m
  change s ⊗ₜ[R] (x • f m) = algebraMap R S x • (s ⊗ₜ[R] f m)
  rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul',Algebra.smul_def]
  rfl

def baseChange_nullhomotopy [Algebra R S]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (x : R)
    (H : Homotopy (x • 𝟙 F) 0) :
    Homotopy (algebraMap R S x • 𝟙 (((baseChangeFunctor R S).mapHomologicalComplex _).obj F)) 0 := by
  have H' := (baseChangeFunctor R S).mapHomotopy H
  have he : ((baseChangeFunctor R S).mapHomologicalComplex (.up ℤ)).map (x • 𝟙 F) =
      algebraMap R S x • 𝟙 (((baseChangeFunctor R S).mapHomologicalComplex _).obj F) := by
    ext i : 1
    change (baseChangeFunctor R S).map (x • 𝟙 (F.X i)) =
      algebraMap R S x • 𝟙 ((baseChangeFunctor R S).obj (F.X i))
    rw [baseChange_map_smul,CategoryTheory.Functor.map_id]
  rw [he,Functor.map_zero] at H'
  exact H'

lemma short_extension_acyclicAway [IsLocalRing R] [IsNoetherianRing R]
    (φ : R →+* S) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    (((baseChangeFunctor S (Localization.Away (φ x))).mapHomologicalComplex _).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj F)).Acyclic := by
  let G := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F
  let A := Localization.Away (φ x)
  let f := algebraMap S A
  obtain ⟨a,ha⟩ := shortComplex_nullScalar_radical F hF hx
  have H := baseChange_nullhomotopy (S:=A) G (φ (x^a))
    (extendScalars_nullhomotopy φ F (x^a) ha.some)
  apply acyclic_of_unit_nullhomotopy _ (f (φ (x^a))) _ H
  rw [map_pow,map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (φ x)).pow a
end Lech

end

end OAI
