import Mathlib
import OAI.RingTheory.Multiplicity.LechSignedUnit
import OAI.RingTheory.Multiplicity.RootUlrichModule

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.RootInvariants
open Polynomial UniversalSplitting
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance homogeneousCoordinatesAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance homogeneousCoordinatesTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat A B]
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
  (σ : Fin n → Bool) (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)

lemma commonBasis_value_apply (ms : Fin n → ℤ) (r : C) :
    commonValue f n hn t v hv d C ms (commonBasis f n hn t v hv d C σ φ ms r)=
      algebraMap C (commonExtension f n hn t v hv d C) r *
        (commonWeight f n hn t v hv d C σ φ ms : commonExtension f n hn t v hv d C) := by
  have hh : commonBasis f n hn t v hv d C σ φ ms r=
      r • commonBasis f n hn t v hv d C σ φ ms 1 := by
    simpa only [smul_eq_mul,mul_one] using (commonBasis f n hn t v hv d C σ φ ms).map_smul r 1
  rw [hh,map_smul,commonBasis_value]
  exact Algebra.smul_def (R := C) (A := commonExtension f n hn t v hv d C) _ _

 

lemma commonBasis_homogeneous (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    (commonBasis f n hn t v hv d C σ φ (fun i => (m i:ℤ))).symm
      (1 ⊗ₜ[algebra f n hn t v hv d]
        ((overAlgebraEquiv f n hn t v hv d _).symm (homogeneousSection f n hn t v hv d m e he))) =
      ∏ i,φ (chartCoordinate f n hn t v hv d σ i true)^(e i)*
        φ (chartCoordinate f n hn t v hv d σ i false)^(m i-e i) := by
  classical
  let := algebra_faithfullyFlat f n hn t v hv d
  have hinj : Function.Injective (algebraMap C (commonExtension f n hn t v hv d C)) :=
    FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C)
  apply hinj
  apply (commonWeight f n hn t v hv d C σ φ (fun i => (m i:ℤ))).mul_left_inj.mp
  rw [←commonBasis_value_apply,LinearEquiv.apply_symm_apply]
  change (1:C) ⊗ₜ[algebra f n hn t v hv d]
      (∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i)) = _
  let inc : d.S →ₐ[algebra f n hn t v hv d] commonExtension f n hn t v hv d C :=
    Algebra.TensorProduct.includeRight
  change inc (∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i)) = _
  rw [commonWeight_product f n hn t v hv d C σ φ (fun i => (m i:ℤ))]
  simp only [map_prod,map_mul,map_pow,Units.coe_prod,zpow_natCast,Units.val_pow_eq_pow_val]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hx := commonCoordinate_relation f n hn t v hv d C σ φ i true
  have hy := commonCoordinate_relation f n hn t v hv d C σ φ i false
  change algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i true))*
    (commonWeight f n hn t v hv d C σ φ (Pi.single i 1) : commonExtension f n hn t v hv d C)=inc (-d.roots i) at hx
  change algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i false))*
    (commonWeight f n hn t v hv d C σ φ (Pi.single i 1) : commonExtension f n hn t v hv d C)=
      inc (1+algebraMap B d.S t*d.roots i) at hy
  rw [←hx,←hy,mul_pow,mul_pow]
  conv_rhs => rhs; rw [←Nat.add_sub_of_le (he i),pow_add]
  ring
end Lech.RootInvariants

end

end OAI
