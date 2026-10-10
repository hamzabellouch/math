import Mathlib
import OAI.RingTheory.Multiplicity.RootUlrichSpan

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ModuleDescent
universe u v w w' z
variable {A : Type u} {B : Type v} {M : Type w} {L : Type w'} {ι : Type z}
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
  [AddCommGroup L] [Module B L] [Module.FaithfullyFlat A B]

lemma exists_basis_of_baseChange (g : ι → M) (E : B ⊗[A] M ≃ₗ[B] L)
    (b : Module.Basis ι B L) (hb : ∀ i,E (1 ⊗ₜ[A] g i)=b i) :
    ∃ c : Module.Basis ι A M, ∀ i,c i=g i := by
  classical
  let q := Finsupp.linearCombination A g
  let b₀ : Module.Basis ι A (ι →₀ A) := Finsupp.basisSingleOne
  have he : E.toLinearMap.comp (q.baseChange B)=
      ((b₀.baseChange B).equiv b (Equiv.refl ι)).toLinearMap := by
    apply (b₀.baseChange B).ext
    intro i
    change E ((q.baseChange B) ((b₀.baseChange B) i))=
      ((b₀.baseChange B).equiv b (Equiv.refl ι)) ((b₀.baseChange B) i)
    rw [Module.Basis.equiv_apply,Module.Basis.baseChange_apply,LinearMap.baseChange_tmul]
    simpa [q,b₀] using hb i
  have hqB : Function.Bijective (q.baseChange B) := by
    have hh' : Function.Bijective (E.toLinearMap.comp (q.baseChange B)) := by
      rw [he]
      exact ((b₀.baseChange B).equiv b (Equiv.refl ι)).bijective
    exact (Function.Bijective.of_comp_iff' E.bijective (q.baseChange B)).mp hh'
  have hq : Function.Bijective q :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B q).mp hqB
  let c : Module.Basis ι A M := Module.Basis.ofRepr (LinearEquiv.ofBijective q hq).symm
  refine ⟨c,fun i => ?_⟩
  change q (Finsupp.single i 1)=g i
  simp [q]
end Lech.ModuleDescent

namespace Lech.RootInvariants
open Polynomial UniversalSplitting
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance rootUlrichModuleAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance rootUlrichModuleIsScalarTower : IsScalarTower A B d.S :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma homogeneous_product_member (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    (∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i)) ∈
      module f n hn t v hv d (fun i => (m i:ℤ)) := by
  classical
  change (RootCoaction.weight f n hn t v hv d (fun i => (m i:ℤ)) : RootCoaction.T f n t v d)*
    RootCoaction.hom f n hn t v hv d _=RootCoaction.right f n t v d _
  simp only [RootCoaction.weight_eq,Units.coe_prod,zpow_natCast,Units.val_pow_eq_pow_val,map_prod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hx := (sectionX f n hn t v hv d i).property
  have hy := (sectionY f n hn t v hv d i).property
  change (RootCoaction.weight f n hn t v hv d (Pi.single i 1) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (-d.roots i)=RootCoaction.right f n t v d (-d.roots i) at hx
  change (RootCoaction.weight f n hn t v hv d (Pi.single i 1) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (1+algebraMap B d.S t*d.roots i)=
        RootCoaction.right f n t v d (1+algebraMap B d.S t*d.roots i) at hy
  rw [weight_single] at hx hy
  simp only [map_mul,map_pow]
  rw [←hx,←hy,mul_pow,mul_pow]
  conv_lhs => lhs; rw [←Nat.add_sub_of_le (he i),pow_add]
  ring

def homogeneousSection (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    module f n hn t v hv d (fun i => (m i:ℤ)) :=
  ⟨∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i),
    homogeneous_product_member f n hn t v hv d m e he⟩

def consecutiveSection (e : PowerIndex n) :
    module f n hn t v hv d (fun i => (powerWeight n i:ℤ)) :=
  ⟨binaryPower t n d.roots e,by
    rw [binaryPower_prod]
    exact homogeneous_product_member f n hn t v hv d _ _ (powerExponent_bound n e)⟩

lemma tensorEquiv_one_tmul [Module.Flat A B] (ms : Fin n → ℤ)
    (x : module f n hn t v hv d ms) : tensorEquiv f n hn t v hv d ms (1 ⊗ₜ[A] x)=(x:d.S) := by
  change (1:B) • (x:d.S)=(x:d.S)
  exact one_smul B _

 

theorem exists_consecutive_basis [Module.FaithfullyFlat A B] :
    ∃ b : Module.Basis (PowerIndex n) A
      (module f n hn t v hv d (fun i => (powerWeight n i:ℤ))),
      ∀ e,b e=consecutiveSection f n hn t v hv d e := by
  have ht := BinaryChange.normalized_top (f.map (algebraMap A B)) t v
    (le_trans (Polynomial.natDegree_map_le) hn) hv
  have hd : (BinaryChange.normalized (f.map (algebraMap A B)) n t v).natDegree≤n := by
    exact le_trans (Polynomial.natDegree_C_mul_le _ _)
      (BinaryChange.transform_degree _ _ _)
  obtain ⟨bb,hbb⟩ := d.exists_binary_basis hd ht t
  apply ModuleDescent.exists_basis_of_baseChange (consecutiveSection f n hn t v hv d)
    (tensorEquiv f n hn t v hv d _) bb
  intro e
  rw [tensorEquiv_one_tmul,hbb]
  rfl
end Lech.RootInvariants

end

end OAI
