import Mathlib

namespace OAI

noncomputable section
open TensorProduct
namespace Lech.AdicFlat
variable {R : Type*} [CommRing R]

def contract (S : Type*) [CommRing S] [Algebra R S] (J : Ideal R) : S ⊗[R] J →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
    (AlgebraTensorModule.lTensor S S J.subtype)

@[simp] lemma contract_tmul (S : Type*) [CommRing S] [Algebra R S]
    (J : Ideal R) (s : S) (j : J) : contract S J (s ⊗ₜ[R] j)=(j:R) • s := rfl

lemma coord_contract {T ι : Type*} [CommRing T] [Algebra R T] [DecidableEq ι]
    (b : Module.Basis ι R T) (J : Ideal R) (y : T ⊗[R] J) (i : ι) :
    b.coord i (contract T J y)=((TensorProduct.equivFinsuppOfBasisLeft b y i : J):R) := by
  classical
  induction y using TensorProduct.inductionOn with
  | tmul t j =>
    simp [mul_comm]
  | add y z hy hz => simp only [map_add,Finsupp.add_apply,Submodule.coe_add,hy,hz]

lemma contract_mem_power {T ι : Type*} [CommRing T] [Algebra R T]
    (b : Module.Basis ι R T) (I J : Ideal R) (c : ℕ)
    (hc : ∀ n ≥ c,I^n ⊓ J ≤ I^(n-c)*J)
    (n : ℕ) (y : T ⊗[R] J)
    (hy : contract T J y ∈ I^(n+c) • (⊤ : Submodule R T)) :
    y ∈ I^n • (⊤ : Submodule R (T ⊗[R] J)) := by
  classical
  let a := TensorProduct.equivFinsuppOfBasisLeft b y
  have ha : ∀ i,a i ∈ I^n • (⊤ : Submodule R J) := by
    intro i
    apply (Submodule.mem_smul_top_iff (I^n) J (a i)).mpr
    have hh := Submodule.smul_top_le_comap_smul_top (I^(n+c)) (b.coord i) hy
    have hcoord : (a i : R) ∈ I^(n+c) := by
      simpa only [Submodule.mem_comap,smul_eq_mul,Ideal.mul_top,coord_contract] using hh
    have hr := hc (n+c) (Nat.le_add_left c n) ⟨hcoord,(a i).2⟩
    simpa only [Nat.add_sub_cancel,smul_eq_mul] using hr
  have he : a.sum (fun i j => b i ⊗ₜ[R] j)=y := by
    simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
      (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply y
  rw [← he]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_top_le_comap_smul_top (I^n) (TensorProduct.mk R T J (b i)) (ha i)

lemma artin_rees_ideal [IsNoetherianRing R] (I J : Ideal R) :
    ∃ c : ℕ,∀ n ≥ c,I^n ⊓ J ≤ I^(n-c)*J := by
  obtain ⟨c,hc⟩ := I.exists_pow_inf_eq_pow_smul J
  refine ⟨c,fun n hn => ?_⟩
  have he := hc n hn
  simp only [smul_eq_mul,Ideal.mul_top] at he
  rw [he]
  exact Ideal.mul_mono_right inf_le_right

 
lemma tensor_dense {T S M : Type*} [CommRing T] [Algebra R T]
    [CommRing S] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ)
    (hd : ∀ s : S,∃ t : T,s-algebraMap T S t ∈ I^n • (⊤ : Submodule R S))
    (x : S ⊗[R] M) :
    ∃ y : T ⊗[R] M,x-(LinearMap.rTensor M (IsScalarTower.toAlgHom R T S).toLinearMap) y ∈
      I^n • (⊤ : Submodule R (S ⊗[R] M)) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨t,ht⟩ := hd s
    refine ⟨t ⊗ₜ[R] m,?_⟩
    have hh := Submodule.smul_top_le_comap_smul_top (I^n)
      ((TensorProduct.mk R S M).flip m) ht
    simpa only [Submodule.mem_comap,LinearMap.flip_apply,sub_tmul,LinearMap.rTensor_tmul,
      IsScalarTower.toAlgHom_apply,AlgHom.toLinearMap_apply,TensorProduct.mk_apply,sub_tmul] using hh
  | add x z hx hz =>
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := hz
    refine ⟨a+b,?_⟩
    simpa only [map_add,add_sub_add_comm] using Submodule.add_mem _ ha hb

end Lech.AdicFlat

namespace Lech.AdicFlat
variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]

lemma contract_natural (J : Ideal R) (y : T ⊗[R] J) :
    contract S J ((LinearMap.rTensor J (IsScalarTower.toAlgHom R T S).toLinearMap) y)=
      algebraMap T S (contract T J y) := by
  induction y using TensorProduct.inductionOn with
  | tmul t j =>
    simp only [LinearMap.rTensor_tmul,AlgHom.toLinearMap_apply,IsScalarTower.toAlgHom_apply,contract_tmul]
    exact ((IsScalarTower.toAlgHom R T S).toLinearMap.map_smul (j:R) t).symm
  | add a b ha hb => simp [ha,hb]

 

lemma flat_of_free_dense [IsNoetherianRing R] [Module.Free R T] (I : Ideal R)
    (hd : ∀ n (s : S),∃ t : T,s-algebraMap T S t ∈ I^n • (⊤ : Submodule R S))
    (hp : ∀ n (t : T),algebraMap T S t ∈ I^n • (⊤ : Submodule R S) →
      t ∈ I^n • (⊤ : Submodule R T))
    (hs : ∀ J : Ideal R,IsHausdorff I (S ⊗[R] J)) : Module.Flat R S := by
  let b := Module.Free.chooseBasis R T
  apply Module.Flat.iff_lTensor_injective'.mpr
  intro J
  have hinj : Function.Injective (contract S J) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    change x=0
    have hx0 : contract S J x=0 := hx
    let : IsHausdorff I (S ⊗[R] J) := hs J
    apply (IsHausdorff.eq_iff_smodEq (I:=I)).mpr
    intro n
    rw [SModEq.sub_mem,sub_zero]
    obtain ⟨c,hc⟩ := artin_rees_ideal I J
    obtain ⟨y,hy⟩ := tensor_dense I (n+c) (hd (n+c)) x
    let g := LinearMap.rTensor J (IsScalarTower.toAlgHom R T S).toLinearMap
    have hy' : contract T J y ∈ I^(n+c) • (⊤ : Submodule R T) := by
      apply hp (n+c)
      have hh := Submodule.smul_top_le_comap_smul_top (I^(n+c))
        ((contract S J).restrictScalars R) hy
      change contract S J (x-g y) ∈ I^(n+c) • (⊤ : Submodule R S) at hh
      rw [map_sub,hx0,contract_natural,zero_sub] at hh
      exact neg_mem_iff.mp hh
    have hyy := contract_mem_power b I J c hc n y hy'
    have hmap : g y ∈ I^n • (⊤ : Submodule R (S ⊗[R] J)) :=
      Submodule.smul_top_le_comap_smul_top (I^n) g hyy
    have hie : I^(n+c) • (⊤ : Submodule R (S ⊗[R] J)) ≤ I^n • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))
    have hadd := Submodule.add_mem _ (hie hy) hmap
    simpa [g] using hadd
  intro x y hxy
  apply hinj
  exact congrArg (TensorProduct.AlgebraTensorModule.rid R S S) hxy
end Lech.AdicFlat

end

end OAI
