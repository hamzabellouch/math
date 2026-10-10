import Mathlib
import OAI.RingTheory.Multiplicity.FibreSquare
import OAI.RingTheory.Multiplicity.ProductSourceCoverCechNat

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def quotientFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))
  map f := ModuleCat.ofHom (idealQuotientMap I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance quotientFunctor_additive : (quotientFunctor I).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

lemma quotientFunctor_map_mk {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    ((quotientFunctor I).map f).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.hom x) := rfl

 
def quotientNat : 𝟭 (ModuleCat.{u} R) ⟶ quotientFunctor I where
  app M := ModuleCat.ofHom (Submodule.mkQ (I • (⊤ : Submodule R M)))
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

 
def tensorQuotientIso :
    (curriedTensor (ModuleCat.{u} R)).flip.obj (ModuleCat.of R (R ⧸ I)) ≅ quotientFunctor I :=
  NatIso.ofComponents (fun M => (TensorProduct.tensorQuotEquivQuotSMul M I).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul x r =>
        obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective r
        change TensorProduct.tensorQuotEquivQuotSMul N I
            (f.hom x ⊗ₜ[R] Ideal.Quotient.mk I r) =
            idealQuotientMap I f.hom (TensorProduct.tensorQuotEquivQuotSMul M I
              (x ⊗ₜ[R] Ideal.Quotient.mk I r))
        rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
            TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, idealQuotientMap_mk,map_smul])

 
def quotientPiEquiv {ι : Type*} [Fintype ι] (M : ι → Type u)
    [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] :
    ((∀ i,M i) ⧸ (I • (⊤ : Submodule R (∀ i,M i)))) ≃ₗ[R]
      (∀ i, M i ⧸ (I • (⊤ : Submodule R (M i)))) := by
  classical
  exact (TensorProduct.quotTensorEquivQuotSMul (∀ i,M i) I).symm ≪≫ₗ
    TensorProduct.piRight R R (R ⧸ I) M ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => TensorProduct.quotTensorEquivQuotSMul (M i) I)

lemma quotientPiEquiv_mk {ι : Type*} [Fintype ι] (M : ι → Type u)
    [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] (x : ∀ i,M i) :
    quotientPiEquiv I M (Submodule.Quotient.mk x) = fun i => Submodule.Quotient.mk (x i) := by
  classical
  unfold quotientPiEquiv
  simp only [LinearEquiv.trans_apply,TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    TensorProduct.piRight_apply,TensorProduct.piRightHom_tmul]
  funext i
  change TensorProduct.quotTensorEquivQuotSMul (M i) I (1 ⊗ₜ[R] x i)=_
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I (x i)

 
lemma mem_smul_pi_iff {ι : Type*} [Fintype ι] (M : ι → Type u)
    [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)] (x : ∀ i,M i) :
    x ∈ I • (⊤ : Submodule R (∀ i,M i)) ↔ ∀ i,x i ∈ I • (⊤ : Submodule R (M i)) := by
  rw [←Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h i
    have he := congrArg (quotientPiEquiv I M) h
    rw [quotientPiEquiv_mk,map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun he i)
  · intro h
    apply (quotientPiEquiv I M).injective
    rw [quotientPiEquiv_mk,map_zero]
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h i)

lemma quotient_torsion (M : Type u) [AddCommGroup M] [Module R M] :
    powerTorsion I (ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [←Submodule.Quotient.mk_smul,Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

variable {ι : Type} [Fintype ι] (M N : ι → Type u)
  [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)]
  [∀ i,AddCommGroup (N i)] [∀ i,Module R (N i)]
  (f : ∀ i,M i →ₗ[R] N i)

lemma quotientPiMap_square (x : (∀ i,M i) ⧸ (I • (⊤ : Submodule R (∀ i,M i)))) :
    quotientPiEquiv I N
      (idealQuotientMap I (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) x) =
        fun i => idealQuotientMap I (f i) (quotientPiEquiv I M x i) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [idealQuotientMap_mk,quotientPiEquiv_mk,quotientPiEquiv_mk]
    rfl

lemma quotientPiMap_factor :
    (quotientFunctor I).map (ModuleCat.ofHom
      (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i)))) =
    (quotientPiEquiv I M).toModuleIso.hom ≫
      ModuleCat.ofHom (LinearMap.pi (fun i => (idealQuotientMap I (f i)).comp (LinearMap.proj i))) ≫
        (quotientPiEquiv I N).toModuleIso.inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (quotientPiEquiv I N).injective
  change quotientPiEquiv I N (idealQuotientMap I _ x) =
    quotientPiEquiv I N ((quotientPiEquiv I N).symm _)
  rw [LinearEquiv.apply_symm_apply]
  exact quotientPiMap_square I M N f x

lemma quotientPi_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hf : ∀ i,P.isoModSerre (ModuleCat.ofHom (idealQuotientMap I (f i)))) :
    P.isoModSerre ((quotientFunctor I).map (ModuleCat.ofHom
      (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))))) := by
  let e := (quotientPiEquiv I M).toModuleIso
  let e' := (quotientPiEquiv I N).toModuleIso
  have hM : P.isoModSerre e.hom := P.isoModSerre_of_isIso e.hom
  have hN : P.isoModSerre e'.inv := P.isoModSerre_of_isIso e'.inv
  have hp := piLinear_isoModSerre (fun i => idealQuotientMap I (f i)) P hf
  rw [quotientPiMap_factor]
  exact P.isoModSerre.comp_mem _ _ hM (P.isoModSerre.comp_mem _ _ hp hN)

end Lech.TensorIdeal

end

end OAI
