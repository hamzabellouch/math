import Mathlib
import OAI.RingTheory.Multiplicity.ScalarHomologyError

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.TensorConductor
universe u
variable {D R C : Type u} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) [Algebra D B] [IsScalarTower D B C]

def stageComplex (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex _).obj
    (((ModuleCat.extendScalars (algebraMap D B)).mapHomologicalComplex _).obj F)

def ambientComplex (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).obj
    (((ModuleCat.extendScalars (algebraMap D C)).mapHomologicalComplex _).obj F)

def complexInclusion (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    stageComplex B F ⟶ ambientComplex (R := R) (C := C) F := by
  have hc := IsScalarTower.algebraMap_eq D B C
  let fB := algebraMap D B
  let fC := algebraMap D C
  letI : Algebra D B := fB.toAlgebra
  letI : Algebra D C := fC.toAlgebra
  letI : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' hc
  refine { f := fun i => ?_, comm' := ?_ }
  · let X := (stageComplex B F).X i
    let Y := (ambientComplex (R := R) (C := C) F).X i
    letI : Module R X := X.isModule
    letI : Module R Y := Y.isModule
    refine ModuleCat.ofHom (X := X) (Y := Y) (show X →ₗ[R] Y from
      { __ := (inclusion (D := D) B (F.X i)).toAddHom, map_smul' := ?_ })
    intro r x
    change B ⊗[D] (F.X i) at x
    change inclusion (D := D) B (F.X i) ((algebraMap R B r) • (x : B ⊗[D] (F.X i))) =
      (algebraMap R C r) • inclusion (D := D) B (F.X i) x
    simpa only [IsScalarTower.algebraMap_smul] using
      (inclusion (D := D) B (F.X i)).map_smul r x
  · intro i j hij
    apply ModuleCat.hom_ext
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b x => rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (·+·) hx hy).trans (map_add _ x y).symm)

def complexRetreat (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (g : R) (hg : ∀ c : C,g • c∈B) :
    ambientComplex (R := R) (C := C) F ⟶ stageComplex B F := by
  have hc := IsScalarTower.algebraMap_eq D B C
  let fB := algebraMap D B
  let fC := algebraMap D C
  letI : Algebra D B := fB.toAlgebra
  letI : Algebra D C := fC.toAlgebra
  letI : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' hc
  refine { f := fun i => ?_, comm' := ?_ }
  · let X := (ambientComplex (R := R) (C := C) F).X i
    let Y := (stageComplex B F).X i
    letI : Module R X := X.isModule
    letI : Module R Y := Y.isModule
    refine ModuleCat.ofHom (X := X) (Y := Y) (show X →ₗ[R] Y from
      { __ := (conductor (D := D) B (F.X i) g hg).toAddHom, map_smul' := ?_ })
    intro r x
    change C ⊗[D] (F.X i) at x
    change conductor (D := D) B (F.X i) g hg ((algebraMap R C r) • (x : C ⊗[D] (F.X i))) =
      (algebraMap R B r) • conductor (D := D) B (F.X i) g hg x
    simpa only [IsScalarTower.algebraMap_smul] using
      (conductor (D := D) B (F.X i) g hg).map_smul r x
  · intro i j hij
    apply ModuleCat.hom_ext
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul c x => rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (·+·) hx hy).trans (map_add _ x y).symm)

lemma complex_conductor_composition (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (g : R) (hg : ∀ c : C,g • c∈B) :
    complexInclusion B F ≫ complexRetreat B F g hg = g • 𝟙 (stageComplex B F) := by
  have hc := IsScalarTower.algebraMap_eq D B C
  let fB := algebraMap D B
  let fC := algebraMap D C
  let : Algebra D B := fB.toAlgebra
  let : Algebra D C := fC.toAlgebra
  let : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' hc
  ext i : 1
  apply ModuleCat.hom_ext
  ext x
  change B ⊗[D] (F.X i) at x
  have he := LinearMap.congr_fun (conductor_composition (D := D) B (F.X i) g hg) x
  change conductor (D := D) B (F.X i) g hg (inclusion (D := D) B (F.X i) x) =
    (algebraMap R B g) • (x : B ⊗[D] (F.X i))
  simpa only [IsScalarTower.algebraMap_smul,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply] using he

lemma stage_homology_length_le (T : NormalizedLength.Tower R)
    (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (g : R) (hg : ∀ c : C,g • c∈B) (i : ℤ)
    (hinj : ∀ j,Function.Injective (fun x : (stageComplex B F).X j => g • x))
    (hfin : T.length ((stageComplex B F).homology i) ≠ ⊤) :
    T.length ((stageComplex B F).homology i) ≤
      T.length ((ambientComplex (R := R) (C := C) F).homology i) +
      T.length ((((Lech.complexQuotient (Ideal.span {g}) (.up ℤ)).obj
        (stageComplex B F)).homology i)) :=
  normalized_homology_length_le_of_scalar_retract T
    (complexInclusion B F) (complexRetreat B F g hg) g
    (complex_conductor_composition B F g hg) i hinj hfin
end Lech.TensorConductor

end

end OAI
