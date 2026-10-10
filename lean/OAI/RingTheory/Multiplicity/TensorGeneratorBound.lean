import Mathlib
import OAI.RingTheory.Multiplicity.FiniteTensorBound

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorGenerator
variable {D M : Type*} [CommRing D] [AddCommGroup M] [Module D M]

variable {b : ℕ} (f : (Fin b → D) →ₗ[D] M)
  (B : Type*) [CommRing B] [Algebra D B]

def baseGenerators : (Fin b → B) →ₗ[B] B ⊗[D] M :=
  (f.baseChange B).comp (((Pi.basisFun D (Fin b)).baseChange B).equivFun.symm.toLinearMap)

lemma baseGenerators_surjective (hf : Function.Surjective f) :
    Function.Surjective (baseGenerators f B) :=
  (LinearMap.baseChange_surjective B hf).comp
    (((Pi.basisFun D (Fin b)).baseChange B).equivFun.symm.surjective)

variable {R : Type*} [CommRing R] (T : Lech.NormalizedLength.Tower R)
  [Algebra R B]

lemma length_le (hf : Function.Surjective f) (I : Ideal D)
    (hI : I ≤ Module.annihilator D M) :
    T.length (B ⊗[D] M) ≤ (b : ℝ≥0∞) * T.length (B ⧸ I.map (algebraMap D B)) := by
  exact T.length_le_quotient_mul (I.map (algebraMap D B))
    (Lech.NormalizedLength.map_le_annihilator_baseChange I hI)
    (baseGenerators f B) (baseGenerators_surjective f B hf)

lemma scalar_cokernel_le (hf : Function.Surjective f) (I : Ideal D)
    (hI : I ≤ Module.annihilator D M) (g : R) :
    T.length ((B ⊗[D] M) ⧸ (LinearMap.lsmul R (B ⊗[D] M) g).range) ≤
      (b : ℝ≥0∞) * T.length (B ⧸ (I.map (algebraMap D B) ⊔
        Ideal.span {algebraMap R B g})) := by
  exact T.length_scalar_cokernel_le (I.map (algebraMap D B))
    (Lech.NormalizedLength.map_le_annihilator_baseChange I hI)
    (baseGenerators f B) (baseGenerators_surjective f B hf) g
end Lech.TensorGenerator

end

end OAI
