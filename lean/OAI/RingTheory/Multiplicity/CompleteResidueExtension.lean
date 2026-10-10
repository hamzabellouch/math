import Mathlib
import OAI.RingTheory.Multiplicity.AdicDense
import OAI.RingTheory.Multiplicity.AdicFlatCriterion
import OAI.RingTheory.Multiplicity.CompleteNoetherian

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech.ResidueCompletion
variable {T K : Type*} [CommRing T] [IsLocalRing T] [Field K]

def coefficient (φ : K →+* T) : K →+* AdicCompletion (maximalIdeal T) T :=
  (algebraMap T (AdicCompletion (maximalIdeal T) T)).comp φ

lemma coefficient_surjective (fg : (maximalIdeal T).FG) (φ : K →+* T)
    (hφ : Function.Surjective ((residue T).comp φ)) :
    letI := AdicCompletion.isLocalRing_of_fg fg
    Function.Surjective ((residue (AdicCompletion (maximalIdeal T) T)).comp (coefficient φ)) := by
  let := AdicCompletion.isLocalRing_of_fg fg
  let := AdicCompletion.algebraMap_isLocalHom_of_fg fg
  intro x
  obtain ⟨y,rfl⟩ := (AdicCompletion.residueField_map_bijective_of_fg fg).2 x
  obtain ⟨k,rfl⟩ := hφ y
  refine ⟨k,?_⟩
  exact (ResidueField.map_residue _ _).symm

lemma noetherian (fg : (maximalIdeal T).FG) (φ : K →+* T)
    (hφ : Function.Surjective ((residue T).comp φ)) :
    IsNoetherianRing (AdicCompletion (maximalIdeal T) T) := by
  let := AdicCompletion.isLocalRing_of_fg fg
  let := AdicCompletion.isAdicComplete_of_fg fg
  apply Lech.CompleteLocal.noetherian_of_coefficient_and_fg (coefficient φ)
    (coefficient_surjective fg φ hφ)
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact fg.map _

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Algebra R T] [Module.Free R T]

lemma flat (hmax : (maximalIdeal R).map (algebraMap R T)=maximalIdeal T)
    (hNoeth : IsNoetherianRing (AdicCompletion (maximalIdeal T) T)) :
    Module.Flat R (AdicCompletion (maximalIdeal T) T) := by
  let S := AdicCompletion (maximalIdeal T) T
  have fg : (maximalIdeal T).FG := hmax ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _
  let := AdicCompletion.isLocalRing_of_fg fg
  let : IsNoetherianRing S := hNoeth
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' rfl
  have hmap : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
    calc
      (maximalIdeal R).map (algebraMap R S)=
          ((maximalIdeal R).map (algebraMap R T)).map (algebraMap T S) := by
            rw [Ideal.map_map]
            rfl
      _ = (maximalIdeal T).map (algebraMap T S) := congrArg (Ideal.map (algebraMap T S)) hmax
  apply Lech.AdicFlat.flat_of_free_dense (T:=T) (maximalIdeal R)
  · exact Lech.AdicFlat.completion_dense _ _ hmax fg
  · exact Lech.AdicFlat.completion_contract _ _ hmax fg
  · intro J
    let : Module.Finite R J := Module.Finite.iff_fg.mpr (Ideal.fg_of_isNoetherianRing J)
    let : Module.Finite S (S ⊗[R] J) := inferInstance
    exact IsHausdorff.of_map (I:=maximalIdeal R) (J:=maximalIdeal S) hmap.le
end Lech.ResidueCompletion

end

end OAI
