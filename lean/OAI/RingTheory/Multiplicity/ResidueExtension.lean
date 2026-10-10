import Mathlib
import OAI.RingTheory.Multiplicity.AlgebraicResidueTensor
import OAI.RingTheory.Multiplicity.ArbitraryCoefficientField
import OAI.RingTheory.Multiplicity.CompleteResidueExtension

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech
universe u
structure ResidueExtension (R : Type u) [CommRing R] [IsLocalRing R] where
  S : Type u
  commRing : CommRing S
  localRing : IsLocalRing S
  noetherian : IsNoetherianRing S
  algebra : Algebra R S
  flat : Module.Flat R S
  complete : IsAdicComplete (maximalIdeal S) S
  maximal_map : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S
  algClosed : IsAlgClosed (ResidueField S)
attribute [instance] ResidueExtension.commRing ResidueExtension.localRing
  ResidueExtension.noetherian ResidueExtension.algebra ResidueExtension.flat
  ResidueExtension.complete ResidueExtension.algClosed

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p] [IsAdicComplete (maximalIdeal R) R]

 

def residueExtension : ResidueExtension R := by
  let k := R ⧸ maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  let φ := ArbitraryCoefficientField.localSection R p
  letI : Algebra k R := φ.toAlgebra
  have hres : Function.Bijective (algebraMap k (ResidueField R)) := by
    have h : ∀ a : k,algebraMap k (ResidueField R) a=a :=
      ArbitraryCoefficientField.localSection_rightInverse R p
    exact ⟨fun a b hab => (h a).symm.trans (hab.trans (h b)), fun a => ⟨a,h a⟩⟩
  let K := AlgebraicClosure k
  let T := R ⊗[k] K
  letI : IsLocalRing T := ResidueTensor.isLocal k R K hres
  have hmax : (maximalIdeal R).map (algebraMap R T)=maximalIdeal T :=
    (ResidueTensor.maximalIdeal_eq_map k R K hres).symm
  have fg : (maximalIdeal T).FG := hmax ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _
  let ψ : K →+* T := (Algebra.TensorProduct.includeRight (R:=k) (A:=R)).toRingHom
  have hψ : Function.Surjective ((residue T).comp ψ) :=
    ResidueTensor.residue_surjective k R K hres hmax.symm
  let S := AdicCompletion (maximalIdeal T) T
  letI : IsLocalRing S := AdicCompletion.isLocalRing_of_fg fg
  letI : IsNoetherianRing S := ResidueCompletion.noetherian fg ψ hψ
  letI : IsAdicComplete (maximalIdeal S) S := AdicCompletion.isAdicComplete_of_fg fg
  letI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Free R T := inferInstance
  letI : Module.Flat R S := ResidueCompletion.flat hmax inferInstance
  have hmaxS : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
    calc
      (maximalIdeal R).map (algebraMap R S)=
          ((maximalIdeal R).map (algebraMap R T)).map (algebraMap T S) := by
            rw [Ideal.map_map]
            rfl
      _ = (maximalIdeal T).map (algebraMap T S) := congrArg (Ideal.map (algebraMap T S)) hmax
  let e : K ≃+* ResidueField S := RingEquiv.ofBijective
    ((residue S).comp (ResidueCompletion.coefficient ψ))
    ⟨RingHom.injective _,ResidueCompletion.coefficient_surjective fg ψ hψ⟩
  exact ⟨S,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,hmaxS,IsAlgClosed.of_ringEquiv K (ResidueField S) e⟩

end Lech

end

end OAI
