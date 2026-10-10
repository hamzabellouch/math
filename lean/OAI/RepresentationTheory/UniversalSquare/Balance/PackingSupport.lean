import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ProductInduction
import OAI.RepresentationTheory.UniversalSquare.Specht.CyclicRestriction
import OAI.RepresentationTheory.UniversalSquare.Support.CoindProduct

namespace OAI

/-! Packing Support. -/

section

noncomputable section
open scoped TensorProduct MonoidAlgebra
namespace Saxl

theorem cyclic_supportLE_coind {G H X Y : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ H Y)
    (φ : H →* G) (v : X)
    (T : Representation.IntertwiningMap σ (ρ.comp φ)) (hv : v ∈ T.range) :
    SupportLE (cyclic ρ v).toRepresentation (Representation.coind φ σ) := by
  apply intertwining_separates_of_simple_support
  intro S hS
  let := hS
  have hi : subrepInclusion S ≠ 0 := by
    intro hz
    let : Nontrivial S.toRepresentation.asModule :=
      IsSimpleModule.nontrivial ℂ[G] S.toRepresentation.asModule
    let : Nontrivial S.toSubmodule := S.toRepresentation.asModuleEquiv.symm.toEquiv.nontrivial
    obtain ⟨x,hx⟩ := exists_ne (0 : S.toSubmodule)
    apply hx
    apply Subtype.ext
    exact congrArg (fun f : Representation.IntertwiningMap S.toRepresentation
      (cyclic ρ v).toRepresentation => f x) hz
  obtain ⟨F,hF⟩ := cyclic_restriction_support S.toRepresentation σ ρ φ v T hv
    (subrepInclusion S) hi
  exact ⟨coindLift φ F,coindLift_ne_zero φ F hF⟩

theorem SupportLE.cyclic_image {G X Y Z : Type*} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z} (v : X)
    (T : Representation.IntertwiningMap ρ σ) (h : SupportLE (cyclic ρ v).toRepresentation τ) :
    SupportLE (cyclic σ (T v)).toRepresentation τ := by
  let Q := T.comp (subrepInclusion (cyclic ρ v))
  have hm : T v ∈ Q.range := ⟨⟨v,mem_cyclic ρ v⟩,rfl⟩
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range Q (cyclic σ (T v))
    ((cyclic_le _ _ _).mpr hm)
  exact (SupportLE.of_injective i hi).trans h

def cyclicProductMap {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d) :
    Representation.IntertwiningMap
      (outer (cyclic (wordRep a d) v).toRepresentation (cyclic (wordRep b d) u).toRepresentation)
      ((wordRep n d).comp (sumPermHom e)) :=
  externalWordMap e (subrepInclusion (cyclic (wordRep a d) v))
    (subrepInclusion (cyclic (wordRep b d) u))

lemma cyclicProduct_mem_range {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d) :
    positionProduct e v u ∈ (cyclicProductMap e v u).range := by
  refine ⟨(⟨v,mem_cyclic _ _⟩ : (cyclic (wordRep a d) v).toSubmodule) ⊗ₜ[ℂ]
    (⟨u,mem_cyclic _ _⟩ : (cyclic (wordRep b d) u).toSubmodule), ?_⟩
  exact positionTensor_tmul e v u

theorem product_supportLE_coind {n a b d : ℕ} {G H X Y : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (φ : G →* Equiv.Perm (Fin a)) (ψ : H →* Equiv.Perm (Fin b))
    (ρ : Representation ℂ G X) (σ : Representation ℂ H Y)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (hv : SupportLE (cyclic (wordRep a d) v).toRepresentation (Representation.coind φ ρ))
    (hu : SupportLE (cyclic (wordRep b d) u).toRepresentation (Representation.coind ψ σ)) :
    SupportLE (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation
      (Representation.coind ((sumPermHom e).comp (φ.prodMap ψ)) (outer ρ σ)) := by
  classical
  let : AddCommGroup ((cyclic (wordRep a d) v).toSubmodule ⊗[ℂ]
      (cyclic (wordRep b d) u).toSubmodule) := Module.addCommMonoidToAddCommGroup ℂ
  have h₀ := cyclic_supportLE_coind (wordRep n d)
    (outer (cyclic (wordRep a d) v).toRepresentation (cyclic (wordRep b d) u).toRepresentation)
    (sumPermHom e) (positionProduct e v u) (cyclicProductMap e v u) (cyclicProduct_mem_range e v u)
  have h₁ := (hv.outer hu).coind (sumPermHom e)
  have h₂ := (SupportLE.of_injective (coindOuter φ ψ ρ σ)
    (coindOuter_injective φ ψ ρ σ)).coind (sumPermHom e)
  have h₃ := SupportLE.of_injective (coindTrans (φ.prodMap ψ) (sumPermHom e) (outer ρ σ))
    (coindTrans_injective (φ.prodMap ψ) (sumPermHom e) (outer ρ σ))
  exact ((h₀.trans h₁).trans h₂).trans h₃

theorem young_cyclic_support {n : ℕ} (θ μ : YoungDiagram) (t : Tableau n μ)
    (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (w : Fin n → Fin (θ.colLen 0)) (f : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = f j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation, F ≠ 0 := by
  obtain ⟨F,hF⟩ := young_orbit_map θ μ t hc hd w f hw
  let Q := F.comp (subrepInclusion (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)))
  have hQ : Q ≠ 0 := by
    intro h0
    exact hF (congrArg (fun T : Representation.IntertwiningMap
      (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation (spechtRep t) =>
        T ⟨Pi.single w 1,mem_cyclic _ _⟩) h0)
  exact intertwining_reverse_nonzero Q hQ

end Saxl
end
end

end OAI
