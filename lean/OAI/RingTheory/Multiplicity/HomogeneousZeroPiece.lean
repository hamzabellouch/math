import Mathlib
import OAI.RingTheory.Multiplicity.LechPiIso

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
attribute [local instance] awayAddCommGroup

def toZeroPiece : Away G f →ₗ[R] TwistedLocalization.piece G (f:=f) (d:=d) 0 where
  toFun x := ⟨x.val,by
    obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective G hf x
    change Localization.mk a (⟨f^n,n,rfl⟩ : Submonoid.powers f) ∈ _
    exact TwistedLocalization.fraction_mem G 0 n
      ⟨a,by simpa only [Nat.add_zero,nsmul_eq_mul,Nat.cast_id] using ha⟩⟩
  map_add' x y := Subtype.ext (HomogeneousLocalization.val_add _ _)
  map_smul' r x := Subtype.ext (HomogeneousLocalization.val_smul _ r x)

lemma toZeroPiece_val (x : Away G f) : (toZeroPiece G hf x).val = x.val := rfl
lemma toZeroPiece_injective : Function.Injective (toZeroPiece G hf) := by
  intro x y hxy
  exact HomogeneousLocalization.val_injective _ (congrArg Subtype.val hxy)
lemma toZeroPiece_surjective : Function.Surjective (toZeroPiece G hf) := by
  intro x
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction G hf 0 x
  refine ⟨Away.mk G hf n a (by simpa only [Nat.add_zero,nsmul_eq_mul,Nat.cast_id] using a.property),?_⟩
  apply Subtype.ext
  exact ha

def zeroPieceEquiv : Away G f ≃ₗ[R] TwistedLocalization.piece G (f:=f) (d:=d) 0 :=
  LinearEquiv.ofBijective (toZeroPiece G hf) ⟨toZeroPiece_injective G hf,toZeroPiece_surjective G hf⟩
end Lech.Homogeneous

end

end OAI
