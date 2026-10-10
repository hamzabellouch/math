import Mathlib
import OAI.RepresentationTheory.Saxl.DominatedSupport

namespace OAI

/-! Sign twisting and transpose-invariant tensor-square support. -/

noncomputable section
open scoped TensorProduct
open scoped TensorProduct
namespace UniversalTensorSquares
open Saxl

def signTwistEquiv {n : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} (e : ρ.Equiv σ) :
    (signTwist ρ).Equiv (signTwist σ) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' := (signTwistMap e.toIntertwiningMap).isIntertwining'

def signCancelEquiv {n : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} (e : (signTwist ρ).Equiv σ) :
    ρ.Equiv (signTwist σ) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' := (signCancelMap e.toIntertwiningMap).isIntertwining'

def spechtTableauEquiv {n : ℕ} {mu : YoungDiagram} (s t : Tableau n mu) :
    (spechtRep s).Equiv (spechtRep t) :=
  equivOfSubrepEq (spechtSub s) (spechtSub t) (spechtSub_tableau_independent s t)

def spechtShapeEquiv {n : ℕ} {mu nu : YoungDiagram} (s : Tableau n mu)
    (t : Tableau n nu) (h : mu = nu) : (spechtRep s).Equiv (spechtRep t) := by
  subst nu
  exact spechtTableauEquiv s t

lemma canonical_sign_transpose {n : ℕ} (mu : YoungDiagram) (hmu : mu.card = n) :
    Nonempty ((spechtRep (canonicalTableau mu hmu)).Equiv
      (signTwist (spechtRep (canonicalTableau mu.transpose ((transpose_card mu).trans hmu))))) := by
  obtain ⟨e⟩ := specht_sign_transpose (canonicalTableau mu hmu)
  exact ⟨e.trans (signTwistEquiv (spechtTableauEquiv
    (transposeTableau (canonicalTableau mu hmu))
    (canonicalTableau mu.transpose ((transpose_card mu).trans hmu))))⟩

lemma canonical_self_sign {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) :
    Nonempty ((spechtRep (canonicalTableau lam hlam)).Equiv
      (signTwist (spechtRep (canonicalTableau lam hlam)))) := by
  obtain ⟨e⟩ := specht_sign_transpose (canonicalTableau lam hlam)
  exact ⟨e.trans (signTwistEquiv (spechtShapeEquiv
    (transposeTableau (canonicalTableau lam hlam)) (canonicalTableau lam hlam) hself))⟩

lemma support_sign_transfer {n : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (a : ρ.Equiv (signTwist ρ)) (e : σ.Equiv (signTwist τ))
    (f : Representation.IntertwiningMap σ (ρ.tprod ρ)) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap τ (ρ.tprod ρ), F ≠ 0 := by
  let T := tensorAnti ρ a.toIntertwiningMap
  have hT : Function.Injective T := by
    change Function.Injective (TensorProduct.congr (LinearEquiv.refl ℂ X) a.toLinearEquiv)
    exact (TensorProduct.congr (LinearEquiv.refl ℂ X) a.toLinearEquiv).injective
  let F := signCancelMap (ρ := τ) (σ := ρ.tprod ρ) (f.comp e.symm.toIntertwiningMap)
  refine ⟨T.comp F, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have he := congrArg (fun F => F (e x)) hz
  change T (f (e.symm (e x))) = 0 at he
  rw [e.symm_apply_apply] at he
  exact hT (he.trans (map_zero T).symm)

theorem transpose_support_of_self_conjugate {n : ℕ} (lam : YoungDiagram)
    (hlam : lam.card = n) (hself : lam.transpose = lam)
    (nu : YoungDiagram) (hnu : nu.card = n) :
    (0 < kronecker (canonicalTableau lam hlam)
      (canonicalTableau lam hlam) (canonicalTableau nu hnu)) ↔
    (0 < kronecker (canonicalTableau lam hlam) (canonicalTableau lam hlam)
      (canonicalTableau nu.transpose ((transpose_card nu).trans hnu))) := by
  obtain ⟨a⟩ := canonical_self_sign lam hlam hself
  obtain ⟨e⟩ := canonical_sign_transpose nu hnu
  rw [kronecker_pos_iff, kronecker_pos_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact support_sign_transfer a e f hf
  · rintro ⟨f, hf⟩
    exact support_sign_transfer a (signCancelEquiv e.symm) f hf

end UniversalTensorSquares

end

end OAI
