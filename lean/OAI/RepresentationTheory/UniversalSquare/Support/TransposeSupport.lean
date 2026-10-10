import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Candidate

namespace OAI

/-! Transpose Support. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

def signTwistEquiv {n : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} (e : ρ.Equiv σ) :
    (Saxl.signTwist ρ).Equiv (Saxl.signTwist σ) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' := (Saxl.signTwistMap e.toIntertwiningMap).isIntertwining'

lemma canonical_sign_transpose {n : ℕ} (μ : YoungDiagram) (hμ : μ.card = n) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau μ hμ)).Equiv
      (Saxl.signTwist (Saxl.spechtRep
        (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ))))) := by
  obtain ⟨e⟩ := Saxl.specht_sign_transpose (Saxl.canonicalTableau μ hμ)
  let e' := Saxl.equivOfSubrepEq
    (Saxl.spechtSub (Saxl.transposeTableau (Saxl.canonicalTableau μ hμ)))
    (Saxl.spechtSub
      (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ)))
    (Saxl.spechtSub_tableau_independent _ _)
  exact ⟨e.trans (signTwistEquiv e')⟩

def spechtShapeEquiv {n : ℕ} {μ ν : YoungDiagram} (h : μ = ν)
    (t : Saxl.Tableau n μ) (s : Saxl.Tableau n ν) :
    (Saxl.spechtRep t).Equiv (Saxl.spechtRep s) := by
  subst ν
  exact Saxl.equivOfSubrepEq _ _ (Saxl.spechtSub_tableau_independent t s)

lemma canonical_self_sign {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).Equiv
      (Saxl.signTwist (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)))) := by
  obtain ⟨e⟩ := canonical_sign_transpose lam hlam
  let e' := spechtShapeEquiv hself
    (Saxl.canonicalTableau lam.transpose ((Saxl.transpose_card lam).trans hlam))
    (Saxl.canonicalTableau lam hlam)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma tensorAnti_injective {n : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (e : σ.Equiv (Saxl.signTwist τ)) :
    Function.Injective (Saxl.tensorAnti ρ e.toIntertwiningMap) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ X) e.toLinearEquiv).injective

lemma kronecker_pos_transpose {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
    (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)) := by
  obtain ⟨eL⟩ := canonical_self_sign lam hlam hself
  obtain ⟨eν⟩ := canonical_sign_transpose ν hν
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp hpos
  let A := Saxl.tensorAnti (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))
    eL.toIntertwiningMap
  let B := (Saxl.signTwistMap
    (Y := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f).comp (Saxl.signCancelMap eν.symm.toIntertwiningMap)
  apply (Saxl.kronecker_pos_iff _ _ _).mpr
  refine ⟨A.comp B, ?_⟩
  intro hz
  apply hf
  ext x
  have h := congrArg (fun F => F (eν x)) hz
  have hi : Function.Injective A := tensorAnti_injective _ eL
  apply hi
  change A (f x) = A 0
  change A (f (eν.symm (eν x))) = 0 at h
  simpa only [eν.symm_apply_apply, map_zero] using h

theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) := by
  constructor
  · exact kronecker_pos_transpose lam hlam hself ν hν
  · intro h
    have ht := kronecker_pos_transpose lam hlam hself ν.transpose
      ((Saxl.transpose_card ν).trans hν) h
    obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp ht
    let e := spechtShapeEquiv (YoungDiagram.transpose_transpose ν).symm
      (Saxl.canonicalTableau ν hν)
      (Saxl.canonicalTableau ν.transpose.transpose
        ((Saxl.transpose_card ν.transpose).trans ((Saxl.transpose_card ν).trans hν)))
    apply (Saxl.kronecker_pos_iff _ _ _).mpr
    refine ⟨f.comp e.toIntertwiningMap, ?_⟩
    intro hz
    apply hf
    ext x
    have hh := congrArg (fun F => F (e.symm x)) hz
    change f (e (e.symm x)) = 0 at hh
    simpa using hh

lemma fixedCandidate_support_transpose (n : ℕ) (hM : 3 ≤ staircaseIndex n)
    (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau (fixedCandidate n) (fixedCandidate_card n hM))
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) :=
  kronecker_pos_transpose_iff _ _ (fixedCandidate_transpose n) ν hν

end UniversalTensorSquare
end
end

end OAI
