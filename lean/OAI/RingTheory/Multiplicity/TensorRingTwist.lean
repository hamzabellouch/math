import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusIntermediatePowerMap
import OAI.RingTheory.Multiplicity.PerfectTensorLimit

namespace OAI

noncomputable section
open scoped TensorProduct ChangeOfRings
namespace Lech.TensorTwist
open CategoryTheory
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable {D C C' : Type u} [CommRing D] [CommRing C] [CommRing C']

def scalarEquiv (f : D →+* C) (e : C ≃+* C') :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of C C) ≃ₗ[D]
      (ModuleCat.restrictScalars ((e : C →+* C').comp f)).obj (ModuleCat.of C' C') where
  __ := e.toAddEquiv
  map_smul' d c := by
    exact e.map_mul (f d) c

def extendEquiv (f : D →+* C) (e : C ≃+* C') (M : ModuleCat.{u} D) :
    LinearEquiv (σ' := (e.symm : C' →+* C)) (e : C →+* C')
      ((ModuleCat.extendScalars f).obj M) ((ModuleCat.extendScalars ((e : C →+* C').comp f)).obj M) where
  __ := (TensorProduct.congr (scalarEquiv f e) (LinearEquiv.refl D M)).toAddEquiv
  map_smul' c t := by
    induction t using TensorProduct.inductionOn with
    | tmul x m =>
      exact congrArg (fun (v : C') => v ⊗ₜ[D, (e : C →+* C').comp f] m)
        (e.map_mul c x)
    | add x y hx hy =>
      let F : ((ModuleCat.extendScalars f).obj M) →+
          ((ModuleCat.extendScalars ((e : C →+* C').comp f)).obj M) :=
        (TensorProduct.congr (scalarEquiv f e) (LinearEquiv.refl D M)).toAddEquiv.toAddMonoidHom
      have hs : c • (show (ModuleCat.extendScalars f).obj M from x + y) =
          c • (show (ModuleCat.extendScalars f).obj M from x) +
            c • (show (ModuleCat.extendScalars f).obj M from y) :=
        smul_add c (show (ModuleCat.extendScalars f).obj M from x)
          (show (ModuleCat.extendScalars f).obj M from y)
      exact (congrArg F hs).trans ((F.map_add _ _).trans
        ((congrArg₂ (·+·) hx hy).trans ((smul_add (e c) (F x) (F y)).symm.trans
          (congrArg (fun z => e c • z) (F.map_add x y).symm))))

def algebraExtendEquiv {P : Type u} [CommRing P] [Algebra P C] [Algebra P C']
    (f : D →+* C) (e : C ≃ₐ[P] C') (M : ModuleCat.{u} D) :
    (ModuleCat.restrictScalars (algebraMap P C)).obj ((ModuleCat.extendScalars f).obj M) ≃ₗ[P]
      (ModuleCat.restrictScalars (algebraMap P C')).obj
        ((ModuleCat.extendScalars (e.toRingHom.comp f)).obj M) where
  __ := (extendEquiv f e.toRingEquiv M).toAddEquiv
  map_smul' r x := by
    have h := (extendEquiv f e.toRingEquiv M).map_smulₛₗ (algebraMap P C r)
      (show (ModuleCat.extendScalars f).obj M from x)
    exact h.trans (congrArg
      (fun c : C' => c • extendEquiv f e.toRingEquiv M x) (e.commutes r))

def undo (e : C ≃+* C) (M : ModuleCat.{u} C) :
    LinearEquiv (σ' := (e : C →+* C)) (e.symm : C →+* C)
      ((ModuleCat.extendScalars (e : C →+* C)).obj M) M := by
  have hx : (e.symm : C →+* C).comp (e : C →+* C) = RingHom.id C := by ext x; exact e.symm_apply_apply x
  let q := extendEquiv (e : C →+* C) e.symm M
  rw [hx] at q
  exact q.trans ((ModuleCat.extendScalarsId C).app M).toLinearEquiv

end Lech.TensorTwist

namespace Lech.RootTower
open CategoryTheory
open scoped ENNReal ChangeOfRings
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable (σ : Type) (k : Type u) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]
  {D C : Type u} [CommRing D] [CommRing C] [CharP C p] [PerfectRing C p]
  [Algebra (PerfectClosure (MvPowerSeries σ k) p) C]

 

theorem normalizedLength_frobenius_extend (f : D →+* C) (d : ℕ) (M : ModuleCat.{u} D) :
    normalizedLength σ k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries σ k) p) C)).obj
        ((ModuleCat.extendScalars f).obj M)) =
      ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * normalizedLength σ k p
        ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries σ k) p) C)).obj
          ((ModuleCat.extendScalars
            ((iterateFrobeniusEquiv C p d : C →+* C).comp f)).obj M)) := by
  let P := PerfectClosure (MvPowerSeries σ k) p
  let e := iterateFrobeniusEquiv C p d
  let g := (e : C →+* C).comp f
  have hx : (e.symm : C →+* C).comp g = f := by ext x; exact e.symm_apply_apply (f x)
  let q := Lech.TensorTwist.extendEquiv g e.symm M
  rw [hx] at q
  let E : LinearEquiv (σ' := (iterateFrobeniusEquiv P p d : P →+* P))
      ((iterateFrobeniusEquiv P p d).symm : P →+* P)
      ((ModuleCat.restrictScalars (algebraMap P C)).obj ((ModuleCat.extendScalars g).obj M))
      ((ModuleCat.restrictScalars (algebraMap P C)).obj ((ModuleCat.extendScalars f).obj M)) :=
    { q.toAddEquiv with
      map_smul' := by
        intro a x
        have h := q.map_smulₛₗ (algebraMap P C a)
          (show (ModuleCat.extendScalars g).obj M from x)
        exact h.trans (congrArg (fun c : C => c • q x)
          (map_inverse_frobenius p (algebraMap P C) d a).symm) }
  exact normalizedLength_root_equiv σ k p d E
end Lech.RootTower

end

end OAI
