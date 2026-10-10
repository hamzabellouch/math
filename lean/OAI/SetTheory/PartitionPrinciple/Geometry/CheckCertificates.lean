import OAI.SetTheory.PartitionPrinciple.Definability.RawCheckFormulas

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def checkStateFormula : SetFormula 3 :=
  ex (ex (.conj (orderedPairFormula 2 1 0) (checkStepFormula 4 3 1 0)))

def checkCertificateFormula : SetFormula 2 := postfixedFormula checkStateFormula

def uniformCheckFormula : SetFormula 3 :=
  ex (.conj (binaryApplication checkCertificateFormula Fin.elim0 0 3) (pairMembershipFormula 1 2 0))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_checkState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (top z R : ZFSet.{u}) (htop : top ∈ M.sets) (hz : z ∈ M.sets) (hr : R ∈ M.sets) :
    Realize M.sets checkStateFormula (extend z (extend R (extend top Fin.elim0))) ↔
      ∃ x ∈ M.sets, ∃ y ∈ M.sets, z = ZFSet.pair x y ∧ M.RawCheckStep top R x y := by
  rw [checkStateFormula, realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [realize_ex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  let e := extend y (extend x (extend z (extend R (extend top Fin.elim0))))
  change (Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_orderedPairFormula pairing 2 1 0 e hz hx hy,
    M.realize_checkStepFormula pairing 4 3 1 0 e htop hr hx hy]
  rfl

theorem checkCertificate_sound {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (hone : s.encode one ∈ M.sets)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets checkCertificateFormula (extend R (extend (s.encode one) Fin.elim0))) :
    ∀ x ∈ M.sets, ∀ y ∈ M.sets, ZFSet.pair x y ∈ R → y = (Name.check s one x).val := by
  have post : ∀ x ∈ M.sets, ∀ y ∈ M.sets, ZFSet.pair x y ∈ R →
      M.RawCheckStep (s.encode one) R x y := by
    intro x _ y _ rel
    have step := (realize_imp M.sets _ _ _).1 (certificate _ (M.transitive hr rel)) rel
    obtain ⟨v, _, w, _, eq, raw⟩ := (M.realize_checkState pairing (s.encode one) _ R
      hone (M.transitive hr rel) hr).1 step
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact raw
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx y hy rel
    exact M.rawCheckStep_eq s one (post x hx y hy rel)
      (fun v hv w hw relation => ih v hv (M.transitive hx hv) w hw relation)

end PartitionPilot.Forcing.TransitiveGround

end OAI
