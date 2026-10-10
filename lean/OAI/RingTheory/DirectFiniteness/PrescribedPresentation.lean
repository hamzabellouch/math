import Mathlib
import OAI.RingTheory.DirectFiniteness.HNNPresentation
import OAI.RingTheory.DirectFiniteness.PrescribedOutputs

namespace OAI

/-! Finite presentation of the prescribed group. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.Prescription.Output

lemma prescribed_base_finitelyPresented :
    Group.IsFinitelyPresented (AssignedDevelopment.Base Inc ell assignment) := by
  let : Finite (GluedGroup.shortRelators Inc ell
    (AssignedDirections.incidenceMap Inc ell assignment)) := N_shortRelators_finite
  exact Group.IsFinitelyPresented.equiv N_shortEquiv

theorem prescribed_finitelyPresented : Group.IsFinitelyPresented G := by
  let := prescribed_base_finitelyPresented
  let : Group.IsFinitelyPresented
      (ChosenCriterion.Extension ell Inc assignment nonempty_Inc girth_Inc v0 form) :=
    CurrentMain.characterTwist_finitelyPresented _ _ _ _
  exact CurrentMain.finitelyPresented_prod _ _

end KaplanskyCounterexample.Prescription.Output

end

end OAI
