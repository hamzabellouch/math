import OAI.RingTheory.DirectFiniteness.ShortRelators

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription.Output
local instance (priority := 3000) : DecidableEq Subfield := Classical.decEq _
local instance (priority := 3000) : DecidableEq V := Classical.decEq _

/-- The group in the literal prescription: the coordinate gluing, its multiple
HNN extension and the finite permutation/character block. -/
abbrev G := ChosenCriterion.Group (m := Slots) ell Inc assignment nonempty_Inc girth_Inc v0 form

def a : MonoidAlgebra Coeff G :=
  ChosenCriterion.aOut ell Inc assignment nonempty_Inc girth_Inc v0 form
    (zeta_primitive h) X i0 slot

def b : MonoidAlgebra Coeff G :=
  ChosenCriterion.bOut ell Inc assignment nonempty_Inc girth_Inc v0 form
    (zeta_primitive h) X i0 slot

/-- The two product assertions are for the specified first successful data and
specified sums, not merely for some field, some group or some pair of inverses. -/
theorem prescribed_products : a*b=1 ∧ b*a≠1 :=
  ChosenCriterion.products ell Inc assignment nonempty_Inc girth_Inc v0 form
    (zeta_primitive h) X i0 slot (prime_odd h.val h.property) sizes.2.1
    (by convert X_global using 1; congr 1; ext i j; simp only [Matrix.one_apply]; split_ifs <;> rfl) X_local forms_distinct

instance G_fg : Group.FG G := inferInstance

def N_shortEquiv :
    PresentedGroup (GluedGroup.shortRelators Inc ell
      (AssignedDirections.incidenceMap Inc ell assignment)) ≃*
    AssignedDevelopment.Base Inc ell assignment :=
  GluedGroup.shortEquiv Inc ell _ (AssignedDevelopment.covers Inc ell assignment)

lemma N_shortRelators_finite :
    (GluedGroup.shortRelators Inc ell (AssignedDirections.incidenceMap Inc ell assignment)).Finite :=
  GluedGroup.shortRelators_finite _ _ _

/-- The literal prescription supplies the main existential witnesses. -/
theorem prescribed_main :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
        ∃ a b : MonoidAlgebra K G, a*b=1 ∧ b*a≠1 :=
  ⟨Coeff,inferInstance,inferInstance,inferInstance,G,inferInstance,inferInstance,a,b,
    prescribed_products⟩

end KaplanskyCounterexample.Prescription.Output
end

end OAI
