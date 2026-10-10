import OAI.Topology.CoarseAssembly.RelativeUnitary

namespace OAI

/-! # Homotopy invariance of relative unitary classes -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {A P : Type*} [CStarAlgebra A] [TopologicalSpace P]
variable (S : NonUnitalStarSubalgebra ℂ A) [hS : IsClosed (S : Set A)]

theorem continuous_relativeUnitary (u : P → unitary A)
    (hu : ∀ p, (u p : A) - 1 ∈ S) (hcont : Continuous (fun p => (u p : A))) :
    Continuous (fun p => (relativeUnitary S (u p) (hu p) : Unitization ℂ S)) := by
  have hr : Continuous (fun p => relativePart S (u p) (hu p)) :=
    (hcont.sub continuous_const).subtype_mk hu
  exact continuous_const.add (Unitization.continuous_inr.comp hr)

theorem continuous_relativeMatrix (u : P → unitary A)
    (hu : ∀ p, (u p : A) - 1 ∈ S) (hcont : Continuous (fun p => (u p : A))) :
    Continuous (fun p => relativeMatrix S (u p) (hu p)) := by
  have hv := continuous_relativeUnitary S u hu hcont
  have hw : Continuous (fun p => Unitary.toUnits (relativeUnitary S (u p) (hu p))) := by
    apply Units.continuous_iff.mpr
    exact ⟨hv, hv.star⟩
  apply Continuous.comp _ hw
  apply Continuous.units_map
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hij : i = j := Subsingleton.elim _ _
  change Continuous (fun x : Unitization ℂ S => if i = j then x else 0)
  simp only [hij, ite_true]
  convert! (continuous_id : Continuous (fun x : Unitization ℂ S => x))

theorem relativeClass_homotopy (u : Interval → unitary A)
    (hu : ∀ t, (u t : A) - 1 ∈ S) (hcont : Continuous (fun t => (u t : A))) :
    relativeClass S (u start) (hu start) = relativeClass S (u finish) (hu finish) := by
  apply Subtype.ext
  exact TopologicalK1.matrixClass_homotopy (fun t => relativeMatrix S (u t) (hu t))
    (continuous_relativeMatrix S u hu hcont)

end CoarseAssembly.OperatorKTheory

end

end OAI
