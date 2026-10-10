import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.Assembly

namespace OAI

/-! # Transport of a proved compatible analytic index family -/

noncomputable section

namespace CoarseAssembly.Analytic.CompatibleIndexFamily

universe u v

variable {C D : Coarsening.{u}} {A B : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Apply an actual homomorphism to the target of every scale index. -/
def mapTarget (I : CompatibleIndexFamily C A) (φ : A →⋆ₙₐ[ℂ] B) :
    CompatibleIndexFamily C B where
  atScale r := (OperatorKTheory.map φ).comp (I.atScale r)
  compatible r s hrs a := by
    change OperatorKTheory.map φ (I.atScale s (C.map r s hrs a)) = _
    rw [I.compatible]
    rfl

end CoarseAssembly.Analytic.CompatibleIndexFamily

end

end OAI
