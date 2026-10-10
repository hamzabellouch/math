import OAI.SetTheory.PartitionPrinciple.Forcing.InitialRecursiveActionAgreement
import OAI.SetTheory.PartitionPrinciple.Forcing.RecursiveNextTaskActions

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

structure FixedCompressionSeed
    (P r μ A τ I Sources Reps G m inv one T Filters : ZFSet.{u}) : Prop where
  originalOrder : MeetOrderCode P r μ
  originalAction : PosetActionCode G P m one r A
  top_mem : τ ∈ P
  sources : ZFSet.IsFunc I P Sources
  filters : FunctionGraphOn I Filters
  productAgreement : ∀ δ i j g h k a,
    ZFSet.pair (ZFSet.pair δ i) j ∈ T → ZFSet.pair i a ∈ Sources →
    ZFSet.pair i g ∈ Reps → ZFSet.pair j h ∈ Reps →
    ZFSet.pair (ZFSet.pair δ g) k ∈ m → ActionAgreementBelow P r A k h a
  positiveAgreement : ∀ g h v i j k F,
    ActionAgreementBelow P r A g h v → ZFSet.pair i F ∈ Filters → v ∈ F →
    ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair (ZFSet.pair h i) k ∈ T → j = k

end PartitionPilot.Forcing

end

end OAI
