import OAI.RepresentationTheory.RestrictedTilting.GeneratedStableKernel

namespace OAI

namespace FiberFunctorProof
open CategoryTheory
universe u
 
def StableRestrictionKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ), 1 ≤ r → ∀ (l : (Fin r → ZMod p) →+ k), Function.Injective l →
      ∀ (A B : Tilting k) (f : A ⟶ B),
        FactorsThroughProjective ((restrictElementary k p r l).map f.hom) ↔
          f ∈ steinbergIdeal k p r A B

 

theorem stable_restriction_kernel : StableRestrictionKernelStatement.{u} := by
  intro k _ _ p _ _ r hr l hl A B f
  constructor
  · intro hf
    exact steinbergSpan_to_ideal k p r A B f.hom
      (tilting_projective_factor_mem_steinbergSpan k p r l hl hr A.obj B.obj
        A.property B.property f.hom hf)
  · exact steinbergIdeal_restricts_projectively k p r l hl A B f
end FiberFunctorProof

end OAI
