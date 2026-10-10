import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsRealization
import OAI.Topology.CoarseAssembly.NonUnitalK1
import OAI.Topology.CoarseAssembly.RoeTransfer

namespace OAI

/-!
# Compatible analytic indices and their coarsening limit

The scale-index homomorphisms and their compatibility are the precise
published input from Willett--Yu, *Higher Index Theory*, §§5.1, 6.7, 7.1--7.2
(with errata 30--31). Their source is the Fredholm-module group of the actual
C₀ algebra; their target is the topological K₁ of the actual nonunital algebra.
The induced coarse map is constructed here by the universal property of the
direct limit. No geometric detection, filling or transfer conclusion is part
of this input.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u v

namespace CoarseningMorphism

variable {C D : Coarsening.{u}}

theorem pushforward_compatible (f : CoarseningMorphism C D) (r s : ℕ) (h : r ≤ s) :
    (pushforward (f.atScale s)).comp (C.map r s h) =
      (D.map r s h).comp (pushforward (f.atScale r)) := by
  change (pushforward (f.atScale s)).comp (pushforward (C.inclusion r s h)) =
    (pushforward (D.inclusion r s h)).comp (pushforward (f.atScale r))
  rw [← pushforward_comp, ← pushforward_comp, f.compatible]

def homologyMap (f : CoarseningMorphism C D) : C.Homology →+ D.Homology :=
  AddCommGroup.DirectLimit.map (fun r => pushforward (f.atScale r))
    f.pushforward_compatible

@[simp] theorem homologyMap_of (f : CoarseningMorphism C D) (r : ℕ)
    (a : LocallyFiniteK1 (C.space r)) :
    f.homologyMap (C.of r a) = D.of r (pushforward (f.atScale r) a) :=
  AddCommGroup.DirectLimit.map_apply_of _ _ _

end CoarseningMorphism

namespace CompatibleIndexFamily

variable {C D : Coarsening.{u}} {A B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

@[simp] theorem assembly_of (I : CompatibleIndexFamily C A) (r : ℕ)
    (a : LocallyFiniteK1 (C.space r)) : I.assembly (C.of r a) = I.atScale r a :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

/-- Scale-level analytic naturality passes to the actual coarsening limit. -/
theorem assembly_natural (I : CompatibleIndexFamily C A) (J : CompatibleIndexFamily D B)
    (f : CoarseningMorphism C D) (φ : A →⋆ₙₐ[ℂ] B)
    (hnat : ∀ r, (J.atScale r).comp (pushforward (f.atScale r)) =
      (OperatorKTheory.map φ).comp (I.atScale r)) :
    J.assembly.comp f.homologyMap = (OperatorKTheory.map φ).comp I.assembly := by
  apply AddCommGroup.DirectLimit.hom_ext
  intro r
  apply AddMonoidHom.ext
  intro a
  change J.assembly (f.homologyMap (C.of r a)) =
    OperatorKTheory.map φ (I.assembly (C.of r a))
  simp only [CoarseningMorphism.homologyMap_of, assembly_of]
  exact DFunLike.congr_fun (hnat r) a

end CompatibleIndexFamily

end CoarseAssembly.Analytic

end

end OAI
