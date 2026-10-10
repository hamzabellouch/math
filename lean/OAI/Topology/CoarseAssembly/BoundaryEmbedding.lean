import OAI.Topology.CoarseAssembly.InclusionModule
import OAI.Topology.CoarseAssembly.ConcreteSpaces

namespace OAI

/-! # The exact spatial boundary factorization

Boundary fibers have depth zero and are singletons. The normalized fiber
embedding therefore agrees exactly with the coordinate inclusion there,
which proves the operator factorization needed by assembly naturality.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

def BoundaryVertex := {u : BaseUnion // discDepth u.1 u.2 = 0}

noncomputable instance boundaryVertexDecidableEq : DecidableEq BoundaryVertex := Classical.decEq _

def boundaryToBase : BoundaryVertex ↪ BaseUnion := ⟨Subtype.val, Subtype.val_injective⟩

def boundaryToVertex : BoundaryVertex ↪ VertexUnion where
  toFun b := ⟨b.val, 1⟩
  inj' := by
    intro b c h
    apply Subtype.ext
    exact congrArg Sigma.fst h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundaryBaseIsometry : lp (fun _ : BoundaryVertex => H) 2 →ₗᵢ[ℂ]
    lp (fun _ : BaseUnion => H) 2 := inclusionIsometry boundaryToBase

def boundaryVertexIsometry : lp (fun _ : BoundaryVertex => H) 2 →ₗᵢ[ℂ]
    lp (fun _ : VertexUnion => H) 2 := inclusionIsometry boundaryToVertex

omit [CompleteSpace H] in
theorem fiberEmbedding_boundary :
    (fiberEmbedding (H := H) BaseFiber).comp boundaryBaseIsometry = boundaryVertexIsometry := by
  classical
  have he : (fiberEmbedding (H := H) BaseFiber).toContinuousLinearMap.comp
      (boundaryBaseIsometry.toContinuousLinearMap) =
      boundaryVertexIsometry.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro b
    apply ContinuousLinearMap.ext
    intro h
    change fiberEmbedding BaseFiber (inclusionIsometry boundaryToBase (lp.single 2 b h)) =
      inclusionIsometry boundaryToVertex (lp.single 2 b h)
    rw [inclusionIsometry_single, inclusionIsometry_single]
    have : Subsingleton (BaseFiber b.val) := by
      change Subsingleton (Quotient (discDepth b.val.1 b.val.2))
      rw [b.property]
      infer_instance
    exact fiberEmbedding_singleton BaseFiber b.val 1 h
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun he x

theorem boundary_operator_factorization
    (T : lp (fun _ : BoundaryVertex => H) 2 →L[ℂ] lp (fun _ : BoundaryVertex => H) 2) :
    operatorConjugation (fiberEmbedding BaseFiber) (operatorConjugation boundaryBaseIsometry T) =
      operatorConjugation boundaryVertexIsometry T := by
  rw [operatorConjugation_comp, fiberEmbedding_boundary]

end CoarseAssembly

end

end OAI
