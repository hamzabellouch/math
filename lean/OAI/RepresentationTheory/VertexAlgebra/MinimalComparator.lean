import OAI.RepresentationTheory.VertexAlgebra.MainClauseOne

noncomputable section
universe u v w

namespace OAI.StronglyRationalVOA.HilbertCore
open Filter
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.space (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Submodule ℂ (Completion V) :=
  LinearMap.range (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.equiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V ≃ₗ[ℂ] (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.space V) :=
  LinearEquiv.ofInjective (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap
    (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.operator (T : V →ₗ[ℂ] Completion V) : Completion V →ₗ.[ℂ] Completion V where
  domain := (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.space V)
  toFun := T.comp (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.equiv V).symm.toLinearMap

end OAI.StronglyRationalVOA.HilbertCore

namespace OAI.StronglyRationalVOA.SmoothCircleFunction
open Filter
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.coefficient (f : OAI.StronglyRationalVOA.SmoothCircleFunction) (n : ℤ) : ℂ := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleFunction_period_pos  : 0 < 2*Real.pi := by positivity
  exact
    fourierCoeffOn h_OAI_StronglyRationalVOA_SmoothCircleFunction_period_pos f n

end OAI.StronglyRationalVOA.SmoothCircleFunction

namespace OAI.StronglyRationalVOA.ClosedGraphData
open Filter
open scoped ContDiff
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable abbrev _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double (H : Type u) := WithLp 2 (H × H)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph (T : H →ₗ.[ℂ] H) : Submodule ℂ (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) :=
  T.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toLinearEquiv.toLinearMap

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.projection (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) : (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) →L[ℂ] (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) := by
  classical
  have h_OAI_StronglyRationalVOA_ClosedGraphData_graph_closed {H : Type u} [instLocal1 : NormedAddCommGroup H] [instLocal2 : InnerProductSpace ℂ H]  {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
      IsClosed ((OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph T) : Set (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H)) :=
    hT.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).continuous
  letI : IsClosed ((OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph T) : Set (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H)) := (h_OAI_StronglyRationalVOA_ClosedGraphData_graph_closed hT)
  exact (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.graph T).starProjection

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.inclusion (i : Bool) : H →L[ℂ] (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (if i then ContinuousLinearMap.inr ℂ H H else ContinuousLinearMap.inl ℂ H H)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.coordinate (i : Bool) : (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.Double H) →L[ℂ] H :=
  (if i then ContinuousLinearMap.snd ℂ H H else ContinuousLinearMap.fst ℂ H H).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.entry (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) : H →L[ℂ] H :=
  (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.coordinate i).comp ((OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.projection T hT).comp (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.inclusion j))

end OAI.StronglyRationalVOA.ClosedGraphData

namespace OAI.StronglyRationalVOA.LocalOperatorAlgebra
open Filter
open scoped ContDiff
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open scoped Pointwise

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.LocalOperatorAlgebra.generated (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
        (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]

end OAI.StronglyRationalVOA.LocalOperatorAlgebra

namespace OAI.StronglyRationalVOA.SmoothCircleFunction
open Filter
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.onCircle (f : OAI.StronglyRationalVOA.SmoothCircleFunction) : AddCircle (2*Real.pi) → ℂ :=
  f.periodic.lift

end OAI.StronglyRationalVOA.SmoothCircleFunction

namespace OAI.StronglyRationalVOA.ProperCircleArc
open Filter
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier (I : OAI.StronglyRationalVOA.ProperCircleArc) : Set (AddCircle (2*Real.pi)) :=
  (fun t : ℝ => (t : AddCircle (2*Real.pi))) '' Set.Ioo I.left I.right

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.complement (I : OAI.StronglyRationalVOA.ProperCircleArc) : OAI.StronglyRationalVOA.ProperCircleArc where
  left := I.right
  right := I.left + 2*Real.pi
  nonempty' := I.nondense'
  nondense' := by linarith [I.nonempty']

end OAI.StronglyRationalVOA.ProperCircleArc

namespace OAI.StronglyRationalVOA.BoundedFlow
open scoped Topology
open Filter
open scoped Topology
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.BoundedFlow.boundedFlowRationalNormedAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) :=
  .restrictScalars ℚ ℂ (H →L[ℂ] H)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.BoundedFlow.flow (K : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := NormedSpace.exp (t • K)

end OAI.StronglyRationalVOA.BoundedFlow

namespace OAI.StronglyRationalVOA.SmoothCircleLift
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity : OAI.StronglyRationalVOA.SmoothCircleLift where
  toOrderIso := OrderIso.refl ℝ
  smooth := contDiff_id
  inverse_smooth := contDiff_id
  period := fun _ => rfl

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose (F G : OAI.StronglyRationalVOA.SmoothCircleLift) : OAI.StronglyRationalVOA.SmoothCircleLift where
  toOrderIso := G.toOrderIso.trans F.toOrderIso
  smooth := F.smooth.comp G.smooth
  inverse_smooth := G.inverse_smooth.comp F.inverse_smooth
  period := by intro t; change F (G (t+2*Real.pi))=F (G t)+2*Real.pi; rw [G.period,F.period]

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse (F : OAI.StronglyRationalVOA.SmoothCircleLift) : OAI.StronglyRationalVOA.SmoothCircleLift where
  toOrderIso := F.toOrderIso.symm
  smooth := F.inverse_smooth
  inverse_smooth := F.smooth
  period := by
    intro t
    apply F.toOrderIso.injective
    rw [F.toOrderIso.apply_symm_apply,F.period,F.toOrderIso.apply_symm_apply]

noncomputable instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup : Group OAI.StronglyRationalVOA.SmoothCircleLift := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_ext  {F G : OAI.StronglyRationalVOA.SmoothCircleLift} (h : ∀ t, F t=G t) : F=G := by
    cases F with
    | mk f hf hfi hp =>
      cases G with
      | mk g hg hgi hgp =>
        have he : f=g := DFunLike.ext _ _ h
        subst g
        rfl
  exact {
    mul := OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose
    one := OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity
    inv := OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse
    npow := @npowRec OAI.StronglyRationalVOA.SmoothCircleLift
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity⟩
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose⟩
    div := fun F G => OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose F
      (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse G)
    zpow := @zpowRec OAI.StronglyRationalVOA.SmoothCircleLift
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity⟩
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose⟩
      ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.inverse⟩
      (@npowRec OAI.StronglyRationalVOA.SmoothCircleLift
        ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.identity⟩
        ⟨OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.compose⟩)
    mul_assoc F G H := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; rfl
    one_mul F := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; rfl
    mul_one F := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; rfl
    inv_mul_cancel F := by apply h_OAI_StronglyRationalVOA_SmoothCircleLift_ext; intro t; exact F.toOrderIso.symm_apply_apply t
  }

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle (F : OAI.StronglyRationalVOA.SmoothCircleLift) : AddCircle (2*Real.pi) → AddCircle (2*Real.pi) := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply  (t : ℝ) : (1 : OAI.StronglyRationalVOA.SmoothCircleLift) t=t := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_circle_periodic  (F : OAI.StronglyRationalVOA.SmoothCircleLift) : Function.Periodic (fun t : ℝ => (F t : AddCircle (2*Real.pi))) (2*Real.pi) := by
    intro t
    change ((F.toOrderIso (t+2*Real.pi) : ℝ) : AddCircle (2*Real.pi)) =
      (F.toOrderIso t : AddCircle (2*Real.pi))
    rw [F.period,AddCircle.coe_add]
    simp
  exact
    (h_OAI_StronglyRationalVOA_SmoothCircleLift_circle_periodic F).lift

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleHomeomorph (F : OAI.StronglyRationalVOA.SmoothCircleLift) :
    AddCircle (2*Real.pi) ≃ₜ AddCircle (2*Real.pi) := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply  (t : ℝ) : (1 : OAI.StronglyRationalVOA.SmoothCircleLift) t=t := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one  (t : AddCircle (2*Real.pi)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle 1 t)=t := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : AddCircle (2*Real.pi)) :
      (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle (F * G) t)=(OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle G t)) := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_inverse  (F : OAI.StronglyRationalVOA.SmoothCircleLift) (t : AddCircle (2*Real.pi)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F⁻¹ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F t))=t := by
    rw [← h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul,inv_mul_cancel,h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one]
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_continuous_onCircle  (F : OAI.StronglyRationalVOA.SmoothCircleLift) : Continuous (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F) := by
    exact ((AddCircle.continuous_mk' (2*Real.pi)).comp F.smooth.continuous).quotient_liftOn' _
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
  exact {
    toFun := (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F)
    invFun := (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F⁻¹)
    left_inv := (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_inverse F)
    right_inv := by intro t; simpa [h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply, h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply] using (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_inverse F⁻¹ t)
    continuous_toFun := (h_OAI_StronglyRationalVOA_SmoothCircleLift_continuous_onCircle F)
    continuous_invFun := (h_OAI_StronglyRationalVOA_SmoothCircleLift_continuous_onCircle F⁻¹)
  }

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction : OAI.StronglyRationalVOA.SmoothCircleLift →* Equiv.Perm (AddCircle (2*Real.pi)) := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one  (t : AddCircle (2*Real.pi)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle 1 t)=t := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : AddCircle (2*Real.pi)) :
      (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle (F * G) t)=(OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle F (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.onCircle G t)) := by
    induction t using QuotientAddGroup.induction_on with
    | H t => rfl
  exact {
    toFun F := (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleHomeomorph F).toEquiv
    map_one' := by ext x; exact (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_one x)
    map_mul' F G := by ext x; exact (h_OAI_StronglyRationalVOA_SmoothCircleLift_onCircle_mul F G x)
  }

end OAI.StronglyRationalVOA.SmoothCircleLift

namespace OAI.StronglyRationalVOA
open scoped ContDiff

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism := OAI.StronglyRationalVOA.SmoothCircleLift ⧸ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker

noncomputable instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.instGroupSmoothCircleDiffeomorphism : Group OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism := inferInstanceAs
  (Group (OAI.StronglyRationalVOA.SmoothCircleLift ⧸ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker))

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA
open UniformSpace Filter Set
open scoped Topology

noncomputable instance _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.instTopologicalSpaceSmoothCircleDiffeomorphism : TopologicalSpace OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism := inferInstanceAs
  (TopologicalSpace (OAI.StronglyRationalVOA.SmoothCircleLift ⧸ (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker))

end OAI.StronglyRationalVOA

namespace OAI.StronglyRationalVOA.CircleMobiusGeometry
open Set
open scoped MatrixGroups

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel (M : SL(2,ℝ)) (x y : ℝ) : Prop :=
  (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))*Real.sin (y/2)=
    (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))*Real.cos (y/2)

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements (M : SL(2,ℝ)) (F : OAI.StronglyRationalVOA.SmoothCircleLift) : Prop := ∀ x, (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel M x ((OAI.StronglyRationalVOA.SmoothCircleLift.toOrderIso F) x))

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts : Subgroup OAI.StronglyRationalVOA.SmoothCircleLift := by
  classical
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply  (t : ℝ) : (1 : OAI.StronglyRationalVOA.SmoothCircleLift) t=t := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply  (F G : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
  have h_OAI_StronglyRationalVOA_SmoothCircleLift_apply_inv_apply  (F : OAI.StronglyRationalVOA.SmoothCircleLift) (t : ℝ) : F (F⁻¹ t)=t := F.toOrderIso.apply_symm_apply t
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_inv  {M : SL(2,ℝ)} {F : OAI.StronglyRationalVOA.SmoothCircleLift}
      (hF : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M⁻¹ F⁻¹) := by
    intro x
    have h := hF (F⁻¹ x)
    rw [OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,(h_OAI_StronglyRationalVOA_SmoothCircleLift_apply_inv_apply F)] at h
    simp only [OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,Matrix.SpecialLinearGroup.SL2_inv_expl,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
    linear_combination -h
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_one  : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements 1 1) := by
    intro x
    simp [h_OAI_StronglyRationalVOA_SmoothCircleLift_one_apply, OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,mul_comm]
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_collinear_unit  {p q c s : ℝ} (hu : c^2+s^2=1) (h : p*s=q*c) :
      (p*c+q*s)*c=p ∧ (p*c+q*s)*s=q := by
    constructor
    · linear_combination p*hu-s*h
    · linear_combination q*hu+c*h
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq  (x : ℝ) : Real.cos x^2+Real.sin x^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_mul  {M N : SL(2,ℝ)} {F G : OAI.StronglyRationalVOA.SmoothCircleLift}
      (hF : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F)) (hG : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements N G)) : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements (M * N) (F * G)) := by
    intro x
    have hh := hF (G x)
    have hg := hG x
    obtain ⟨hr1,hr2⟩ := (h_OAI_StronglyRationalVOA_CircleMobiusGeometry_collinear_unit
    (h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq
      ((OAI.StronglyRationalVOA.SmoothCircleLift.toOrderIso G) x / 2))
    hg)
    let r := (N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2))*Real.cos (G x/2)+
      (N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2))*Real.sin (G x/2)
    change r*Real.cos (G x/2)=N 0 0*Real.cos (x/2)+N 0 1*Real.sin (x/2) at hr1
    change r*Real.sin (G x/2)=N 1 0*Real.cos (x/2)+N 1 1*Real.sin (x/2) at hr2
    change (M 0 0*Real.cos (G x/2)+M 0 1*Real.sin (G x/2))*Real.sin (F (G x)/2)=
      (M 1 0*Real.cos (G x/2)+M 1 1*Real.sin (G x/2))*Real.cos (F (G x)/2) at hh
    simp only [OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Rel,(h_OAI_StronglyRationalVOA_SmoothCircleLift_mul_apply),Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
    linear_combination r*hh+(M 1 0*Real.cos (F (G x)/2)-M 0 0*Real.sin (F (G x)/2))*hr1+
      (M 1 1*Real.cos (F (G x)/2)-M 0 1*Real.sin (F (G x)/2))*hr2
  exact {
    carrier := {F | ∃ M : SL(2,ℝ), (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F)}
    one_mem' := ⟨1,h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_one⟩
    mul_mem' := by rintro F G ⟨M,hM⟩ ⟨N,hN⟩; exact ⟨M*N,(h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_mul hM hN)⟩
    inv_mem' := by rintro F ⟨M,hM⟩; exact ⟨M⁻¹,(h_OAI_StronglyRationalVOA_CircleMobiusGeometry_implements_inv hM)⟩
  }

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.rotationMatrix (s : ℝ) : SL(2,ℝ) := by
  classical
  have h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq  (x : ℝ) : Real.cos x^2+Real.sin x^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  exact
    ⟨!![Real.cos (s/2),-Real.sin (s/2);Real.sin (s/2),Real.cos (s/2)],by
        simp only [Matrix.det_fin_two_of]
        nlinarith [(h_OAI_StronglyRationalVOA_CircleMobiusGeometry_cos_sq_add_sin_sq (s / 2))]⟩

noncomputable abbrev _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group := OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts ⧸ ((OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).comp OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts.subtype).ker

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.inclusion : OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group →* OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism :=
  QuotientGroup.lift ((OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).comp OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts.subtype).ker
    ((QuotientGroup.mk' (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker).comp OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts.subtype) (by
      intro F hF
      exact (QuotientGroup.eq_one_iff _).mpr hF)

end OAI.StronglyRationalVOA.CircleMobiusGeometry

namespace OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism
open Set
open scoped Topology MatrixGroups

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism.action : OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism →* Equiv.Perm (AddCircle (2*Real.pi)) :=
  QuotientGroup.lift (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction).ker (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.circleAction)
    (fun _ h => h)

end OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism

namespace OAI.StronglyRationalVOA
open Set
open scoped Topology MatrixGroups

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.projectiveConjugation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : OAI.StronglyRationalVOA.ProjectiveUnitaryGroup H → ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := by
  classical
  have h_OAI_StronglyRationalVOA_projective_equality_conjugation  {H : Type _} [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (E F : H ≃ₗᵢ[ℂ] H)
      (h : (QuotientGroup.mk E : OAI.StronglyRationalVOA.ProjectiveUnitaryGroup H)=QuotientGroup.mk F) :
      E.conjStarAlgEquiv=F.conjStarAlgEquiv := by
    obtain ⟨c,_,hc⟩ := QuotientGroup.eq.mp h
    have he (x : H) : F x=c • E x := by
      have H := congrArg E (hc x)
      change E (E.symm (F x))=E (c • x) at H
      simpa only [E.apply_symm_apply,map_smul] using H
    ext B x
    change E (B (E.symm x))=F (B (F.symm x))
    have hi : E.symm x=c • F.symm x := by
      apply E.injective
      rw [E.apply_symm_apply,map_smul,← he,F.apply_symm_apply]
    rw [hi,map_smul,map_smul,← he]
  exact
    Quotient.lift (fun E : H ≃ₗᵢ[ℂ] H => E.conjStarAlgEquiv) (by
        intro E F h
        exact (h_OAI_StronglyRationalVOA_projective_equality_conjugation E F (Quotient.sound h)))

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.globalObservableAlgebra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : OAI.StronglyRationalVOA.ProperCircleArc → VonNeumannAlgebra H) :
    Subalgebra ℂ (H →L[ℂ] H) :=
  Algebra.adjoin ℂ (⋃ I, (N I : Set (H →L[ℂ] H)))

noncomputable def _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.globalCyclicSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : OAI.StronglyRationalVOA.ProperCircleArc → VonNeumannAlgebra H) (Ω : H) : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ B ∈ (OAI.MinimalVertex.Code.StronglyRationalVOA.globalObservableAlgebra N), x=B Ω}).topologicalClosure

end OAI.StronglyRationalVOA

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V}

noncomputable def smearedMap (A : OAI.StronglyRationalVOA.CFTTypeVOA V) (a : V) (d : ℕ) (_ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (_hf : OAI.StronglyRationalVOA.RapidCoefficients f) : V →ₗ[ℂ] Completion V := by
  classical
  let family : ℤ → (V →ₗ[ℂ] Completion V) := fun m =>
    f m • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      (A.physicalMode a d m)
  exact if h : ∀ v, Summable (fun m => family m v) then
    SummableLinearFamily.tsumMap family h
  else 0

noncomputable def smoothSmearedField (_U : A.UnitaryStructure) (_hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : OAI.StronglyRationalVOA.SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V := by
  classical
  exact if h : A.PolynomialEnergyBounds ∧ OAI.StronglyRationalVOA.RapidCoefficients (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.coefficient f) then
    (OAI.MinimalVertex.Code.StronglyRationalVOA.HilbertCore.operator
  (OAI.MinimalVertex.smearedMap A a d (And.left h a) (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.coefficient f)
    (And.right h)))
  else 0

noncomputable def closedSmoothField (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : OAI.StronglyRationalVOA.SmoothCircleFunction) : Completion V →ₗ.[ℂ] Completion V :=
  (OAI.MinimalVertex.smoothSmearedField U hc a d f).closure

noncomputable def localGraphData (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : Set (Completion V →L[ℂ] Completion V) :=
  {x | ∃ (a : V) (d : ℕ), a ∈ A.grade d ∧ ∃ (f : OAI.StronglyRationalVOA.SmoothCircleFunction),
      tsupport (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleFunction.onCircle f) ⊆ O ∧ ∃ (h : (OAI.MinimalVertex.closedSmoothField U hc a d f).IsClosed),
        ∃ i j : Bool, x = (OAI.MinimalVertex.Code.StronglyRationalVOA.ClosedGraphData.entry (OAI.MinimalVertex.closedSmoothField U hc a d f) h i j)}

noncomputable def localAlgebra (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : VonNeumannAlgebra (Completion V) :=
  (OAI.MinimalVertex.Code.StronglyRationalVOA.LocalOperatorAlgebra.generated (OAI.MinimalVertex.localGraphData U hc O))

noncomputable def intervalAlgebra (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (I : OAI.StronglyRationalVOA.ProperCircleArc) : VonNeumannAlgebra (Completion V) :=
  OAI.MinimalVertex.localAlgebra U hc (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I)

noncomputable def CKLWStrongLocal (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  (∀ a : V, A.PolynomialEnergyBound a) ∧
    ∀ I : OAI.StronglyRationalVOA.ProperCircleArc, OAI.MinimalVertex.intervalAlgebra U hc I ≤
      (OAI.MinimalVertex.intervalAlgebra U hc (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.complement I)).commutant

end OAI.MinimalVertex

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def resolvent (T : H →ₗ.[ℂ] H) (_hs : IsSelfAdjoint T) (z : ℂ) (_hz : 1 ≤ |z.im|) :
    H →L[ℂ] H := by
  classical
  exact if h : ∃ R : H →L[ℂ] H, ∀ y, (R y, y + z • R y) ∈ T.graph then h.choose
  else 0

noncomputable def boundedGenerator (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : H →L[ℂ] H :=
  ((r : ℂ)^2/2) •
    (OAI.MinimalVertex.resolvent T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr) +
     OAI.MinimalVertex.resolvent T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr))

noncomputable def approximatingFlow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (n : ℕ) (t : ℝ) : H →L[ℂ] H :=
  (OAI.MinimalVertex.Code.StronglyRationalVOA.BoundedFlow.flow
  (Complex.I • OAI.MinimalVertex.boundedGenerator T hs (↑n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))) t)

end OAI.MinimalVertex

namespace OAI.MinimalVertex
open Filter Set UniformSpace
open scoped Topology MatrixGroups
open StronglyRationalVOA

noncomputable def flow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) : H →L[ℂ] H := by
  classical
  exact if h : ∃ L : H →L[ℂ] H, ∀ x,
      Tendsto (fun n => OAI.MinimalVertex.approximatingFlow T hs n t x) atTop (𝓝 (L x)) then
    h.choose
  else 0

noncomputable def projectiveStandardAction : PSL(2,ℝ) →* (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group) := by
  classical
  exact if h : ∃ L : PSL(2,ℝ) →* (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Group),
      ∀ M : SL(2,ℝ), ∃ F : OAI.StronglyRationalVOA.SmoothCircleLift, ∃ hF : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F),
        L (QuotientGroup.mk M) =
          QuotientGroup.mk (⟨F, M, hF⟩ : (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.lifts)) then h.choose
  else 1

structure IrreducibleConformalNetStructure {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : OAI.StronglyRationalVOA.ProperCircleArc → VonNeumannAlgebra H) where
  separable : TopologicalSpace.SeparableSpace H
  carrier_congr : ∀ I J, (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I)=(OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J) → N I=N J
  isotony : ∀ I J, (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I) ⊆ (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J) → N I ≤ N J
  locality : ∀ I J, Disjoint (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I) (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J) → N I ≤ (N J).commutant
  mobius : PSL(2,ℝ) →* (H ≃ₗᵢ[ℂ] H)
  mobius_continuous : Continuous mobius
  diffeomorphism : OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism →* OAI.StronglyRationalVOA.ProjectiveUnitaryGroup H
  diffeomorphism_continuous : Continuous diffeomorphism
  extends_mobius : ∀ F, diffeomorphism ((OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.inclusion) (OAI.MinimalVertex.projectiveStandardAction F))=QuotientGroup.mk (mobius F)
  covariance : ∀ F I J, (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier J)=(OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism.action) F '' (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I) →
    ∀ B : H →L[ℂ] H, OAI.MinimalVertex.Code.StronglyRationalVOA.projectiveConjugation (diffeomorphism F) B ∈ N J ↔ B ∈ N I
  local_action : ∀ F I, (∀ x ∈ (OAI.MinimalVertex.Code.StronglyRationalVOA.ProperCircleArc.carrier I), (OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleDiffeomorphism.action) F x=x) →
    ∀ B ∈ N I, OAI.MinimalVertex.Code.StronglyRationalVOA.projectiveConjugation (diffeomorphism F) B=B
  vacuum : H
  vacuum_norm : ‖vacuum‖=1
  vacuum_invariant : ∀ F, mobius F vacuum=vacuum
  vacuum_unique : ∀ x : H, (∀ F, mobius F x=x) → ∃ c : ℂ, x=c • vacuum
  vacuum_cyclic : (OAI.MinimalVertex.Code.StronglyRationalVOA.globalCyclicSpace N vacuum)=⊤
  hamiltonian : H →ₗ.[ℂ] H
  hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian
  positive_energy : ∀ x y, (x,y) ∈ hamiltonian.graph → 0 ≤ (inner ℂ x y).re
  rotation_flow : ∀ t : ℝ,
    (mobius (QuotientGroup.mk (OAI.MinimalVertex.Code.StronglyRationalVOA.CircleMobiusGeometry.rotationMatrix t))).toLinearIsometry.toContinuousLinearMap=
      OAI.MinimalVertex.flow hamiltonian hamiltonian_selfAdjoint t
  irreducible : ∀ Q : H →L[ℂ] H, (∀ I, Q ∈ (N I).commutant) →
    ∃ c : ℂ, Q=c • (1 : H →L[ℂ] H)

end OAI.MinimalVertex

end


noncomputable section
open Filter Set UniformSpace
open scoped Topology MatrixGroups
universe u v
namespace OAI.MinimalVertex
open StronglyRationalVOA

theorem cloned_entry_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) :
    Code.StronglyRationalVOA.ClosedGraphData.entry T hT i j = ClosedGraphData.entry T hT i j := by
  rfl

section Fields
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V}

theorem smearedMap_eq (A : CFTTypeVOA V) (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) :
    smearedMap A a d ha f hf = A.smearedMap a d ha f hf := by
  have h : ∀ v, Summable (fun m =>
      (f m • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
        (A.physicalMode a d m)) v) :=
    fun v => (A.summable_norm_physicalSmear ha d hf v).of_norm
  simp only [smearedMap, dite_eq_left h]
  rfl

theorem smoothSmearedField_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) :
    smoothSmearedField U hc a d f = U.smoothSmearedField hc a d f := by
  rw [smoothSmearedField, dite_eq_left ⟨U.polynomialEnergyBounds hc, f.rapid_coefficients⟩, smearedMap_eq]
  rfl

theorem closedSmoothField_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) :
    closedSmoothField U hc a d f = U.closedSmoothField hc a d f := by
  rw [closedSmoothField, smoothSmearedField_eq]
  rfl

theorem localGraphData_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : localGraphData U hc O = U.localGraphData hc O := by
  ext x
  simp only [localGraphData, CFTTypeVOA.UnitaryStructure.localGraphData, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, d, ha, f, hf, h, i, j, hx⟩
    refine ⟨a, d, ha, f, hf, i, j, ?_⟩
    simpa only [closedSmoothField_eq, cloned_entry_eq] using hx
  · rintro ⟨a, d, ha, f, hf, i, j, hx⟩
    have h : (closedSmoothField U hc a d f).IsClosed := by
      rw [closedSmoothField_eq]
      exact U.closedSmoothField_isClosed hc ha f
    refine ⟨a, d, ha, f, hf, h, i, j, ?_⟩
    simpa only [closedSmoothField_eq, cloned_entry_eq] using hx

theorem intervalAlgebra_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite) :
    intervalAlgebra U hc = U.intervalAlgebra hc := by
  funext I
  unfold intervalAlgebra localAlgebra CFTTypeVOA.UnitaryStructure.intervalAlgebra
    CFTTypeVOA.UnitaryStructure.localAlgebra
  rw [localGraphData_eq]
  rfl

theorem CKLWStrongLocal_eq (U : A.UnitaryStructure) (hc : A.toVertexAlgebra.C2Cofinite) :
    CKLWStrongLocal U hc = U.CKLWStrongLocal hc := by
  unfold CKLWStrongLocal CFTTypeVOA.UnitaryStructure.CKLWStrongLocal
  rw [intervalAlgebra_eq]
  rfl
end Fields

section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_eq (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) :
    resolvent T hs z hz = SymmetricOperator.resolvent T hs z hz := by
  have h : ∃ R : H →L[ℂ] H, ∀ y, (R y, y + z • R y) ∈ T.graph :=
    ⟨SymmetricOperator.resolvent T hs z hz, SymmetricOperator.resolvent_graph T hs z hz⟩
  rw [resolvent, dite_eq_left h]
  ext y
  have he := SymmetricOperator.resolvent_on_graph T hs z hz (h.choose_spec y)
  rw [map_add, map_smul] at he
  exact (add_right_cancel he).symm

theorem boundedGenerator_eq (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) :
    boundedGenerator T hs r hr = SymmetricOperator.boundedGenerator T hs r hr := by
  unfold boundedGenerator SymmetricOperator.boundedGenerator
  simp only [resolvent_eq]

theorem approximatingFlow_eq (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (n : ℕ) (t : ℝ) :
    approximatingFlow T hs n t = SymmetricOperator.approximatingFlow T hs n t := by
  unfold approximatingFlow SymmetricOperator.approximatingFlow
  rw [boundedGenerator_eq]
  rfl

end Operators

theorem flow_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    flow T hs t = SymmetricOperator.flow T hs t := by
  have h : ∃ L : H →L[ℂ] H, ∀ x,
      Tendsto (fun n => approximatingFlow T hs n t x) atTop (𝓝 (L x)) := by
    simpa only [approximatingFlow_eq] using SymmetricOperator.exists_flow_limit T hs t
  rw [flow, dite_eq_left h]
  ext x
  have he : (fun n => approximatingFlow T hs n t x) =
      (fun n => SymmetricOperator.approximatingFlow T hs n t x) := by
    funext n
    rw [approximatingFlow_eq]
  have hx := (congrArg (fun f : ℕ → H => Tendsto f atTop (𝓝 (h.choose x))) he).mp
    (h.choose_spec x)
  exact tendsto_nhds_unique hx ((SymmetricOperator.exists_flow_limit T hs t).choose_spec x)

theorem projectiveStandardAction_eq :
    projectiveStandardAction = CircleMobiusGeometry.projectiveStandardAction := by
  have h : ∃ L : PSL(2,ℝ) →* Code.StronglyRationalVOA.CircleMobiusGeometry.Group,
      ∀ M : SL(2,ℝ), ∃ F : SmoothCircleLift, ∃ hF : Code.StronglyRationalVOA.CircleMobiusGeometry.Implements M F,
        L (QuotientGroup.mk M) =
          QuotientGroup.mk (⟨F, M, hF⟩ : Code.StronglyRationalVOA.CircleMobiusGeometry.lifts) := by
    refine ⟨CircleMobiusGeometry.projectiveStandardAction, ?_⟩
    intro M
    obtain ⟨F, hF⟩ := CircleMobiusGeometry.exists_implements M
    exact ⟨F, hF, CircleMobiusGeometry.standardAction_eq_mk hF⟩
  rw [projectiveStandardAction, dite_eq_left h]
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H M =>
    obtain ⟨F, hF, hM⟩ := h.choose_spec M
    exact hM.trans (CircleMobiusGeometry.standardAction_eq_mk hF).symm

theorem netStructure_of_original {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : ProperCircleArc → VonNeumannAlgebra H}
    (net : StronglyRationalVOA.IrreducibleConformalNetStructure N) :
    Nonempty (IrreducibleConformalNetStructure N) := by
  refine ⟨{
    separable := net.separable
    carrier_congr := net.carrier_congr
    isotony := net.isotony
    locality := net.locality
    mobius := net.mobius
    mobius_continuous := net.mobius_continuous
    diffeomorphism := net.diffeomorphism
    diffeomorphism_continuous := net.diffeomorphism_continuous
    extends_mobius := by
      intro F
      rw [projectiveStandardAction_eq]
      exact net.extends_mobius F
    covariance := net.covariance
    local_action := net.local_action
    vacuum := net.vacuum
    vacuum_norm := net.vacuum_norm
    vacuum_invariant := net.vacuum_invariant
    vacuum_unique := net.vacuum_unique
    vacuum_cyclic := net.vacuum_cyclic
    hamiltonian := net.hamiltonian
    hamiltonian_selfAdjoint := net.hamiltonian_selfAdjoint
    positive_energy := net.positive_energy
    rotation_flow := ?_
    irreducible := net.irreducible
  }⟩
  intro t
  rw [flow_eq]
  exact net.rotation_flow t

theorem main {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)
    (hSimple : A.toVertexAlgebra.IsSimple) (hSR : A.IsStronglyRational.{u,v}) :
    A.PolynomialEnergyBounds ∧ CKLWStrongLocal U hSR.2.2 ∧
      Nonempty (IrreducibleConformalNetStructure (intervalAlgebra U hSR.2.2)) := by
  have h := U.source_main_clause_one hSimple hSR
  refine ⟨h.1, ?_, ?_⟩
  · rw [CKLWStrongLocal_eq]
    exact h.2.1
  · rw [intervalAlgebra_eq]
    exact netStructure_of_original h.2.2.some

end OAI.MinimalVertex

end
