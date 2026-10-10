import OAI.RepresentationTheory.RowColumn.CopyOverlap
import OAI.RepresentationTheory.RowColumn.Sectors

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState

 theorem exists_hook_isometry (a : YoungDiagram) (h : ℕ) (H : InHook a h) :
    ∃ K : hilbertSpace a →ₗᵢ[ℂ] Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H),
      ∀ g x, K (unitaryRepresentation a g x) = HookModel.hookRepresentation a h H g (K x) := by

  let := unitaryRepresentation_irreducible a

  let f : Representation.IntertwiningMap (unitaryRepresentation a) (HookModel.hookRepresentation a h H) :=
    (HookModel.hookEmbedding a h H).comp (unitaryEquiv a).symm.toIntertwiningMap

  have hf : Function.Injective f := by
    intro x y hxy
    apply (spaceHilbertEquiv a).symm.injective
    apply HookModel.hookEmbedding_injective a h H
    exact hxy

  have hu : IsUnitary (V := Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H)) (HookModel.hookRepresentation a h H) :=
    Signed.representation_unitary (S := Cell a) (odd := HookModel.IsOdd (h := h)) (k := HookModel.oddCount a h H)

  have hh := @isometric_intertwiner_of_injective
    (Equiv.Perm (Cell a)) (hilbertSpace a)
    (Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (unitaryRepresentation a) (HookModel.hookRepresentation a h H)
    (unitaryRepresentation_unitary a) hu (unitaryRepresentation_irreducible a) f hf

  exact hh

section LineCopy
variable {S L V : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {u : ℕ} (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h)
    (K : hilbertSpace a →ₗᵢ[ℂ] Sector (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))
    (hK : ∀ g x, K (unitaryRepresentation a g x) = HookModel.hookRepresentation a h H g (K x))
    (line : S → L) (ρ : Representation ℂ (lineGroup line) V) (hρ : IsUnitary ρ)
    (I : Fin u → V →ₗᵢ[ℂ] hilbertSpace a)
    (hI : ∀ i, Intertwines (V := V) (W := hilbertSpace a) ρ ((relabelledUnitary a e).comp (lineGroup line).subtype) (I i).toLinearMap)

include hK hρ hI in
omit [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L] in
lemma hook_copy_projection_intertwines :
    Intertwines (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h))
      (k := HookModel.oddCount a h H) (line ∘ e.symm))
      (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h))
        (k := HookModel.oddCount a h H) (line ∘ e.symm))
      (copyProjection (fun i => K.comp (I i))).toLinearMap := by
  let τ := hookLineTarget line a e h H
  have hKI : ∀ i, Intertwines ρ τ (K.comp (I i)).toLinearMap := by
    intro i g x
    change K (I i (ρ g x)) = HookModel.hookRepresentation a h H (e.permCongr g.1) (K (I i x))
    have hi : I i (ρ g x)=unitaryRepresentation a (e.permCongr g.1) (I i x) := hI i g x
    rw [hi]
    exact hK (e.permCongr g.1) _
  have hp := copyProjection_intertwines ρ τ hρ
    (fun g => Signed.representation_unitary (e.permCongr g.1)) (fun i => K.comp (I i)) hKI
  intro g x
  have hh := hp ((lineGroupCongr e line).symm g) x
  change copyProjection (fun i => K.comp (I i))
    (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h)) (k := HookModel.oddCount a h H)
      (line ∘ e.symm) ((lineGroupCongr e line) ((lineGroupCongr e line).symm g)) x) =
    Signed.lineRepresentation (odd := HookModel.IsOdd (h := h)) (k := HookModel.oddCount a h H)
      (line ∘ e.symm) ((lineGroupCongr e line) ((lineGroupCongr e line).symm g))
      (copyProjection (fun i => K.comp (I i)) x) at hh
  rw [MulEquiv.apply_symm_apply] at hh
  exact hh

end LineCopy

section Filter
variable {G V E X : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]

omit [FiniteDimensional ℂ X] in
lemma isotypic_filter_copy_projection (ρ : Representation ℂ G X) (τ : Representation ℂ G E)
    (K : X →ₗᵢ[ℂ] E) (hK : ∀ g x, K (ρ g x)=τ g (K x))
    (Q : E →L[ℂ] E) (hQ : ∀ x ∈ Isotypic.carrier ρ τ, Q x=x)
    {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X) :
    Q * copyProjection (fun i => K.comp (I i)) = copyProjection (fun i => K.comp (I i)) := by
  let f : Representation.IntertwiningMap ρ τ :=
    { toLinearMap := K.toLinearMap
      isIntertwining' g := by ext x; exact hK g x }
  have hk (x : X) : Q (K x)=K x := hQ _ (Isotypic.mem_carrier ρ τ f x)
  ext x
  simp only [mul_apply_eq_comp, copyProjection, sum_apply,
    map_sum, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.coe_comp, Function.comp_apply, hk]

end Filter
end RowColumn

end
end

end OAI
