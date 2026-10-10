import OAI.RepresentationTheory.RowColumn.HookModel

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn

section Retraction
variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

def algebraicAverage (A : V →ₗ[ℂ] W) : Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g, (σ g).comp (A.comp (ρ g⁻¹))
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
    intro g
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    have hh (w : W) : σ h (σ h⁻¹ w) = w := by
      change (σ h * σ h⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hh]

/-- Averaging an algebraic left inverse produces a genuine equivariant retraction.
Used to transfer the signed-slot commutant bound to the hook Specht module. -/
lemma intertwiner_has_retraction (L : Representation.IntertwiningMap ρ σ)
    (hL : Function.Injective L) :
    ∃ R : Representation.IntertwiningMap σ ρ, ∀ v, R (L v) = v := by
  obtain ⟨A, hA⟩ := L.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hL)
  refine ⟨(Fintype.card G : ℂ)⁻¹ • algebraicAverage A, ?_⟩
  intro v
  change (Fintype.card G : ℂ)⁻¹ • (∑ g, (ρ g).comp (A.comp (σ g⁻¹))) (L v) = v
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  have ha (g : G) : ρ g (A (σ g⁻¹ (L v))) = v := by
    rw [← Representation.IntertwiningMap.isIntertwining ρ σ L]
    have he : A (L (ρ g⁻¹ v)) = ρ g⁻¹ v :=
      LinearMap.congr_fun hA (ρ g⁻¹ v)
    rw [he]
    change (ρ g * ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  simp only [ha, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

def extendCommutant (L : Representation.IntertwiningMap ρ σ)
    (R : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ ρ →ₗ[ℂ] Representation.IntertwiningMap σ σ where
  toFun A := L.comp (A.comp R)
  map_add' A B := by ext v; simp
  map_smul' z A := by ext v; simp

omit [Fintype G] in
lemma extendCommutant_injective (L : Representation.IntertwiningMap ρ σ)
    (R : Representation.IntertwiningMap σ ρ) (hL : Function.Injective L)
    (hR : ∀ v, R (L v) = v) : Function.Injective (extendCommutant L R) := by
  intro A B h
  apply Representation.IntertwiningMap.ext
  ext v
  change A v = B v
  apply hL
  have he := congrArg (fun T : Representation.IntertwiningMap σ σ => T (L v)) h
  simpa only [extendCommutant, LinearMap.coe_mk, AddHom.coe_mk,
    Representation.IntertwiningMap.comp_apply, hR] using he

lemma commutant_finrank_le_of_embedding [FiniteDimensional ℂ W]
    (L : Representation.IntertwiningMap ρ σ) (hL : Function.Injective L) :
    Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) ≤
      Module.finrank ℂ (Representation.IntertwiningMap σ σ) := by
  obtain ⟨R, hR⟩ := intertwiner_has_retraction L hL
  exact LinearMap.finrank_le_finrank_of_injective (f := extendCommutant L R)
    (extendCommutant_injective L R hL hR)

end Retraction
end RowColumn
namespace RowColumn
open scoped BigOperators Classical
open CubeShuffle.UnitaryFinite

section CopyCount
variable {G V X : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G X}
  {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X)

lemma adjoint_intertwines (A : V →ₗ[ℂ] X) (hA : Intertwines ρ τ A)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ) :
    Intertwines τ ρ A.toContinuousLinearMap.adjoint.toLinearMap := by
  intro g x
  apply ext_inner_left ℂ
  intro v
  change inner ℂ v (A.toContinuousLinearMap.adjoint (τ g x)) =
    inner ℂ v (ρ g (A.toContinuousLinearMap.adjoint x))
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← inv_inv g, unitary_inner_inv ρ hρ, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (A v) (τ (g⁻¹)⁻¹ x) = inner ℂ (A (ρ g⁻¹ v)) x
  rw [hA, unitary_inner_inv τ hτ]

def copyIdempotent (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ) (i : Fin u) :
    Representation.IntertwiningMap τ τ where
  toLinearMap := (I i).toLinearMap.comp (I i).toContinuousLinearMap.adjoint.toLinearMap
  isIntertwining' g := by
    ext x
    change I i ((I i).toContinuousLinearMap.adjoint (τ g x)) =
      τ g (I i ((I i).toContinuousLinearMap.adjoint x))
    rw [show (I i).toContinuousLinearMap.adjoint (τ g x) =
      ρ g ((I i).toContinuousLinearMap.adjoint x) from
      adjoint_intertwines (I i).toLinearMap (hI i) hρ hτ g x]
    exact hI i g _

lemma adjoint_copy_apply (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0)
    (i j : Fin u) (v : V) :
    (I i).toContinuousLinearMap.adjoint (I j v) = if i = j then v else 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  by_cases he : i = j
  · subst j
    simp [LinearIsometry.inner_map_map]
  · simp only [ite_eq_right he, inner_zero_right, LinearIsometry.coe_toContinuousLinearMap]
    exact ho i j he w v

lemma copyIdempotent_apply (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0)
    (i j : Fin u) (v : V) :
    copyIdempotent I hI hρ hτ i (I j v) = if i = j then I j v else 0 := by
  change I i ((I i).toContinuousLinearMap.adjoint (I j v)) = _
  rw [adjoint_copy_apply I ho]
  split_ifs with he
  · subst j; rfl
  · exact map_zero _

/-- Orthogonal nonzero copies supply linearly independent elements of the
commutant by their actual range projections. -/
lemma copyIdempotent_independent [Nontrivial V]
    (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0) :
    LinearIndependent ℂ (copyIdempotent I hI hρ hτ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rw [linearIndependent_iff']
  intro s z hz j hj
  have he := congrArg (fun T : Representation.IntertwiningMap τ τ => T (I j v)) hz
  simp only [Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply,
    copyIdempotent_apply I hI hρ hτ ho] at he
  have he' : ∑ i ∈ s, z i • (if i = j then I j v else 0) = 0 := he
  simp only [smul_ite, smul_zero] at he'
  simp only [Finset.sum_ite_eq', ite_eq_left hj] at he'
  exact (smul_eq_zero.mp he').resolve_right (fun hz => hv ((I j).injective (hz.trans (map_zero _).symm)))

lemma copy_count_le_commutant [Nontrivial V]
    (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (ho : ∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0) :
    u ≤ Module.finrank ℂ (Representation.IntertwiningMap τ τ) := by
  simpa using (copyIdempotent_independent I hI hρ hτ ho).fintype_card_le_finrank
end CopyCount
end RowColumn
namespace RowColumn
open scoped BigOperators Classical
open CubeShuffle.Specht CubeShuffle.UnitaryFinite

section Relabelling
variable {S T L : Type*}

def lineGroupCongr (e : S ≃ T) (f : S → L) :
    lineGroup f ≃* lineGroup (f ∘ e.symm) where
  toFun g := ⟨e.permCongr g.1, by
    intro x
    simpa only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply] using g.2 (e.symm x)⟩
  invFun g := ⟨e.symm.permCongr g.1, by
    intro x
    simpa only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply] using g.2 (e x)⟩
  left_inv g := by apply Subtype.ext; exact e.permCongr.symm_apply_apply g.1
  right_inv g := by apply Subtype.ext; exact e.permCongr.apply_symm_apply g.1
  map_mul' g t := by apply Subtype.ext; exact e.permCongrHom.map_mul g.1 t.1

end Relabelling

section Transfer
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def commutantOfComp (ρ : Representation ℂ G V) (e : H ≃* G) :
    Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) →ₗ[ℂ]
      Representation.IntertwiningMap ρ ρ where
  toFun T :=
    { toLinearMap := T.toLinearMap
      isIntertwining' g := by simpa using T.isIntertwining' (e.symm g) }
  map_add' A B := rfl
  map_smul' z A := rfl

lemma commutantOfComp_injective (ρ : Representation ℂ G V) (e : H ≃* G) :
    Function.Injective (commutantOfComp ρ e) := by
  intro T U he
  exact Representation.IntertwiningMap.ext
    (congrArg (fun T : Representation.IntertwiningMap ρ ρ => T.toLinearMap) he)

lemma commutant_comp_finrank_le [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (e : H ≃* G) :
    Module.finrank ℂ (Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) ≤
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) :=
  LinearMap.finrank_le_finrank_of_injective (commutantOfComp_injective ρ e)
end Transfer

section HookMultiplicity
variable {S L : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  (f : S → L) (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h)

abbrev hookLineTarget :=
  (Signed.lineRepresentation (odd := HookModel.IsOdd (h := h))
    (k := HookModel.oddCount a h H) (f ∘ e.symm)).comp (lineGroupCongr e f).toMonoidHom

def hookLineEmbedding : Representation.IntertwiningMap
    ((relabelledUnitary a e).comp (lineGroup f).subtype) (hookLineTarget f a e h H) where
  toLinearMap := (HookModel.hookEmbedding a h H).toLinearMap.comp (spaceHilbertEquiv a).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let T := (HookModel.hookEmbedding a h H).comp (unitaryEquiv a).symm.toIntertwiningMap
    exact Representation.IntertwiningMap.isIntertwining _ _ T (e.permCongr g.1) v

omit [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L] in
lemma hookLineEmbedding_injective : Function.Injective (hookLineEmbedding f a e h H) :=
  (HookModel.hookEmbedding_injective a h H).comp (spaceHilbertEquiv a).symm.injective

include H

/-- Polynomial commutant estimate for the actual hook Specht representation
restricted to arbitrary fibres. This is the required first multiplicity bound
for both row and column restrictions in the occupied theorem. -/
lemma hook_line_commutant_bound :
    Module.finrank ℂ (Representation.IntertwiningMap
      ((relabelledUnitary a e).comp (lineGroup f).subtype)
      ((relabelledUnitary a e).comp (lineGroup f).subtype)) ≤
      (Fintype.card S + 1) ^ (4 * Fintype.card L * h ^ 2) := by
  apply (commutant_finrank_le_of_embedding (hookLineEmbedding f a e h H)
    (hookLineEmbedding_injective f a e h H)).trans
  apply (commutant_comp_finrank_le _ (lineGroupCongr e f)).trans
  have hc := Signed.commutant_dimension_bound (odd := HookModel.IsOdd (h := h))
    (k := HookModel.oddCount a h H) (f ∘ e.symm)
  have hs : Fintype.card (Cell a) = Fintype.card S := (Fintype.card_congr e).symm
  simpa only [hs, HookModel.Color, Fintype.card_sum, Fintype.card_fin,
    show Fintype.card L * (h + h) ^ 2 = 4 * Fintype.card L * h ^ 2 by ring] using hc

lemma hook_line_copy_count {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ (lineGroup f) V)
    (hρ : IsUnitary ρ) {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] hilbertSpace a)
    (hI : CompleteCopies (V := V) (W := hilbertSpace a) ρ ((relabelledUnitary a e).comp (lineGroup f).subtype) I) :
    u ≤ (Fintype.card S + 1) ^ (4 * Fintype.card L * h ^ 2) :=
  (copy_count_le_commutant (V := V) (X := hilbertSpace a) I hI.1 hρ (fun g => relabelledUnitary_unitary a e g.1) hI.2.1).trans
    (hook_line_commutant_bound f a e h H)

end HookMultiplicity
end RowColumn

end

end OAI
