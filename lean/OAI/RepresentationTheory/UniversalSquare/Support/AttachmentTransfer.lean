import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Attachment Transfer. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl

def transposeColumnAverage {n : ℕ} {α : YoungDiagram} (t : Tableau n α) : Specht t := by
  classical
  letI := Fintype.ofFinite (columnGroup (transposeTableau t))
  exact ∑ g : columnGroup (transposeTableau t),
    spechtRep t g.val ⟨polytabloid t, mem_cyclic _ _⟩

lemma transposeColumnAverage_nonzero {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    transposeColumnAverage t ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  intro he
  have hh := congrArg (fun y : Specht t => y.val (rowWord t)) he
  have hg (g : columnGroup (transposeTableau t)) : rowWord t ∘ g.val = rowWord t := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [transposeColumnAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (transposeTableau t),
    polytabloid t (rowWord t ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma transposeColumnAverage_fixed {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g : columnGroup (transposeTableau t)) :
    spechtRep t g.val (transposeColumnAverage t) = transposeColumnAverage t := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  unfold transposeColumnAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (transposeTableau t) =>
    spechtRep t h.val ⟨polytabloid t, mem_cyclic _ _⟩)

lemma signEquiv_transposeColumnAverage {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (transposeColumnAverage t)).val =
      c • polytabloid (transposeTableau t) := by
  have ha (g : columnGroup (transposeTableau t)) :
      spechtRep (transposeTableau t) g.val (φ (transposeColumnAverage t)) =
        signC g.val • φ (transposeColumnAverage t) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (transposeColumnAverage t)
    change φ (spechtRep t g.val (transposeColumnAverage t)) =
      signC g.val • spechtRep (transposeTableau t) g.val (φ (transposeColumnAverage t)) at he
    rw [transposeColumnAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (transposeTableau t)
    (φ (transposeColumnAverage t)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply transposeColumnAverage_nonzero t
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

def rowColumnWord {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    WordSpace n (α.transpose.colLen 0 * α.colLen 0) :=
  wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid t)

def rowColumnCyclic {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :=
  cyclic (wordRep n (α.transpose.colLen 0 * α.colLen 0)) (rowColumnWord t)

def columnAmbientSignMap {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    Representation.IntertwiningMap (wordRep n (α.colLen 0))
      (signTwist (wordRep n (α.transpose.colLen 0))) :=
  (signTwistMap (spechtInclusion (transposeTableau t))).comp
    (φ.toIntertwiningMap.comp (subrepProject (spechtSub t)
      (fun _ hx => cyclic_star _ (polytabloid_real _) hx)))

lemma columnAmbientSignMap_subtype {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
    (x : Specht t) : columnAmbientSignMap t φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub t) _ x.val)).val = _
  exact congrArg (fun y : Specht t => (φ y).val) (subrepProject_subtype (spechtSub t) _ x)

def columnPairAntiMap {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    Representation.IntertwiningMap
      (signTwist (wordRep n (α.transpose.colLen 0 * α.colLen 0)))
      (wordRep n (α.transpose.colLen 0 * α.transpose.colLen 0)) :=
  (wordTensorEquiv _ _ _).toIntertwiningMap.comp
    ((tensorAnti (wordRep _ _) (columnAmbientSignMap t φ)).comp
      (signTwistMap (wordTensorEquiv _ _ _).symm.toIntertwiningMap))

lemma columnPairAntiMap_tensor {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
    (x : WordSpace n (α.transpose.colLen 0)) (y : WordSpace n (α.colLen 0)) :
    columnPairAntiMap t φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] columnAmbientSignMap t φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id
    (columnAmbientSignMap t φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_rowColumn {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    letI := Fintype.ofFinite (columnGroup (transposeTableau t))
    ∑ g : columnGroup (transposeTableau t), signC g.val •
      wordRep n (α.transpose.colLen 0 * α.colLen 0) g.val (rowColumnWord t) =
      wordTensor _ _ _
        (polytabloid (transposeTableau t) ⊗ₜ[ℂ] (transposeColumnAverage t).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  change _ = wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
    (∑ g : columnGroup (transposeTableau t),
      spechtRep t g.val ⟨polytabloid t, mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid t)) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (transposeTableau t)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid t)) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    map_smul, smul_smul, signC_mul_self, one_smul]
  rfl

def rowColumnToSquare {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    Representation.IntertwiningMap (signTwist (rowColumnCyclic t).toRepresentation)
      (wordRep n (α.transpose.colLen 0 * α.transpose.colLen 0)) :=
  (columnPairAntiMap t φ).comp (signTwistMap
    { toLinearMap := (rowColumnCyclic t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl })

theorem polytabloid_square_in_rowColumn_image {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
      polytabloid (transposeTableau t)) ∈ (rowColumnToSquare t φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  obtain ⟨c,hc,hφ⟩ := signEquiv_transposeColumnAverage t φ
  let x : (rowColumnCyclic t).toSubmodule :=
    ∑ g : columnGroup (transposeTableau t), signC g.val •
      (rowColumnCyclic t).toRepresentation g.val ⟨rowColumnWord t, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
      (transposeColumnAverage t).val) := by
    change (∑ g : columnGroup (transposeTableau t), signC g.val •
      (rowColumnCyclic t).toRepresentation g.val ⟨rowColumnWord t, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_rowColumn t
  have hF : rowColumnToSquare t φ x = c • wordTensor _ _ _
      (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid (transposeTableau t)) := by
    change columnPairAntiMap t φ x.val = _
    rw [hx, columnPairAntiMap_tensor, columnAmbientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul]
  exact (Submodule.smul_mem_iff _ hc).mp ⟨x,hF⟩

theorem subrepresentation_embeds_of_le_range {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (S : Subrepresentation σ) (hS : S ≤ F.range) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation ρ, Function.Injective f := by
  let Q : Representation.IntertwiningMap ρ F.range.toRepresentation :=
    { toLinearMap := F.toLinearMap.rangeRestrict
      isIntertwining' := by
        intro g
        ext x
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  have hQ : Function.Surjective Q := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let I : Representation.IntertwiningMap S.toRepresentation F.range.toRepresentation :=
    { toLinearMap := S.toSubmodule.inclusion hS
      isIntertwining' := fun _ => rfl }
  obtain ⟨f,hf⟩ := intertwining_lift_surjective Q hQ I
  refine ⟨f, ?_⟩
  intro x y he
  apply Subtype.ext
  have hx := congrArg (fun H => (H x).val) hf
  have hy := congrArg (fun H => (H y).val) hf
  change (Q (f x)).val = x.val at hx
  change (Q (f y)).val = y.val at hy
  exact hx.symm.trans ((congrArg (fun z => (Q z).val) he).trans hy)

theorem square_cyclic_embeds_sign_rowColumn {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    ∃ f : Representation.IntertwiningMap
      (cyclic (wordRep n (α.transpose.colLen 0 * α.transpose.colLen 0))
        (wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
          polytabloid (transposeTableau t)))).toRepresentation
      (signTwist (rowColumnCyclic t).toRepresentation), Function.Injective f := by
  obtain ⟨φ⟩ := specht_sign_transpose t
  apply subrepresentation_embeds_of_le_range (rowColumnToSquare t φ)
  exact (cyclic_le _ _ _).mpr (polytabloid_square_in_rowColumn_image t φ)

end Saxl
end
end

end OAI
