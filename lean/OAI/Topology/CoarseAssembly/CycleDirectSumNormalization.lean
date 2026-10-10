import OAI.Topology.CoarseAssembly.CycleUnitaryNormalization
import OAI.Topology.CoarseAssembly.DirectSumIndex

namespace OAI

/-! # Direct sums are preserved by explicit cycle normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem boundedTransform_prod (F : A) (G : B) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    boundedTransform (F, G) (Prod.ext hF.star_eq hG.star_eq) =
      (boundedTransform F hF, boundedTransform G hG) := by
  apply Prod.ext
  · exact map_boundedTransform (StarAlgHom.fst ℂ A B) (F, G) _
  · exact map_boundedTransform (StarAlgHom.snd ℂ A B) (F, G) _

variable {R : Type} [CStarAlgebra R] {c d e : OddCycle R}

theorem OddCycle.IsDirectSum.block_boundedTransform (h : c.IsDirectSum d e)
    (F : End c.space) (G : End d.space) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    h.block (boundedTransform F hF) (boundedTransform G hG) =
      boundedTransform (h.block F G) ((show IsSelfAdjoint (F, G) from Prod.ext hF.star_eq hG.star_eq).map h.blockHom) := by
  have hb := map_boundedTransform h.blockHom (F, G) (Prod.ext hF.star_eq hG.star_eq)
  rw [boundedTransform_prod] at hb
  exact hb

def OddCycle.IsDirectSum.regularize (h : c.IsDirectSum d e) (χ : R →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).IsDirectSum (d.regularize χ) (e.regularize χ) where
  left := h.left
  right := h.right
  orthogonal := h.orthogonal
  exhaustive := h.exhaustive
  representation_eq a := by
    let φ := h.blockHom
    have hr (a : R) : h.block (c.representation a) (d.representation a) = e.representation a :=
      (h.representation_eq a).symm
    change e.representation a + χ a • (1 - e.representation 1) =
      φ ((c.representation a, d.representation a) +
        χ a • (1 - (c.representation 1, d.representation 1)))
    rw [map_add, map_smul, map_sub, map_one φ]
    change e.representation a + χ a • (1 - e.representation 1) =
      h.block (c.representation a) (d.representation a) +
        χ a • (1 - h.block (c.representation 1) (d.representation 1))
    rw [hr a, hr 1]
  operator_eq := by
    have hc := c.unitalSelfAdjoint_selfAdjoint χ
    have hd := d.unitalSelfAdjoint_selfAdjoint χ
    have he := e.unitalSelfAdjoint_selfAdjoint χ
    have hcut : h.block (c.unitalSelfAdjoint χ).operator (d.unitalSelfAdjoint χ).operator =
        (e.unitalSelfAdjoint χ).operator := by
      have hr : h.block (c.representation 1) (d.representation 1) = e.representation 1 :=
        (h.representation_eq 1).symm
      have ho : h.block c.operator d.operator = e.operator := h.operator_eq.symm
      rw [c.unitalSelfAdjoint_operator, d.unitalSelfAdjoint_operator,
        e.unitalSelfAdjoint_operator, h.block_cutDown, hr, ho]
    have hb := h.block_boundedTransform (c.unitalSelfAdjoint χ).operator
      (d.unitalSelfAdjoint χ).operator hc hd
    exact (hb.trans (boundedTransform_congr hcut _ he)).symm

end CoarseAssembly.Analytic

end

end OAI
