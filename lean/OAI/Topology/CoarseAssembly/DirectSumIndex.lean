import OAI.Topology.CoarseAssembly.OrthogonalBlock

namespace OAI

/-! # Direct-sum additivity of the explicit cycle index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {c d e : OddCycle A}

theorem OddCycle.IsDirectSum.block_cutDown (h : c.IsDirectSum d e)
    (P F : End c.space) (Q G : End d.space) :
    h.block (symmetricCutDown P F) (symmetricCutDown Q G) =
      symmetricCutDown (h.block P Q) (h.block F G) := by
  let φ := h.blockHom
  have hs (r : ℝ) (p : End c.space × End d.space) : φ (r • p) = r • φ p :=
    φ.toAlgHom.map_smul_of_tower r p
  change φ ((1 / 2 : ℝ) • ((P, Q) * (F, G) * (P, Q) +
    star ((P, Q) * (F, G) * (P, Q))) + (1 - (P, Q))) = _
  rw [map_add, hs, map_add, map_star, map_mul, map_mul, map_sub, map_one]
  rfl

theorem OddCycle.IsDirectSum.block_positive (h : c.IsDirectSum d e)
    (F : End c.space) (G : End d.space) :
    h.block (positiveProjection F) (positiveProjection G) =
      positiveProjection (h.block F G) := by
  let φ := h.blockHom
  have hs (r : ℝ) (p : End c.space × End d.space) : φ (r • p) = r • φ p :=
    φ.toAlgHom.map_smul_of_tower r p
  change φ ((1 / 2 : ℝ) • ((F, G) + 1)) = _
  rw [hs, map_add, map_one]
  rfl

theorem OddCycle.IsDirectSum.block_toeplitz (h : c.IsDirectSum d e)
    (P U : End c.space) (Q V : End d.space) :
    h.block (toeplitzCompression P U) (toeplitzCompression Q V) =
      toeplitzCompression (h.block P Q) (h.block U V) := by
  let φ := h.blockHom
  change φ ((P, Q) * (U, V) * (P, Q) + (1 - (P, Q))) = _
  rw [map_add, map_mul, map_mul, map_sub, map_one]
  rfl

theorem OddCycle.IsDirectSum.block_unitaryExtension (h : c.IsDirectSum d e) (u : A) :
    h.block (unitaryExtension c u) (unitaryExtension d u) = unitaryExtension e u := by
  let φ := h.blockHom
  change φ ((c.representation u, d.representation u) +
    (1 - (c.representation 1, d.representation 1))) = _
  rw [map_add, map_sub, map_one]
  change h.block (c.representation u) (d.representation u) +
    (1 - h.block (c.representation 1) (d.representation 1)) = _
  have hr (a : A) : h.block (c.representation a) (d.representation a) = e.representation a :=
    (h.representation_eq a).symm
  rw [hr u, hr 1]
  rfl

theorem rawCycleToeplitz_directSum (h : c.IsDirectSum d e) (u : A) :
    h.block (rawCycleToeplitz c u) (rawCycleToeplitz d u) = rawCycleToeplitz e u := by
  unfold rawCycleToeplitz
  have hr : h.block (c.representation 1) (d.representation 1) = e.representation 1 :=
    (h.representation_eq 1).symm
  have ho : h.block c.operator d.operator = e.operator := h.operator_eq.symm
  rw [h.block_toeplitz, h.block_positive, h.block_cutDown, hr, ho, h.block_unitaryExtension]

theorem OddCycle.IsDirectSum.block_coordinates (h : c.IsDirectSum d e)
    (T : End c.space) (S : End d.space) :
    h.coordinates ∘L h.block T S ∘L h.inclusion = T.prodMap S := by
  have he : h.block T S = h.inclusion ∘L (T.prodMap S) ∘L h.coordinates := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [he]
  simp only [← ContinuousLinearMap.comp_assoc, h.coordinates_inclusion,
    ContinuousLinearMap.id_comp]
  rw [ContinuousLinearMap.comp_assoc, h.coordinates_inclusion,
    ContinuousLinearMap.comp_id]

theorem rawCycleIndex_directSum (h : c.IsDirectSum d e) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    rawCycleIndex e u = rawCycleIndex c u + rawCycleIndex d u := by
  have hc := rawCycleToeplitz_fredholm c u hul hur
  have hd := rawCycleToeplitz_fredholm d u hul hur
  have he := rawCycleToeplitz_fredholm e u hul hur
  have hcoord : h.coordinates.IsFredholm := h.coordinateEquiv.isFredholm
  have hincl : h.inclusion.IsFredholm := h.coordinateEquiv.symm.isFredholm
  have hcz : h.coordinates.toLinearMap.index = 0 :=
    LinearMap.index_of_bijective h.coordinateEquiv.bijective
  have hiz : h.inclusion.toLinearMap.index = 0 :=
    LinearMap.index_of_bijective h.coordinateEquiv.symm.bijective
  have hi : (h.coordinates ∘L rawCycleToeplitz e u ∘L h.inclusion).toLinearMap.index =
      (rawCycleToeplitz e u).toLinearMap.index := by
    rw [hcoord.index_comp (he.comp hincl), he.index_comp hincl, hcz, hiz, zero_add, add_zero]
  have hprod : h.coordinates ∘L rawCycleToeplitz e u ∘L h.inclusion =
      (rawCycleToeplitz c u).prodMap (rawCycleToeplitz d u) := by
    rw [← rawCycleToeplitz_directSum h u, h.block_coordinates]
  rw [hprod] at hi
  exact hi.symm.trans (fredholmIndex_prodMap _ _ hc hd)

end CoarseAssembly.Analytic

end

end OAI
