import OAI.Topology.EilenbergGanea.SeedContraction
import OAI.Topology.EilenbergGanea.LevelBasis
import OAI.Topology.EilenbergGanea.CliqueCohomology

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.SeedEncoding
@[simp] theorem cellEquiv_symm_apply (i : Fin 103) : cellEquiv.symm i = cellAt i := rfl
end EilenbergGanea.SeedEncoding
namespace EilenbergGanea
noncomputable abbrev sourceVertexOrder : LinearOrder SeedCell :=
  LinearOrder.lift' SeedEncoding.cellEquiv SeedEncoding.cellEquiv.injective
local instance : LinearOrder SeedCell := sourceVertexOrder
local instance : Preorder SeedCell := sourceVertexOrder.toPartialOrder.toPreorder
local instance : LT SeedCell := sourceVertexOrder.toLT
local instance : LE SeedCell := sourceVertexOrder.toLE

@[simp] theorem sourceVertexOrder_lt (a b : SeedCell) :
    a < b ↔ SeedEncoding.cellEquiv a < SeedEncoding.cellEquiv b := Iff.rfl

theorem source_valid_to_index (w : List SeedCell) (hw : SimplicialChains.Valid seedGraph w) :
    SimplicialChains.Valid SeedChainCertificate.graph (w.map SeedEncoding.cellEquiv) := by
  constructor
  · rw [List.pairwise_map]
    exact hw.1
  · rw [List.pairwise_map]
    simpa only [SeedChainCertificate.graph,SimpleGraph.comap_adj,
      ← SeedEncoding.cellEquiv_symm_apply,Equiv.symm_apply_apply] using hw.2

theorem index_valid_to_source (w : List (Fin 103))
    (hw : SimplicialChains.Valid SeedChainCertificate.graph w) :
    SimplicialChains.Valid seedGraph (w.map SeedEncoding.cellEquiv.symm) := by
  constructor
  · rw [List.pairwise_map]
    simpa only [sourceVertexOrder_lt,Equiv.apply_symm_apply] using hw.1
  · rw [List.pairwise_map]
    exact hw.2

/-- Relabeling uses the original seed graph and merely chooses an order on its
vertices for the signed integral chain convention. -/
noncomputable def sourceLinkContraction (K : SimplicialChains.Contraction SeedChainCertificate.graph) :
    SimplicialChains.Contraction seedGraph :=
  K.reindex SeedEncoding.cellEquiv.symm (index_valid_to_source) (source_valid_to_index)

end EilenbergGanea

namespace EilenbergGanea
local instance : LinearOrder SeedCell := sourceVertexOrder
local instance : Preorder SeedCell := sourceVertexOrder.toPartialOrder.toPreorder
local instance : LT SeedCell := sourceVertexOrder.toLT
local instance : LE SeedCell := sourceVertexOrder.toLE

theorem source_valid_length_le (w : List SeedCell) (hw : SimplicialChains.Valid seedGraph w) :
    w.length ≤ 3 := by
  simpa only [List.length_map] using
    SeedChainCertificate.valid_length_le (w.map SeedEncoding.cellEquiv) (source_valid_to_index w hw)

theorem source_cd_eq_two_of_contraction
    (K : SimplicialChains.Contraction SeedChainCertificate.graph) :
    cohomologicalDimension SourceGroup = 2 := by
  apply le_antisymm
  · exact LevelBasis.artin_height_kernel_cd_le_two seedGraph seedBase seed_connected.preconnected
      (sourceLinkContraction K) source_valid_length_le
  · exact source_two_le_cohomologicalDimension

/-- The exact remaining geometric interface is not limited to finite or
countable presentations. This endpoint excludes any ordinary presentation
whose actual integral equivariant cellular boundaries freely span cycles. -/
theorem source_no_boundary_basis_of_contraction
    (K : SimplicialChains.Contraction SeedChainCertificate.graph)
    {A R : Type*} (a₀ : A → SourceGroup)
    (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains SourceGroup R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains SourceGroup A) = relatorChainMap a₀ r₀ c) : False := by
  let : Group.ResiduallyFinite SourceGroup := source_residuallyFinite
  exact LevelBasis.no_boundary_basis_presentation seedGraph seedBase seed_connected.preconnected
    (sourceLinkContraction K) source_valid_length_le SourceTransport.source_small_labels
    a₀ ha₀ r₀ hr₀ hp₀ E hE

end EilenbergGanea



namespace EilenbergGanea

/-- Literal integral cohomological dimension of the source's fixed group. -/
theorem source_cohomologicalDimension : cohomologicalDimension SourceGroup = 2 :=
  source_cd_eq_two_of_contraction SeedChainCertificate.contraction

/-- No arbitrary-alphabet genuine presentation has its relators as an integral
basis of Cayley cycles.  -/
theorem source_no_boundary_basis
    {A R : Type*} (a₀ : A → SourceGroup)
    (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains SourceGroup R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains SourceGroup A) = relatorChainMap a₀ r₀ c) : False :=
  source_no_boundary_basis_of_contraction SeedChainCertificate.contraction
    a₀ ha₀ r₀ hr₀ hp₀ E hE

end EilenbergGanea



end

end OAI
