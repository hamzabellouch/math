import OAI.Topology.EilenbergGanea.Dimension
import OAI.Topology.EilenbergGanea.CubicalCover
import OAI.AlgebraicTopology.CWComplex.Presentation

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea
universe u

/-- Exclusion is for arbitrary ordinary2-dimensional classifying CW spaces,
not merely finite presentations or cell complexes with finitely many orbits. -/
theorem source_no_classifyingSpace_two : ¬ HasClassifyingSpace.{u} SourceGroup 2 := by
  rintro ⟨X,tX,hTX,cX,hd,hpc,x,⟨χ⟩,E,tE,hcon,p,cov,hs⟩
  let : TopologicalSpace X := tX
  let : T2Space X := hTX
  let : Topology.CWComplex (Set.univ : Set X) := cX
  let : PathConnectedSpace X := hpc
  let : TopologicalSpace E := tE
  let : ContractibleSpace E := hcon
  obtain ⟨A,a,ha,r,hr,hp,B,hB⟩ := CWPresentation.ordinary_boundary_basis cov hd hs x χ
  exact source_no_boundary_basis a ha r hr hp B hB

/-- Source Theorem1.1 for the exact103-cell flag triangulation and its actual
Artin height kernel. The last conjunct is polymorphic in the universe of the
hypothetical ordinary CW model, with unrestricted numbers of cells. -/
theorem source_main :
    Group.FG SourceGroup ∧ Group.ResiduallyFinite SourceGroup ∧
    cohomologicalDimension SourceGroup = 2 ∧
    HasClassifyingSpace.{0} SourceGroup 3 ∧
    ¬ HasClassifyingSpace.{u} SourceGroup 2 :=
  ⟨source_finitely_generated,source_residuallyFinite,source_cohomologicalDimension,
    source_hasClassifyingSpace_three,source_no_classifyingSpace_two⟩

end EilenbergGanea


end

end OAI
