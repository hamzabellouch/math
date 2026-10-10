import OAI.Topology.EilenbergGanea.Seed
import OAI.GroupTheory.RightAngledArtin.ResidualFiniteness
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
abbrev SourceGroup := (height seedGraph).ker

/-- Integral, left-module cohomological dimension; no rational replacement. -/
def cohomologicalDimension (G : Type*) [Group G] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ G) (Representation.trivial ℤ G ℤ).asModule)

universe u
/-- Ordinary K(G,1) of dimension at most n. The cell and space types have no
finiteness or countability restriction. The contractible surjective covering
is the usual universal-cover characterization of a classifying space. -/
def HasClassifyingSpace (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
    (_ : Topology.CWComplex (Set.univ : Set X)),
    (∀ k : ℕ, n < k → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) k)) ∧
    PathConnectedSpace X ∧
    ∃ x : X, Nonempty (FundamentalGroup X x ≃* G) ∧
    ∃ (E : Type u) (_ : TopologicalSpace E), ContractibleSpace E ∧
    ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p


end EilenbergGanea

namespace EilenbergGanea
/-- The finite-generation conjunct for the exact source height kernel. -/
theorem source_finitely_generated : Group.FG SourceGroup :=
  height_kernel_fg seedGraph seed_connected.preconnected seedBase



end EilenbergGanea

namespace EilenbergGanea
/-- The second exact conjunct of the source main theorem. -/
theorem source_residuallyFinite : Group.ResiduallyFinite SourceGroup := by
  have := artin_residuallyFinite SeedCell seedGraph
  infer_instance

end EilenbergGanea



end

end OAI
