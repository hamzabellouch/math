import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.DifferentialMulExtendLayer
import OAI.Topology.ArtinGroups.Complexes.RestrictLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma frameModel_layer_middle_vanishing (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V)
    (l k n v : ℤ)
    {f : Matrix {i // ((frameModel Q (K := K) hn M hM x α).complex.placement i).level = l}
      {j // ((frameModel Q (K := K) hn M hM x α).complex.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) k) n v)
    (hlin : LinearMatrix Q f) :
    f ∈ homBoundaries Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) k) n v := by
  apply layer_boundary_of_extended_boundary Q _ _
    (frameModel_minimal Q hn M hM x α) (frameModel_minimal Q hn M hM x α) l k n v hlin
  apply frameModel_linear_cycle_boundary Q hn M hM x α n v
  · exact extendLayer_cycle Q _ _ (frameModel_minimal Q hn M hM x α)
      (frameModel_minimal Q hn M hM x α) l k n v hf hlin
  · exact extendLayer_linear Q _ _ l k hlin

lemma frameModel_orthogonal_layer_middle_vanishing (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M)
    {α β : V} (h : OrthogonalVertices Q α β) (l k n v : ℤ)
    {f : Matrix {i // ((frameModel Q (K := K) hn M hM x α).complex.placement i).level = l}
      {j // ((frameModel Q (K := K) hn M hM x β).complex.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x β).complex.pureLayer Q (frameModel_minimal Q hn M hM x β) k) n v)
    (hlin : LinearMatrix Q f) :
    f ∈ homBoundaries Q
      ((frameModel Q hn M hM x α).complex.pureLayer Q (frameModel_minimal Q hn M hM x α) l)
      ((frameModel Q hn M hM x β).complex.pureLayer Q (frameModel_minimal Q hn M hM x β) k) n v := by
  apply layer_boundary_of_extended_boundary Q _ _
    (frameModel_minimal Q hn M hM x α) (frameModel_minimal Q hn M hM x β) l k n v hlin
  apply frameModel_orthogonal_cycle_boundary Q hn M hM x h n v
  exact extendLayer_cycle Q _ _ (frameModel_minimal Q hn M hM x α)
    (frameModel_minimal Q hn M hM x β) l k n v hf hlin

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
