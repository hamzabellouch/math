import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDimensionZeroCycles

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} [Field K] (Q:ReversibleQuiver V A)
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classLayerTotalHomDimension (x y:FiniteHomotopyClass Q (K:=K))
    (l k t:ℤ) : ℕ :=
  totalHomDimension Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) l)
    ((minimalClassModel Q y).complex.pureLayer Q (minimalClassModel_minimal Q y) k) t

lemma frameModel_pure_orthogonal_middle_dimension (hn:∀ a,Q.source a≠Q.target a)
    (C:CoxeterMatrix V) (hC:UnfoldedPresentation Q C) (x:Artin C)
    {α β:V} (hab:OrthogonalVertices Q α β) (l k:ℤ) :
    totalHomDimension Q
      ((frameModel Q (K:=K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) l)
      ((frameModel Q (K:=K) hn C hC x β).complex.pureLayer Q (frameModel_minimal Q hn C hC x β) k)
      (k-l+1)=0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  apply homDimension_zero_of_cycles_boundary Q
  intro f hf
  apply frameModel_orthogonal_layer_middle_vanishing Q hn C hC x hab l k _ v hf
  exact pure_homSpace_linear Q _ _ (fun i=>i.property) (fun i=>i.property) (by omega) hf.1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
