import Mathlib
import OAI.Topology.ArtinGroups.Complexes.FrameModelLayerMiddle
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in

lemma homDimension_zero_of_cycles_boundary {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (h : ∀ f ∈ homCycles Q E F n v, f ∈ homBoundaries Q E F n v) :
    homDimension Q E F n v = 0 := by
  have hb : (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype = ⊤ := by
    apply eq_top_iff.mpr
    intro f _
    exact h f.val f.property
  unfold homDimension homCohomology
  rw [hb]
  exact Module.finrank_zero_of_subsingleton

lemma frameModel_pure_middle_dimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (C : CoxeterMatrix V) (hC : UnfoldedPresentation Q C) (x : Artin C) (α : V)
    (l k : ℤ) :
    totalHomDimension Q
      ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) l)
      ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) k)
      (k-l+1) = 0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  apply homDimension_zero_of_cycles_boundary Q
  intro f hf
  apply frameModel_layer_middle_vanishing Q hn C hC x α l k _ v hf
  exact pure_homSpace_linear Q _ _ (fun i => i.property) (fun j => j.property) (by omega) hf.1

lemma frameModel_pure_cartan_nonneg (hn : ∀ a, Q.source a ≠ Q.target a)
    (C : CoxeterMatrix V) (hC : UnfoldedPresentation Q C) (x : Artin C) (α : V)
    (l k : ℤ) :
    0 ≤ generatorVector Q
      ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) l) ⬝ᵥ
      ((unfoldedCartan Q).mulVec (generatorVector Q
      ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q (frameModel_minimal Q hn C hC x α) k))) := by
  rw [pure_cartan_euler Q _ _ (fun i => i.property) (fun j => j.property),
    frameModel_pure_middle_dimension Q hn C hC x α l k, Nat.cast_zero, sub_zero]
  positivity

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
