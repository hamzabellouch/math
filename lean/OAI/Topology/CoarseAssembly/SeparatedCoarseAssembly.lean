import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.SeparatedIndexCoarsening
import OAI.Topology.CoarseAssembly.Assembly

namespace OAI

/-! # Constructed coarse assembly for the separated finite-component application

The maps are defined on actual locally finite analytic K-homology and are
compatible with coarsening by the proved finite-tail argument.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

@[simp] theorem separatedIndexFamily_atScale (o : ∀ i, Q i) (n : ℕ) :
    letI := separatedMetric o
    (separatedIndexFamily o).atScale n = separatedRipsIndex o n (Nat.cast_nonneg n) := by
  let := separatedMetric o
  dsimp only [separatedIndexFamily]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    intro r s hrs a
    exact DFunLike.congr_fun (separatedRipsIndex_coarsen o
      (Nat.cast_nonneg r) (Nat.cast_nonneg s) (by exact_mod_cast hrs)) a

def separatedCoarseAssembly (o : ∀ i, Q i) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    KX1 (Sigma Q) →+ OperatorKTheory.K1 (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2)) := by
  letI := separatedMetric o
  letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  exact (separatedIndexFamily o).assembly

@[simp] theorem separatedCoarseAssembly_of (o : ∀ i, Q i) (n : ℕ)
    (a : letI := separatedMetric o; LocallyFiniteK1 (Point (Sigma Q) n)) :
    letI := separatedMetric o
    separatedCoarseAssembly o ((coarsening (Sigma Q)).of n a) =
      separatedRipsIndex o n (Nat.cast_nonneg n) a :=
  by
    exact Eq.trans ((separatedIndexFamily o).assembly_of n a)
      (congrArg (fun f => f a) (separatedIndexFamily_atScale o n))

end CoarseAssembly.Rips

end

end OAI
