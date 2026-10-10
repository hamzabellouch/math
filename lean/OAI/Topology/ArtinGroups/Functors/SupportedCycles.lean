import Mathlib
import OAI.Topology.ArtinGroups.Functors.Placement
import OAI.Topology.ArtinGroups.Functors.TestIndex
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Diagrams.CongrEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma test_matrix_reindex (E:BasedComplex Q (K := K) I) (α:V) :
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).submatrix
      (e.testIndex E.placement α) (e.testIndex E.placement α) =
      testMatrix Q E.placement E.placement α E.differential := by
  apply Matrix.ext
  intro i j
  exact e.test_matrix _ _ _ _ i j

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma test_support_reindex (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    (fun i : TestIndex R (e.complex E).placement (e.vertex α) =>
      ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) ∘ e.testIndex E.placement α =
      (fun i : TestIndex Q E.placement α => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  funext i
  change (_ ∧ Path.length (e.path i.2.val)=n) = _
  rw [e.path_length]
  rfl

noncomputable def supportedCycles (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential)
      (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  exact ((ScalarCycles.reindexEquiv
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential)
    (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) (e.testIndex E.placement α)).trans
    (ScalarCycles.congrEquiv _ _ _ _ (e.test_matrix_reindex E α) (e.test_support_reindex E α c n))).symm

noncomputable def dualSupportedCycles (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).transpose
      (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply LinearEquiv.symm
  refine (ScalarCycles.reindexEquiv
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).transpose
    (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) (e.testIndex E.placement α)).trans
    (ScalarCycles.congrEquiv _ _ _ _ ?_ (e.test_support_reindex E α c n))
  exact (Matrix.transpose_submatrix _ _ _).symm.trans (congrArg Matrix.transpose (e.test_matrix_reindex E α))

noncomputable def coefficientSocle (E:BasedComplex Q (K := K) I) {l:ℤ}
    (hE:∀ i,(E.placement i).level=l) (α:V) (c:ℤ) :
    BasedComplex.coefficientSocle Q E α c ≃ₗ[K]
      BasedComplex.coefficientSocle R (e.complex E) (e.vertex α) c :=
  (coefficientSocleTestEquiv Q E hE α c).trans ((e.supportedCycles E α c 0).trans
    (coefficientSocleTestEquiv R (e.complex E) hE (e.vertex α) c).symm)

noncomputable def coefficientTopDual (E:BasedComplex Q (K := K) I) {l:ℤ}
    (hE:∀ i,(E.placement i).level=l) (α:V) (c:ℤ) :
    BasedComplex.coefficientTopDual Q E α c ≃ₗ[K]
      BasedComplex.coefficientTopDual R (e.complex E) (e.vertex α) c :=
  (coefficientTopTestEquiv Q E hE α c).trans ((e.dualSupportedCycles E α c 2).trans
    (coefficientTopTestEquiv R (e.complex E) hE (e.vertex α) c).symm)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
