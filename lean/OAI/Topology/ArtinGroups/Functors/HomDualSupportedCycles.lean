import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Diagrams.TransposeConjugateEquiv
import OAI.Topology.ArtinGroups.Functors.LeftSocleIndexEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

noncomputable def homDualSupportedCyclesEquiv
    (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) (b n : ℤ) :
    ScalarCycles.supportedKernel
      (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential).transpose
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=n) := by
  apply ScalarCycles.transposeConjugateEquiv _ _ _ _
    (homSwitch Q step hstep N hN orient μ A E.placement u c)
    (homUnswitch Q step hstep N hN orient μ A E.placement u c)
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := evaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homSwitch,Matrix.blockDiagonal'_apply_eq] using h)
      simp only [he]
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := inverseEvaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homUnswitch,Matrix.blockDiagonal'_apply_eq] using h)
      simp only [he]
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · exact homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  · exact homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  · exact homUnswitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

noncomputable def leftTopTestEquiv (E : Zigzag.BasedComplex U (K := K) T)
    (u:V) (c:J) (b:ℤ) :
    ScalarCycles.supportedKernel
      (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=2) ≃ₗ[K]
    ((a : {a:J // N a c}) → Zigzag.BasedComplex.topTestCycles U E (u,a) b) := by
  let e := leftSocleIndexEquiv Q step hstep N hN E.placement u c
  let P := fun x : LeftHomIndex Q step hstep N hN E.placement u c =>
    (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=2
  have h := ScalarCycles.reindexEquiv
    (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose P e
  have ht : ((leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential).transpose).submatrix e e =
      Matrix.blockDiagonal' (fun a : {a:J // N a c} =>
        (Zigzag.testMatrix U E.placement E.placement (u,a) E.differential).transpose) := by
    rw [← Matrix.transpose_submatrix,show e=leftSocleIndexEquiv Q step hstep N hN E.placement u c from rfl,
      leftSocle_differential]
    apply Matrix.ext
    rintro ⟨a,i⟩ ⟨b,j⟩
    by_cases hab : a=b
    · subst b; simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_eq]
    · simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_ne _ _ _ hab,
        Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hab)]
  rw [ht] at h
  exact h.trans (ScalarCycles.blockEquiv
    (fun a : {a:J // N a c} => (Zigzag.testMatrix U E.placement E.placement (u,a) E.differential).transpose)
    (fun a x => (E.placement x.1).cochain=b ∧ Path.length x.2.val=2))

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def coefficientTopLabelEquiv
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Zigzag.BasedComplex.coefficientTopDual U (C E) (u,c) b ≃ₗ[K]
      ((a : {a:J // N a c}) → Zigzag.BasedComplex.coefficientTopDual U E (u,a) b) := by
  let e₀ := Zigzag.BasedComplex.coefficientTopTestEquiv U (C E) (fun i => hE i.1) (u,c) b
  let e₁ := ScalarCycles.reindexEquiv
    (Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential).transpose
    (fun x => ((C E).placement x.1).cochain=b ∧ Path.length x.2.val=2)
    (rightHomEquiv Q step hstep N hN E.placement u c)
  let e₂ := (homDualSupportedCyclesEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c b 2).symm
  let e₃ := leftTopTestEquiv Q step hstep N hN E u c b
  let e₄ := LinearEquiv.piCongrRight (fun a : {a:J // N a c} =>
    (Zigzag.BasedComplex.coefficientTopTestEquiv U E hE (u,a) b).symm)
  exact (((e₀.trans e₁).trans e₂).trans e₃).trans e₄

lemma coefficientTop_label_dimension
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Module.finrank K (Zigzag.BasedComplex.coefficientTopDual U (C E) (u,c) b) =
      ∑ a : {a:J // N a c}, Module.finrank K (Zigzag.BasedComplex.coefficientTopDual U E (u,a) b) := by
  rw [(coefficientTopLabelEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE u c b).finrank_eq]
  exact Module.finrank_pi_fintype K

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
