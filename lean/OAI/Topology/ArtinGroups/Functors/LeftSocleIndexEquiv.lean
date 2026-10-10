import Mathlib
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Functors.LeftHomPlacement
import OAI.Topology.ArtinGroups.Functors.HomSupportedCyclesEquiv

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

def leftSocleIndexEquiv (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    ((a : {a:J // N a c}) × Zigzag.TestIndex U p (u,a)) ≃
      LeftHomIndex Q step hstep N hN p u c where
  toFun x := ⟨x.2.1,x.1,x.2.2⟩
  invFun x := ⟨x.2.1,x.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq B] [Fintype T] [DecidableEq T] in
lemma leftSocle_differential (p : T → GeneratorPlacement (V × J)) (u:V) (c:J)
    (D : Matrix T T (Zigzag U K)) :
    (leftHomMatrix Q step hstep N hN p p u c D).submatrix
      (leftSocleIndexEquiv Q step hstep N hN p u c)
      (leftSocleIndexEquiv Q step hstep N hN p u c) =
    Matrix.blockDiagonal' (fun a : {a:J // N a c} => Zigzag.testMatrix U p p (u,a) D) := by
  apply Matrix.ext
  rintro ⟨a,i,x⟩ ⟨b,j,y⟩
  by_cases hab : a=b
  · subst b
    simp only [Matrix.submatrix_apply,leftSocleIndexEquiv,Equiv.coe_fn_mk,leftHomMatrix,
      ite_true,Matrix.blockDiagonal'_apply_eq,Zigzag.testMatrix]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab]
    exact ite_eq_right hab

noncomputable def leftSocleTestEquiv (E : Zigzag.BasedComplex U (K := K) T)
    (u:V) (c:J) (b:ℤ) :
    ScalarCycles.supportedKernel
      (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential)
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=0) ≃ₗ[K]
    ((a : {a:J // N a c}) → Zigzag.BasedComplex.socleTestCycles U E (u,a) b) := by
  let e := leftSocleIndexEquiv Q step hstep N hN E.placement u c
  let P := fun x : LeftHomIndex Q step hstep N hN E.placement u c =>
    (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=0
  have h := ScalarCycles.reindexEquiv
    (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential) P e
  rw [show e=leftSocleIndexEquiv Q step hstep N hN E.placement u c from rfl,
    leftSocle_differential] at h
  exact h.trans (ScalarCycles.blockEquiv
    (fun a : {a:J // N a c} => Zigzag.testMatrix U E.placement E.placement (u,a) E.differential)
    (fun a x => (E.placement x.1).cochain=b ∧ Path.length x.2.val=0))

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def coefficientSocleLabelEquiv
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Zigzag.BasedComplex.coefficientSocle U (C E) (u,c) b ≃ₗ[K]
      ((a : {a:J // N a c}) → Zigzag.BasedComplex.coefficientSocle U E (u,a) b) := by
  let e₀ := Zigzag.BasedComplex.coefficientSocleTestEquiv U (C E) (fun i => hE i.1) (u,c) b
  let e₁ := ScalarCycles.reindexEquiv
    (Zigzag.testMatrix U (C E).placement (C E).placement (u,c) (C E).differential)
    (fun x => ((C E).placement x.1).cochain=b ∧ Path.length x.2.val=0)
    (rightHomEquiv Q step hstep N hN E.placement u c)
  let e₂ := (homSupportedCyclesEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c b 0).symm
  let e₃ := leftSocleTestEquiv Q step hstep N hN E u c b
  let e₄ := LinearEquiv.piCongrRight (fun a : {a:J // N a c} =>
    (Zigzag.BasedComplex.coefficientSocleTestEquiv U E hE (u,a) b).symm)
  exact (((e₀.trans e₁).trans e₂).trans e₃).trans e₄

lemma coefficientSocle_label_dimension
    (E : Zigzag.BasedComplex U (K := K) T) {l:ℤ}
    (hE : ∀ i, (E.placement i).level=l) (u:V) (c:J) (b:ℤ) :
    Module.finrank K (Zigzag.BasedComplex.coefficientSocle U (C E) (u,c) b) =
      ∑ a : {a:J // N a c}, Module.finrank K (Zigzag.BasedComplex.coefficientSocle U E (u,a) b) := by
  rw [(coefficientSocleLabelEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE u c b).finrank_eq]
  exact Module.finrank_pi_fintype K

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
