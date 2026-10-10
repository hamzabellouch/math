import Mathlib
import OAI.Topology.ArtinGroups.Functors.LayerIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.LevelArrayComplexMinimal

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second : J⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]
def levelGeneratorEquiv (p : T → GeneratorPlacement (V × J)) (v:V) (j:J) (d:ℤ) :
    {i : Index N p // (placement N p i).color=(v,j) ∧ (placement N p i).level=d} ≃
      (Σ a : {a:J // N a j}, {i:T // (p i).color=(v,(a:J)) ∧ (p i).level=d}) where
  toFun x := ⟨⟨(p x.val.1).color.2,by
      have hj := congrArg Prod.snd x.property.1
      change x.val.2.val=j at hj
      simpa only [← hj] using x.val.2.property⟩,
    x.val.1,⟨Prod.ext (by have h := congrArg Prod.fst x.property.1; exact h) rfl,x.property.2⟩⟩
  invFun x := ⟨⟨x.2.val,⟨j,by simpa only [x.2.property.1] using x.1.property⟩⟩,
    ⟨Prod.ext (by have h := congrArg Prod.fst x.2.property.1; exact h) rfl,x.2.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (congrArg Prod.snd x.property.1).symm
  right_inv x := by
    apply Sigma.ext
    · apply Subtype.ext
      exact congrArg Prod.snd x.2.property.1
    · have ha := congrArg Prod.snd x.2.property.1
      dsimp only at ha
      apply (Subtype.heq_iff_coe_eq (fun i => by simp only [ha])).mpr
      rfl

omit [DecidableEq T] in
lemma levelArray_label (E : Zigzag.BasedComplex U (K := K) T) (v:V) (j:J) (d:ℤ) :
    (C E).levelArray U ((v,j),d) = ∑ a : {a:J // N a j}, E.levelArray U ((v,a),d) := by
  simp_rw [levelArray_apply]
  erw [Nat.card_congr (levelGeneratorEquiv N E.placement v j d)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

lemma classLevelArray_label (x : FiniteHomotopyClass U (K := K)) (v:V) (j:J) (d:ℤ) :
    classLevelArray U (F x) ((v,j),d) =
      ∑ a : {a:J // N a j}, classLevelArray U x ((v,a),d) := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLevelArray_complex_minimal U _
    (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  conv_rhs => rw [← hx,classLevelArray_complex_minimal U E hE]
  exact levelArray_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E v j d

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
