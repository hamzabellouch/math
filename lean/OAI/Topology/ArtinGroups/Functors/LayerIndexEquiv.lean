import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Functors.HomDualSupportedCycles
import OAI.Topology.ArtinGroups.Functors.ColorPacketPerm

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]
def layerIndexEquiv (p : T → GeneratorPlacement (V × J)) (d : ℤ) :
    Index N (fun i : {i // (p i).level=d} => p i) ≃
      {i : Index N p // (placement N p i).level=d} where
  toFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  invFun x := ⟨⟨x.1.1,x.2⟩,x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq T] in
lemma layer_eq (E : Zigzag.BasedComplex U (K := K) T) (hE : E.IsMinimal U) (d : ℤ) :
    ((C E).pureLayer U (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d).reindex U
      (layerIndexEquiv N E.placement d) = C (E.pureLayer U hE d) := by
  apply ext_placement_differential U
  · rfl
  · rfl

noncomputable def layerComparison (E : Zigzag.BasedComplex U (K := K) T)
    (hE : E.IsMinimal U) (d : ℤ) :
    ChainIsomorphism U
      ((C E).pureLayer U (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
      (C (E.pureLayer U hE d)) := by
  have e := reindexChainIsomorphism U
    ((C E).pureLayer U (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
    (layerIndexEquiv N E.placement d)
  rw [layer_eq] at e
  exact e

lemma classLabel_complex (E : Zigzag.BasedComplex U (K := K) T) :
    F (classOfComplex U E) = classOfComplex U (C E) := rfl

lemma classLabel_layer (d : ℤ) (x : FiniteHomotopyClass U (K := K)) :
    classLayer U d (F x) = F (classLayer U d x) := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLayer_minimal U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  change _ = classOfComplex U (C (E.pureLayer U hE d))
  exact classOfComplex_eq U
    ((layerComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).toHomotopyEquivalence U)

lemma classLayerSocleDimension_label (d : ℤ) (x : FiniteHomotopyClass U (K := K))
    (v:V) (c:J) (b:ℤ) :
    classLayerSocleDimension U d (v,c) b (F x) =
      ∑ a : {a:J // N a c}, classLayerSocleDimension U d (v,a) b x := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLayerSocleDimension_minimal U (C E)
    (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  rw [((layerComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).coefficientSocle U
    (fun i => i.property) (fun i => i.1.property) (v,c) b).finrank_eq,
    coefficientSocle_label_dimension Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (E.pureLayer U hE d) (fun i => i.property)]
  rfl

lemma classLayerTopDimension_label (d : ℤ) (x : FiniteHomotopyClass U (K := K))
    (v:V) (c:J) (b:ℤ) :
    classLayerTopDimension U d (v,c) b (F x) =
      ∑ a : {a:J // N a c}, classLayerTopDimension U d (v,a) b x := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLayerTopDimension_minimal U (C E)
    (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  rw [((layerComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).coefficientTopDual U
    (fun i => i.property) (fun i => i.1.property) (v,c) b).finrank_eq,
    coefficientTop_label_dimension Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (E.pureLayer U hE d) (fun i => i.property)]
  rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
