import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitModel
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverCartan
import OAI.Topology.ArtinGroups.Complexes.GeneratorVectorPureLayer

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

lemma finite_weighted_cartan {I J A:Type*} [Fintype I] [Fintype J] [Fintype A]
    (C:Matrix A A ℝ) (a:I → ℝ) (b:J → ℝ) (x:I → A → ℝ) (y:J → A → ℝ) :
    (∑ i,a i • x i) ⬝ᵥ (C *ᵥ (∑ j,b j • y j)) =
      ∑ i,∑ j,a i*b j*(x i ⬝ᵥ (C *ᵥ y j)) := by
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag

noncomputable def fusionOrbitMultiplicity (w:List (V × Bool)) (s:V) (q:ℤ) (v:V) : ℝ :=
  Classical.choose (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)

lemma fusionOrbitMultiplicity_nonneg (w:List (V × Bool)) (s:V) (q:ℤ) (v:V) :
    0 ≤ fusionOrbitMultiplicity m d hd hdiag hm w s q v :=
  (Classical.choose_spec (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)).1

noncomputable def fusionOrbitWeightedVector (w:List (V × Bool)) (s:V) (q:ℤ) :
    FusionVertex (V:=V) m → ℝ := ∑ L,fusionWeight m L • generatorVector Q (Y w s L q)

lemma fusionOrbitLayer_generator (w:List (V × Bool)) (s:V) (q:ℤ) (H:FusionLabel m)
    (α:FusionVertex (V:=V) m) : generatorVector Q (Y w s H q) α =
      (classLevelArray Q (fusionPacketOrbit m d hd hdiag w s H) (α,q):ℝ) :=
  generatorVector_minimalLayer Q _ _ _

lemma fusionOrbitWeightedVector_eq (w:List (V × Bool)) (s:V) (q:ℤ) :
    fusionOrbitWeightedVector m d hd hdiag w s q =
      fusionFold m (fusionOrbitMultiplicity m d hd hdiag hm w s q) := by
  ext ⟨v,L⟩
  simp only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hc:= (Classical.choose_spec (fusionPacketOrbit_count_proportional m d hd hdiag hm w s v q)).2 L
  simpa only [fusionOrbitLayer_generator,fusionFold,
    fusionOrbitMultiplicity,mul_comm] using hc

noncomputable def fusionOrbitLayerHom (w:List (V × Bool)) (s:V) (l k:ℤ) : ℝ :=
  ∑ L,∑ H,fusionWeight m L*fusionWeight m H*(totalHomDimension Q (Y w s L l) (Y w s H k) (k-l):ℝ)

include hm in
lemma fusionOrbitLayerHom_nonneg (w:List (V × Bool)) (s:V) (l k:ℤ) :
    0 ≤ fusionOrbitLayerHom m d hd hdiag w s l k := by
  apply Finset.sum_nonneg
  intro L _
  apply Finset.sum_nonneg
  intro H _
  exact mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le (Nat.cast_nonneg _)

theorem fusionOrbit_weighted_euler (w:List (V × Bool)) (s:V) (l k:ℤ) :
    fusionD0 m * (fusionOrbitMultiplicity m d hd hdiag hm w s l ⬝ᵥ
      (fusionFoldedCartan m d *ᵥ fusionOrbitMultiplicity m d hd hdiag hm w s k)) =
    fusionOrbitLayerHom m d hd hdiag w s l k+fusionOrbitLayerHom m d hd hdiag w s k l := by
  calc
    _ = fusionOrbitWeightedVector m d hd hdiag w s l ⬝ᵥ
        (unfoldedCartan Q *ᵥ fusionOrbitWeightedVector m d hd hdiag w s k) := by
      rw [fusionOrbitWeightedVector_eq m d hd hdiag hm,
        fusionOrbitWeightedVector_eq m d hd hdiag hm,fusionQuiver_cartan,fusion_pairing m hm]
    _ = ∑ L,∑ H,fusionWeight m L*fusionWeight m H*
        ((totalHomDimension Q (Y w s L l) (Y w s H k) (k-l):ℝ)+
         (totalHomDimension Q (Y w s H k) (Y w s L l) (l-k):ℝ)) := by
      rw [fusionOrbitWeightedVector,fusionOrbitWeightedVector,finite_weighted_cartan]
      simp_rw [fusionOrbitLayer_cartan]
    _ = _ := by
      simp only [_root_.mul_add,Finset.sum_add_distrib,fusionOrbitLayerHom]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro L _
      apply Finset.sum_congr rfl
      intro H _
      rw [mul_comm (fusionWeight m H) (fusionWeight m L)]

lemma fusionOrbit_cartan_nonneg (w:List (V × Bool)) (s:V) (l k:ℤ) :
    0 ≤ fusionOrbitMultiplicity m d hd hdiag hm w s l ⬝ᵥ
      (fusionFoldedCartan m d *ᵥ fusionOrbitMultiplicity m d hd hdiag hm w s k) := by
  have h:= fusionOrbit_weighted_euler m d hd hdiag hm w s l k
  have h₁:=fusionOrbitLayerHom_nonneg m d hd hdiag hm w s l k
  have h₂:=fusionOrbitLayerHom_nonneg m d hd hdiag hm w s k l
  exact nonneg_of_mul_nonneg_right (by linarith) (fusionD0_pos m hm)

end HarmonicArtin

end OAI
