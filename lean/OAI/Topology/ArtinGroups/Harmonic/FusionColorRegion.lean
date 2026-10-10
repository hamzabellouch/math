import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitMultiplicity
import OAI.Topology.ArtinGroups.Realizations.FusionWeightedHom
import OAI.Topology.ArtinGroups.Complexes.ColorBoundary

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag

def fusionColorRegion (U:Set V) : Set (FusionVertex (V:=V) m) := {a | a.1∈U}

noncomputable def fusionOrbitColorLayer (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (L:FusionLabel m) :=
  colorRestriction Q (Y w s L q) (fusionColorRegion m U) (fun i=>i.property) (hb L)

noncomputable def fusionOrbitColorMultiplicity (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V) : V → ℝ :=
  fun v=>if v∈U then fusionOrbitMultiplicity m d hd hdiag hm w s q v else 0

lemma fusionOrbitColor_generator (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (L:FusionLabel m) (a:FusionVertex (V:=V) m) :
    generatorVector Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L) a=
      if a.1∈U then generatorVector Q (Y w s L q) a else 0 := by
  exact colorRestriction_generatorVector Q (Y w s L q) (fusionColorRegion m U)
    (fun i=>i.property) (hb L) a

lemma fusionOrbitColor_weightedVector (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U)) :
    (∑ L,fusionWeight m L • generatorVector Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L))=
      fusionFold m (fusionOrbitColorMultiplicity m d hd hdiag hm w s q U) := by
  funext a
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm w s q) a
  simp only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
  simp_rw [fusionOrbitColor_generator]
  by_cases ha:a.1∈U
  · simp only [ha,ite_true]
    simpa only [fusionFold,fusionOrbitColorMultiplicity,ha,ite_true] using h
  · simp only [ha,ite_false,MulZeroClass.mul_zero,
      Finset.sum_const_zero,fusionFold,fusionOrbitColorMultiplicity]

lemma fusionOrbitColor_middle (w:List (V × Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (L H:FusionLabel m) :
    totalHomDimension Q (fusionOrbitColorLayer m d hd hdiag w s q U hb L) (Y w s H k) (k-q+1)=0 := by
  apply fusionOrbit_summand_middle m d hd hdiag w s L H _ q k
    (blockInclusionMap Q (Y w s L q) _ (pure_color_block Q _ _ (fun i=>i.property) (hb L)))
    (blockProjectionMap Q (Y w s L q) _ (pure_color_block Q _ _ (fun i=>i.property) (hb L)))
  convert block_inclusion_projection Q (Y w s L q)
    {i | ((Y w s L q).placement i).color∈fusionColorRegion m U} using 1
  · rfl
  · apply Matrix.ext
    intro i j
    simp only [projectiveIdentity,Matrix.diagonal_apply]
    by_cases h:i=j <;> simp only [h,ite_true,ite_false]
    rfl

lemma fusionOrbitColor_cartan_nonneg (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (q k:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U)) :
    0≤fusionOrbitColorMultiplicity m d hd hdiag hm w s q U ⬝ᵥ
      (fusionFoldedCartan m d *ᵥ fusionOrbitMultiplicity m d hd hdiag hm w s k) := by
  have h:0≤(∑ L,fusionWeight m L • generatorVector Q
        (fusionOrbitColorLayer m d hd hdiag w s q U hb L)) ⬝ᵥ
      (unfoldedCartan Q *ᵥ fusionOrbitWeightedVector m d hd hdiag w s k) := by
    rw [fusionOrbitWeightedVector,finite_weighted_cartan]
    apply Finset.sum_nonneg
    intro L _
    apply Finset.sum_nonneg
    intro H _
    apply mul_nonneg (mul_pos (fusionWeight_pos m hm L) (fusionWeight_pos m hm H)).le
    rw [pure_cartan_euler Q _ _ (fun i=>i.val.property) (fun i=>i.property),
      fusionOrbitColor_middle,Nat.cast_zero,sub_zero]
    positivity
  rw [fusionOrbitColor_weightedVector m d hd hdiag hm,
    fusionOrbitWeightedVector_eq m d hd hdiag hm,fusionQuiver_cartan,fusion_pairing m hm] at h
  exact nonneg_of_mul_nonneg_right h (fusionD0_pos m hm)

end HarmonicArtin

end OAI
