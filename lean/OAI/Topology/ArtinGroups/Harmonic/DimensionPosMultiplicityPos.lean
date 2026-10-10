import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UnfoldedCartanSymm
import OAI.Topology.ArtinGroups.Harmonic.DimensionNonneg
import OAI.Topology.ArtinGroups.Harmonic.FusionSignedPacketExterior

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d
local notation "a" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "c" => fusionOrbitColorMultiplicity m d hd hdiag hm

include hm in
lemma FusionEdge.dimension_pos_of_multiplicity_pos (b:FusionEdge E) (L H:FusionLabel m)
    (h:0<b.multiplicity m L H) : 0<b.dimension m := by
  have ht:0<(b.multiplicity m L H:ℝ)*fusionWeight m H :=
    mul_pos (Nat.cast_pos.mpr h) (fusionWeight_pos m hm H)
  have hs:=lt_of_lt_of_le ht (Finset.single_le_sum
    (fun T (_:T∈Finset.univ)=>mul_nonneg (Nat.cast_nonneg (b.multiplicity m L T)) (fusionWeight_pos m hm T).le)
    (Finset.mem_univ H))
  rw [FusionEdge.dimension_identity m hm] at hs
  exact (mul_pos_iff_of_pos_right (fusionWeight_pos m hm L)).mp hs

include hm in
omit [Fintype V] in
lemma fusion_arrow_color_cartan_neg (r:FusionQuiverArrow m d)
    (hr:r.1.1.1≠r.1.2.1) : C r.1.1.1 r.1.2.1<0 := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply,
    ite_eq_right hr,zero_sub,neg_lt_zero]
  exact FusionEdge.dimension_pos_of_multiplicity_pos m hm (d r.1.1.1 r.1.2.1) r.1.1.2 r.1.2.2 (by have:=r.2.isLt; omega)

lemma fusionOrbitMultiplicity_pos_at_generator (w:List (V × Bool)) (s:V) (q:ℤ)
    (H:FusionLabel m) (i:FusionOrbitLayerIndex m d hd hdiag w s H q) :
    0<a w s q ((Y w s H q).placement i).color.1 := by
  let α:=((Y w s H q).placement i).color
  have hg:0<generatorVector Q (Y w s H q) α := by
    unfold generatorVector
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty {j | ((Y w s H q).placement j).color=α} from ⟨i,rfl⟩)
  have hs:0<fusionOrbitWeightedVector m d hd hdiag w s q α := by
    apply lt_of_lt_of_le (mul_pos (fusionWeight_pos m hm H) hg)
    change fusionWeight m H * generatorVector Q (Y w s H q) α ≤
      (∑ T,fusionWeight m T • generatorVector Q (Y w s T q)) α
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.single_le_sum _ (Finset.mem_univ H)
    intro T _
    exact mul_nonneg (fusionWeight_pos m hm T).le (generatorVector_nonneg Q _ _)
  rw [fusionOrbitWeightedVector_eq m d hd hdiag hm] at hs
  exact (mul_pos_iff_of_pos_left (fusionWeight_pos m hm α.2)).mp hs

lemma fusionOrbit_boundary_absent (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hz:∀ b,b∉U → (∃ v∈U,C b v<0) → a w s q b=0) :
    ∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U) := by
  intro L i hi
  rcases hi with ⟨hi,r,hr,he⟩
  have hb:((Y w s L q).placement i).color.1∉U:=hi
  have hu:r.1.1.1∈U:=hr
  have he':r.1.2=((Y w s L q).placement i).color:=he
  have hn:r.1.1.1≠r.1.2.1 := by
    intro hh
    rw [hh,he'] at hu
    exact hb hu
  have hneg:=fusion_arrow_color_cartan_neg m d hm r hn
  rw [fusionFoldedCartan_symm m d hd] at hneg
  rw [he'] at hneg
  have hc:=hz _ hb ⟨r.1.1.1,hu,hneg⟩
  have hp:=fusionOrbitMultiplicity_pos_at_generator m d hd hdiag hm w s q L i
  exact hp.ne' hc

theorem fusionOrbit_no_isolated_null_layer
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hword:∀ b∈w,b.1≠s)
    (hframe:s∉U) (hframeadj:∃ v∈U,C s v<0)
    (hpos:∀ v∈U,0<a w s q v)
    (hnull:∀ v∈U,(C *ᵥ c w s q U) v=0)
    (hzero:∀ b,b∉U → (∃ v∈U,C b v<0) → a w s q b=0) : False := by
  have hz:=fusionOrbit_null_summand_boundary_zero m d hd hdiag hm w s q U
    (fusionOrbit_boundary_absent m d hd hdiag hm w s q U hzero) hpos hnull
    0 s hframe hframeadj
  rw [fusionOrbitMultiplicity_frame m d hd hdiag hm w s hword] at hz
  exact one_ne_zero hz

end HarmonicArtin

end OAI
