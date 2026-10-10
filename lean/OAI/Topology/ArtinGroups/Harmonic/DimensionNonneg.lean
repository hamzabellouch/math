import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Extend
import OAI.Topology.ArtinGroups.Harmonic.FusionColorRegion

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
lemma FusionEdge.dimension_nonneg (b:FusionEdge E) : 0≤b.dimension m := by
  let L:FusionLabel m:=fun e=>⟨0,by have:=hm e; omega⟩
  have hs:0≤∑ H,(b.multiplicity m L H:ℝ)*fusionWeight m H :=
    Finset.sum_nonneg (fun H _=>mul_nonneg (Nat.cast_nonneg _) (fusionWeight_pos m hm H).le)
  rw [FusionEdge.dimension_identity m hm] at hs
  exact nonneg_of_mul_nonneg_left hs (fusionWeight_pos m hm L)

include hd in
omit [Fintype E] [DecidableEq E] [Fintype V] in
lemma fusionFoldedCartan_symm (s t:V) : C s t=C t s := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply]
  rw [hd s t]
  simp only [eq_comm]

include hm in
omit [Fintype V] in
lemma fusionFoldedCartan_off_nonpos (s t:V) (hst:s≠t) : C s t≤0 := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply,
    ite_eq_right hst,zero_sub]
  exact neg_nonpos.mpr (FusionEdge.dimension_nonneg m hm (d s t))

theorem fusionOrbit_null_summand_boundary_zero
    (w:List (V × Bool)) (s:V) (q:ℤ) (U:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m U))
    (hpos:∀ v∈U,0<a w s q v)
    (hnull:∀ v∈U,(C *ᵥ c w s q U) v=0) :
    ∀ k b,b∉U → (∃ v∈U,C b v<0) → a w s k b=0 := by
  have hc:∀ v,0≤c w s q U v := by
    intro v
    unfold fusionOrbitColorMultiplicity
    split_ifs
    · exact fusionOrbitMultiplicity_nonneg m d hd hdiag hm w s q v
    · exact le_rfl
  have hs:∀ v∉U,c w s q U v=0 := by
    intro v hv
    simp only [fusionOrbitColorMultiplicity,hv,ite_false]
  have hp:∀ v∈U,0<c w s q U v := by
    intro v hv
    simpa only [fusionOrbitColorMultiplicity,hv,ite_true] using hpos v hv
  intro k b hbu hbv
  have hy:=fusionOrbitMultiplicity_nonneg m d hd hdiag hm w s k
  have hn:=NullBoundary.null_pairing_nonpos C U (c w s q U) (a w s k)
    (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
    hc hs hnull hy
  have he:=le_antisymm hn (fusionOrbitColor_cartan_nonneg m d hd hdiag hm w s q k U hb)
  exact NullBoundary.null_pairing_eq_zero_boundary C U (c w s q U) (a w s k)
    (fusionFoldedCartan_symm m d hd) (fusionFoldedCartan_off_nonpos m d hm)
    hc hs hp hnull hy he b hbu hbv

end HarmonicArtin

end OAI
