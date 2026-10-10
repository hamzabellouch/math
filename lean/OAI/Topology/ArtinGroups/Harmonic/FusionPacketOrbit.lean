import Mathlib
import OAI.Topology.ArtinGroups.Functors.ComplexInitial
import OAI.Topology.ArtinGroups.Functors.ComplexPureLayer
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketPerm
import OAI.Topology.ArtinGroups.Realizations.FusionWeightSplit

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionPacketOrbit (w:List (V × Bool)) (s:V) (L:FusionLabel m) :
    FiniteHomotopyClass Q (K:=ℂ) :=
  fusionWordPacketPerm m d hd hdiag w (initialClass Q (s,L))

variable (e:E)
local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=ℂ)
local notation "W" => StringFunctor.wordPacketPerm Qr step hstep N hN (K:=ℂ) hnr
local notation "O" => fusionPacketOrbit m d hd hdiag

lemma fusionOrbit_split (w:List (V × Bool)) : ∃ z:List (FusionVertex (V:=V) mr × Bool),
    ∀ s L,F (O w s L)=W z (initialClass U ((s,restLabel m e L),L e)) := by
  obtain ⟨z,hz⟩ := fusionWord_split m d hd hdiag e (K:=ℂ) w
  refine ⟨z,fun s L=>?_⟩
  rw [fusionPacketOrbit,hz,(fusionQuiverSplit m e d hd).classMap_initial]
  rfl

variable (hm:∀ e,2 ≤ m e)

include hm in
lemma fusionOrbit_socle_slice (w:List (V × Bool)) (s v:V) (q b:ℤ)
    (r t:FusionLabel mr) : ∃ c:ℝ, ∀ j,
    (∑ i,stringWeight (m e) i *
      (classLayerSocleDimension Q q (v,(labelSplit m e).symm (r,j)) b
        (O w s ((labelSplit m e).symm (t,i))):ℝ)) = c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩ := fusionOrbit_split m d hd hdiag e w
  obtain ⟨c,hc,h⟩ := StringFunctor.string_wordOrbit_socle_proportional Qr step hstep hnr (m e) (hm e)
    z (s,t) (v,r) q b
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLayerSocleDimension U q ((v,r),j) b
        (W z (initialClass U ((s,t),i))):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_socleDimension,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm in
lemma fusionOrbit_top_slice (w:List (V × Bool)) (s v:V) (q b:ℤ)
    (r t:FusionLabel mr) : ∃ c:ℝ, ∀ j,
    (∑ i,stringWeight (m e) i *
      (classLayerTopDimension Q q (v,(labelSplit m e).symm (r,j)) b
        (O w s ((labelSplit m e).symm (t,i))):ℝ)) = c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩ := fusionOrbit_split m d hd hdiag e w
  obtain ⟨c,hc,h⟩ := StringFunctor.string_wordOrbit_top_proportional Qr step hstep hnr (m e) (hm e)
    z (s,t) (v,r) q b
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLayerTopDimension U q ((v,r),j) b
        (W z (initialClass U ((s,t),i))):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_topDimension,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm in
lemma fusionOrbit_count_slice (w:List (V × Bool)) (s v:V) (q:ℤ)
    (r t:FusionLabel mr) : ∃ c:ℝ, ∀ j,
    (∑ i,stringWeight (m e) i *
      (classLevelArray Q (O w s ((labelSplit m e).symm (t,i))) ((v,(labelSplit m e).symm (r,j)),q):ℝ)) =
        c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩ := fusionOrbit_split m d hd hdiag e w
  obtain ⟨c,hc,h⟩ := StringFunctor.string_wordOrbit_count_proportional Qr step hstep hnr (m e) (hm e)
    z (s,t) (v,r) q
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLevelArray U (W z (initialClass U ((s,t),i))) (((v,r),j),q):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_levelArray,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm

theorem fusionPacketOrbit_socle_proportional (w:List (V × Bool)) (s v:V) (q b:ℤ) :
    ∃ c:ℝ,0≤c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLayerSocleDimension Q q (v,L) b (O w s H):ℝ)) =
        c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionOrbit_socle_slice m d hd hdiag e hm w s v q b)

theorem fusionPacketOrbit_top_proportional (w:List (V × Bool)) (s v:V) (q b:ℤ) :
    ∃ c:ℝ,0≤c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLayerTopDimension Q q (v,L) b (O w s H):ℝ)) =
        c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionOrbit_top_slice m d hd hdiag e hm w s v q b)

theorem fusionPacketOrbit_count_proportional (w:List (V × Bool)) (s v:V) (q:ℤ) :
    ∃ c:ℝ,0≤c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLevelArray Q (O w s H) ((v,L),q):ℝ)) =
        c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionOrbit_count_slice m d hd hdiag e hm w s v q)

end HarmonicArtin

end OAI
