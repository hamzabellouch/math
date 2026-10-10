import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionSignedPacketExterior
import OAI.Topology.ArtinGroups.Complexes.PacketLayerLowerTruncation
import OAI.Topology.ArtinGroups.Harmonic.FusionColorWord
import OAI.Topology.ArtinGroups.Complexes.PacketTwistTopZero

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "T" => fusionPacketPerm m d hd hdiag (K:=ℂ)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "C" => fusionFoldedCartan m d

lemma fusionPacket_layer_exterior (j v:V) (hv:v≠j)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (L:FusionLabel m) (q:ℤ) :
    classTotalVector Q (classLayer Q q (T j x)) (v,L)=
      classTotalVector Q (classLayer Q q x) (v,L) := by
  simp only [classTotalVector_layer_apply]
  congr 1
  have h:=fusionWord_level_exterior m d hd hdiag [(j,true)] x v L q
    (by simpa only [List.mem_singleton,forall_eq,ne_eq] using hv.symm)
  simpa only [fusionWordPacketPerm,fusionSignedPacketPerm,ite_true,_root_.mul_one] using h

include hm in

theorem fusionPacket_zero_rows_force_top (j:V) (q:ℤ)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=ℂ))
    (ht:∀ H L c,classLayerTopDimension Q (q-1) (j,L) c (x H)=0)
    (a b:V→ℝ)
    (ha:(∑ H,fusionWeight m H • classTotalVector Q (classLayer Q q (x H)))=fusionFold m a)
    (hb:(∑ H,fusionWeight m H • classTotalVector Q (classLayer Q q (T j (x H))))=fusionFold m b)
    (hra:(C *ᵥ a) j=0) (hrb:(C *ᵥ b) j=0) :
    a=b ∧ ∀ H L c,classLayerTopDimension Q q (j,L) c (x H)=0 := by
  have hext:∀ v,v≠j→a v=b v := by
    intro v hv
    let L:FusionLabel m:=fun e=>⟨0,by have :=hm e; omega⟩
    have he:(fusionFold m a) (v,L)=(fusionFold m b) (v,L) := by
      rw [← ha,← hb]
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
        fusionPacket_layer_exterior m d hd hdiag j v hv]
    exact mul_left_cancel₀ (ne_of_gt (fusionWeight_pos m hm L)) he
  have hab:a=b:=color_counts_eq_of_rows m d hdiag j a b hext hra hrb
  have hu (H:FusionLabel m):classLayer Q q (T j (x H))=
      classLayer Q q (T j (classLayer Q q (x H))) :=
    classPacketPerm_unshifted_layer Q hn (fun L=>(j,L))
      (fusionColor_orthogonal m d hd hdiag j) (x H) q (ht H)
  have hc:∀ H,ClassUpperBound Q q (T j (classLayer Q q (x H))) := by
    apply fusionPacket_cap_of_bottom_counts m d hd hdiag hm j
      (fun H=>classLayer Q q (x H)) q
      (fun H=>classLayer_lowerBound Q (x H) q)
      (fun H=>classLayer_upperBound Q (x H) q) a ha
    · simp only [← hu]
      exact hb.trans (congrArg (fusionFold m) hab.symm)
    · exact hra
  refine ⟨hab,fun H=>?_⟩
  exact classPacketPerm_top_zero_of_layer_cap Q hn (fun L=>(j,L))
    (fusionColor_orthogonal m d hd hdiag j) (x H) q (hc H)

end HarmonicArtin

end OAI
