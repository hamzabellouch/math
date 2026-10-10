import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverCartan
import OAI.Topology.ArtinGroups.Complexes.ComplexPacketLowerBound
import OAI.Topology.ArtinGroups.Harmonic.FusionExpandedWordAction
import OAI.Topology.ArtinGroups.Harmonic.RowReflectWordReverse
import OAI.Topology.ArtinGroups.Complexes.LowerTruncationLayerFloor

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "T" => fusionPacketPerm m d hd hdiag (K:=K)
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "C" => fusionFoldedCartan m d

noncomputable def fusionColorWord (j:V) : List (FusionVertex (V:=V) m) :=
  (Finset.univ:Finset (FusionLabel m)).toList.map fun L=>(j,L)

lemma fusionColorWord_action (j:V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (fusionColorWord m j) x=T j x := by
  have h:=fusionExpandedWord_action m d hd hdiag [j] x
  simpa only [fusionExpandedWord,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_cons,List.map_nil,fusionWordPacketPerm,fusionSignedPacketPerm,ite_true,
    fusionColorWord,_root_.mul_one] using h

theorem fusionPacket_pure_two_layer (j:V) (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:ClassLowerBound Q q x) (hh:ClassUpperBound Q q x) :
    classTotalVector Q (classLayer Q q (T j x))-
      classTotalVector Q (classLayer Q (q+1) (T j x))=
      rowReflectWord (unfoldedCartan Q) (fusionColorWord m j) (classTotalVector Q x) := by
  have h:=classSignedVector_positiveWord Q (fusionColorWord m j) x
  rw [fusionColorWord_action m d hd hdiag j x] at h
  rw [classSignedVector_two_levels Q (T j x) q
    (classPacketPerm_lower_bound Q hn _ (fusionColor_orthogonal m d hd hdiag j) x hl)
    (classPacketPerm_upper_add_one Q hn _ (fusionColor_orthogonal m d hd hdiag j) x hh),
    classSignedVector_pure Q x q hl hh,rowReflectWord_smul] at h
  have h':=congrArg (fun z:FusionVertex (V:=V) m→ℝ=>cochainSign (K:=ℝ) q • z) h
  simpa only [smul_smul,cochainSign_mul_self,one_smul] using h'

include hm in
lemma fusionPacket_weighted_two_layer (j:V)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:∀ L,ClassLowerBound Q q (x L)) (hh:∀ L,ClassUpperBound Q q (x L))
    (a:V→ℝ) (ha:(∑ L,fusionWeight m L • classTotalVector Q (x L))=fusionFold m a) :
    (∑ L,fusionWeight m L • classTotalVector Q (classLayer Q q (T j (x L))))-
      (∑ L,fusionWeight m L • classTotalVector Q (classLayer Q (q+1) (T j (x L))))=
      fusionFold m (rowReflect C j a) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub,fusionPacket_pure_two_layer m d hd hdiag j _ q (hl _) (hh _),
    ← rowReflectWord_smul]
  rw [← rowReflectWord_sum,ha,fusionQuiver_cartan]
  exact fusion_reflection_intertwining m hm d hdiag j a

include hdiag in

omit [Fintype E] [DecidableEq E] in
lemma color_counts_eq_of_rows (j:V) (a b:V→ℝ)
    (hext:∀ v,v≠j→a v=b v) (ha:(C *ᵥ a) j=0) (hb:(C *ᵥ b) j=0) : a=b := by
  have hdif:(C *ᵥ (a-b)) j=0 := by rw [Matrix.mulVec_sub,Pi.sub_apply,ha,hb,sub_self]
  have hsum:(C *ᵥ (a-b)) j=2*(a j-b j) := by
    change (∑ v,C j v*(a v-b v))=_
    rw [Finset.sum_eq_single j]
    · simp [fusionFoldedCartan,hdiag,FusionEdge.dimension]
    · intro v hv hvj
      rw [hext v hvj,sub_self,MulZeroClass.mul_zero]
    · simp
  funext v
  by_cases hv:v=j
  · subst v
    rw [hsum] at hdif
    linarith
  · exact hext v hv

include hm in

theorem fusionPacket_cap_of_bottom_counts (j:V)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hl:∀ L,ClassLowerBound Q q (x L)) (hh:∀ L,ClassUpperBound Q q (x L))
    (a:V→ℝ) (ha:(∑ L,fusionWeight m L • classTotalVector Q (x L))=fusionFold m a)
    (hb:(∑ L,fusionWeight m L • classTotalVector Q (classLayer Q q (T j (x L))))=fusionFold m a)
    (hr:(C *ᵥ a) j=0) : ∀ L,ClassUpperBound Q q (T j (x L)) := by
  have he:=fusionPacket_weighted_two_layer m d hd hdiag hm j x q hl hh a ha
  have hr':rowReflect C j a=a := by simp only [rowReflect,hr,zero_smul,sub_zero]
  rw [hr',hb] at he
  have hz:(∑ L,fusionWeight m L • classTotalVector Q (classLayer Q (q+1) (T j (x L))))=0 := by
    exact sub_eq_self.mp he
  intro L
  apply classUpperBound_of_upper_layer_zero Q _ q
    (classPacketPerm_upper_add_one Q hn _ (fusionColor_orthogonal m d hd hdiag j) _ (hh L))
  funext α
  have hs:=congrFun hz α
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hs ⊢
  have hnz:∀ H∈(Finset.univ:Finset (FusionLabel m)),0≤fusionWeight m H*
      classTotalVector Q (classLayer Q (q+1) (T j (x H))) α :=
    fun H _=>mul_nonneg (fusionWeight_pos m hm H).le (classTotalVector_layer_nonneg Q _ _ _)
  have hlz: fusionWeight m L*classTotalVector Q (classLayer Q (q+1) (T j (x L))) α=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnz).mp hs L (Finset.mem_univ _)
  exact (mul_eq_zero.mp hlz).resolve_left (ne_of_gt (fusionWeight_pos m hm L))

end HarmonicArtin

end OAI
