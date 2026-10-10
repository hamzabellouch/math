import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CanonicalWordLow
import OAI.Topology.ArtinGroups.Harmonic.FusionExpressionAction
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionAppend

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "P" => fusionWordPacketPerm m d hd hdiag (K:=K)

lemma fusionWordPacketPerm_append (w z:List (V×Bool)) : P (w++z)=P w*P z := by
  induction w with
  | nil => exact (_root_.one_mul _).symm
  | cons a w ih => simp only [List.cons_append,fusionWordPacketPerm,ih,_root_.mul_assoc]

lemma fusionSignedPacketPerm_inverse (a:V×Bool) :
    fusionSignedPacketPerm m d hd hdiag (K:=K) (a.1,!a.2)=
      (fusionSignedPacketPerm m d hd hdiag a)⁻¹ := by
  cases a with | mk v b => cases b <;> rfl

lemma fusionWordPacketPerm_inverse (w:List (V×Bool)) :
    P (w.reverse.map fun a=>(a.1,!a.2))=(P w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      fusionWordPacketPerm_append,fusionWordPacketPerm,_root_.mul_one,ih,
      fusionSignedPacketPerm_inverse,mul_inv_rev]

lemma fusionPositiveWord_expand (w:List V) :
    ∃ z:List (FusionVertex (V:=V) m),(∀ a∈z,a.1∈w) ∧
      ∀ x:FiniteHomotopyClass Q (K:=K),positiveWordAction Q z x=P (w.map fun s=>(s,true)) x := by
  induction w with
  | nil => exact ⟨[],by simp,fun _=>rfl⟩
  | cons s w ih =>
    obtain ⟨z,hz,h⟩:=ih
    obtain ⟨a,ha,he⟩:=classPacketPerm_positiveWord Q (K:=K) hn
      (fun L:FusionLabel m=>(s,L)) (fusionColor_orthogonal m d hd hdiag s)
    refine ⟨a++z,?_,?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv|hv
      · obtain ⟨L,rfl⟩:=ha v hv
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hz v hv)
    · intro x
      rw [positiveWordAction_append,he,h]
      rfl

noncomputable def canonicalFusionLow (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  let p:=P (w.map fun s=>(s,true))
  p (classLowerTruncation Q (q-1) (p.symm x))

lemma canonicalFusionLow_eq_ordinary (w:List V) (z:List (FusionVertex (V:=V) m))
    (hz:∀ x:FiniteHomotopyClass Q (K:=K),positiveWordAction Q z x=P (w.map fun s=>(s,true)) x)
    (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    canonicalFusionLow m d hd hdiag w q x=canonicalWordLow Q z q x := by
  have hinv:(P (w.map fun s=>(s,true))).symm x=inverseWordAction Q z x := by
    apply (P (w.map fun s=>(s,true))).injective
    rw [Equiv.apply_symm_apply,← hz,positive_inverseWord Q hn]
  dsimp [canonicalFusionLow,canonicalWordLow]
  rw [hinv,hz]

def canonicalFusionExpression (w:List V) (z:List (V×Bool)) (q:ℤ) : LayerExpression V :=
  .word (w.map fun s=>(s,true))
    (.low (q-1) (.word ((w.map fun s=>(s,true)).reverse.map fun a=>(a.1,!a.2))
      (.layer q (.word z .input))))

lemma canonicalFusionExpression_action (w:List V) (z:List (V×Bool)) (q:ℤ)
    (x:FiniteHomotopyClass Q (K:=K)) :
    fusionExpressionAction m d hd hdiag (canonicalFusionExpression w z q) x=
      canonicalFusionLow m d hd hdiag w q (classLayer Q q (P z x)) := by
  dsimp [canonicalFusionExpression,fusionExpressionAction,canonicalFusionLow]
  rw [fusionWordPacketPerm_inverse]
  rfl

end HarmonicArtin

end OAI
