import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitMultiplicity
import OAI.Topology.ArtinGroups.Harmonic.FinsuppMapDomainFiber
import OAI.Topology.ArtinGroups.Complexes.PacketPermExterior

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionSignedPacket_exterior (b:V × Bool) (x:FiniteHomotopyClass Q (K:=ℂ))
    (a:GeneratorPlacement (FusionVertex (V:=V) m)) (ha:b.1≠a.color.1) :
    classGeneratorArray Q (fusionSignedPacketPerm m d hd hdiag b x) a=classGeneratorArray Q x a := by
  have he:∀ L:FusionLabel m,(b.1,L)≠a.color :=
    fun L h=>ha (congrArg Prod.fst h)
  cases hb:b.2
  · simpa [fusionSignedPacketPerm,hb,fusionPacketPerm] using
      classPacketPerm_inverse_exterior Q hn _ (fusionColor_orthogonal m d hd hdiag b.1) x a he
  · simpa [fusionSignedPacketPerm,hb,fusionPacketPerm] using
      classPacketPerm_exterior Q hn _ (fusionColor_orthogonal m d hd hdiag b.1) x a he

lemma fusionWord_exterior (w:List (V × Bool)) (x:FiniteHomotopyClass Q (K:=ℂ))
    (a:GeneratorPlacement (FusionVertex (V:=V) m))
    (ha:∀ b∈w,b.1≠a.color.1) :
    classGeneratorArray Q (fusionWordPacketPerm m d hd hdiag w x) a=classGeneratorArray Q x a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change classGeneratorArray Q (fusionSignedPacketPerm m d hd hdiag b
      (fusionWordPacketPerm m d hd hdiag w x)) a=_
    rw [fusionSignedPacket_exterior m d hd hdiag b _ a (ha b (by simp))]
    exact ih (fun b hb=>ha b (by simp [hb]))

lemma fusionWord_level_exterior (w:List (V × Bool)) (x:FiniteHomotopyClass Q (K:=ℂ))
    (v:V) (L:FusionLabel m) (q:ℤ) (hv:∀ b∈w,b.1≠v) :
    classLevelArray Q (fusionWordPacketPerm m d hd hdiag w x) ((v,L),q)=
      classLevelArray Q x ((v,L),q) := by
  apply finsupp_mapDomain_fiber
  intro a ha
  apply fusionWord_exterior m d hd hdiag
  have he:a.color.1=v:=congrArg (fun z=>(z.1:FusionVertex (V:=V) m).1) ha
  simpa only [he] using hv

lemma fusionOrbit_frame_level (w:List (V × Bool)) (s:V) (H L:FusionLabel m) (q:ℤ)
    (hs:∀ b∈w,b.1≠s) :
    classLevelArray Q (fusionPacketOrbit m d hd hdiag w s H) ((s,L),q)=
      if H=L ∧ q=0 then 1 else 0 := by
  rw [fusionPacketOrbit,fusionWord_level_exterior m d hd hdiag w _ s L q hs,
    classLevelArray_initial]
  simp only [Prod.mk.injEq,true_and]

lemma fusionOrbitMultiplicity_frame (hm:∀ e,2 ≤ m e)
    (w:List (V × Bool)) (s:V) (hs:∀ b∈w,b.1≠s) :
    fusionOrbitMultiplicity m d hd hdiag hm w s 0 s=1 := by
  let L:FusionLabel m:=fun e=>⟨0,by have:=hm e; omega⟩
  have hc:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm w s 0) (s,L)
  simp only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    fusionOrbitLayer_generator,fusionFold] at hc
  simp_rw [fusionOrbit_frame_level m d hd hdiag w s _ _ _ hs] at hc
  simp only [and_true,↓reduceIte,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    mul_ite,_root_.mul_one,MulZeroClass.mul_zero,Finset.sum_ite_eq',Finset.mem_univ] at hc
  apply mul_right_cancel₀ (fusionWeight_pos m hm L).ne'
  rw [_root_.one_mul]
  simpa only [mul_comm] using hc.symm

end HarmonicArtin

end OAI
