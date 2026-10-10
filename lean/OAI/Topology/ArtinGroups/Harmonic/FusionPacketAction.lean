import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketOrbit
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverSimpleEdge
import OAI.Topology.ArtinGroups.Complexes.PacketPermAction

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "C" => fusionOrdinaryMatrix m d hd
local notation "Act" => fusionOrdinaryAction m d hd (K:=K) hdiag

lemma fusionPacket_in_action (s:V) : ∃ x:Artin C,
    Act x=fusionPacketPerm m d hd hdiag s :=
  classPacketPerm_in_action Q (fusionQuiver_no_loops m d hd hdiag) C
    (fusionOrdinaryPresentation m d hd) (fun L=>(s,L)) (fusionColor_orthogonal m d hd hdiag s)

lemma fusionSignedPacket_in_action (a:V × Bool) : ∃ x:Artin C,
    Act x=fusionSignedPacketPerm m d hd hdiag a := by
  obtain ⟨x,hx⟩ := fusionPacket_in_action m d hd hdiag (K:=K) a.1
  cases h:a.2
  · refine ⟨x⁻¹,?_⟩
    rw [map_inv,hx]
    simp [fusionSignedPacketPerm,h]
  · exact ⟨x,by simpa only [fusionSignedPacketPerm,h,↓reduceIte] using hx⟩

lemma fusionWord_in_action (w:List (V × Bool)) : ∃ x:Artin C,
    Act x=fusionWordPacketPerm m d hd hdiag w := by
  induction w with
  | nil => exact ⟨1,map_one Act⟩
  | cons a w ih =>
    obtain ⟨x,hx⟩ := fusionSignedPacket_in_action m d hd hdiag (K:=K) a
    obtain ⟨y,hy⟩ := ih
    exact ⟨x*y,by rw [map_mul,hx,hy]; rfl⟩

lemma fusionOrbit_in_action (w:List (V × Bool)) : ∃ x:Artin C, ∀ s L,
    fusionPacketOrbit m d hd hdiag w s L = unfoldedFrame Q
      (fusionQuiver_no_loops m d hd hdiag) C (fusionOrdinaryPresentation m d hd) x (s,L) := by
  obtain ⟨x,hx⟩ := fusionWord_in_action m d hd hdiag (K:=ℂ) w
  refine ⟨x,fun s L=>?_⟩
  exact congrArg (fun f=> f (initialClass Q (s,L))) hx.symm

lemma fusionOrbit_homDimension (w:List (V × Bool)) (s t:V) (L H:FusionLabel m) (n v:ℤ) :
    classHomDimension Q n v (fusionPacketOrbit m d hd hdiag w s L)
      (fusionPacketOrbit m d hd hdiag w t H) =
    homDimension Q (initialProjective Q (s,L) : BasedComplex Q (K:=ℂ) PUnit.{1})
      (initialProjective Q (t,H) : BasedComplex Q (K:=ℂ) PUnit.{1}) n v := by
  obtain ⟨x,hx⟩ := fusionOrbit_in_action m d hd hdiag w
  rw [hx,hx,unfoldedFrame_homDimension]

end HarmonicArtin

end OAI
