import Mathlib
import OAI.Topology.ArtinGroups.Functors.ReversibleQuiverMap
import OAI.Topology.ArtinGroups.Harmonic.FusionFactorStep
import OAI.Topology.ArtinGroups.Complexes.OptionSumEquiv
import OAI.Topology.ArtinGroups.Functors.WordPacketPermAppend

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

include hdiag in
omit [Fintype V] [DecidableEq V] in
lemma fusionColor_orthogonal (s:V) :
    Pairwise fun a b:FusionLabel m => OrthogonalVertices Q (s,a) (s,b) :=
  fun a b h=>fusionQuiver_same_color m d hd hdiag s a b h

noncomputable def fusionPacketPerm (s:V) : Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  classPacketPerm Q hn (fun L:FusionLabel m=>(s,L)) (fusionColor_orthogonal m d hd hdiag s)

noncomputable def fusionSignedPacketPerm (a:V × Bool) :
    Equiv.Perm (FiniteHomotopyClass Q (K:=K)) :=
  if a.2 then fusionPacketPerm m d hd hdiag a.1
  else (fusionPacketPerm m d hd hdiag a.1)⁻¹

noncomputable def fusionWordPacketPerm : List (V × Bool) →
    Equiv.Perm (FiniteHomotopyClass Q (K:=K))
  | [] => 1
  | a::w => fusionSignedPacketPerm m d hd hdiag a * fusionWordPacketPerm w

variable (e:E)
local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))

include hd in
omit [Fintype E] [Fintype V] [DecidableEq V] in
lemma restFusion_symmetric : ∀ s t, dr s t=dr t s :=
  fun s t=>congrArg (FusionEdge.removeFactor e) (hd s t)

include hdiag in
omit [Fintype E] [Fintype V] [DecidableEq V] in
lemma restFusion_diagonal : ∀ s, dr s s=.units 0 := by
  intro s
  change FusionEdge.removeFactor e (d s s) = _
  rw [hdiag]
  rfl

local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=K)
local notation "W" => StringFunctor.wordPacketPerm Qr step hstep N hN (K:=K) hnr

lemma fusionPacket_split (s:V) : ∃ w:List (FusionVertex (V:=V) mr × Bool),
    ∀ x, F (fusionPacketPerm m d hd hdiag s x) = W w (F x) := by
  let v : (FusionLabel mr × StringLabel (m e)) → FusionVertex (V:=V) mr × StringLabel (m e) :=
    fun p=>((s,p.1),p.2)
  have hv : Pairwise fun a b=>OrthogonalVertices U (v a) (v b) := by
    rintro ⟨a,i⟩ ⟨b,j⟩ hab
    have h := (fusionQuiverSplit m e d hd).orthogonal
      (fusionQuiver_same_color m d hd hdiag s ((labelSplit m e).symm (a,i))
        ((labelSplit m e).symm (b,j)) (fun h=>hab ((labelSplit m e).symm.injective h)))
    simpa only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
      labelSplit_symm_at,labelSplit_symm_rest,v] using h
  obtain ⟨l,hl⟩ := exists_packetGroupWord U
    ((fusionQuiverSplit m e d hd).loopless hn) (K:=K) v hv
  refine ⟨l.map fun r=>((s,r),true),?_⟩
  intro x
  rw [fusionPacketPerm,(fusionQuiverSplit m e d hd).classMap_packet]
  erw [classPacketPerm_reindex U _ _ _ (labelSplit m e).symm]
  have he : (fun a=> (fusionQuiverSplit m e d hd).vertex (s,(labelSplit m e).symm a)) = v := by
    funext a
    exact Prod.ext (Prod.ext rfl (labelSplit_symm_rest m e a.1 a.2))
      (labelSplit_symm_at m e a.1 a.2)
  have hp : classPacketPerm U (K:=K) ((fusionQuiverSplit m e d hd).loopless hn)
      (((fusionQuiverSplit m e d hd).vertex ∘ fun L=>(s,L)) ∘ (labelSplit m e).symm)
      (fun a b hab=>(fusionQuiverSplit m e d hd).orthogonal
        (fusionColor_orthogonal m d hd hdiag s
          (fun hh=>hab ((labelSplit m e).symm.injective hh)))) =
      classPacketPerm U ((fusionQuiverSplit m e d hd).loopless hn) v hv := by
    congr 1
  erw [hp]
  rw [hl]
  have hw := StringFunctor.wordPacketPerm_positive Qr step hstep N hN (K:=K) hnr
    (l.map (fun r=>(s,r)))
  simp only [List.map_map] at hw
  erw [hw]
  rfl

lemma fusionSignedPacket_split (a:V × Bool) : ∃ w:List (FusionVertex (V:=V) mr × Bool),
    ∀ x, F (fusionSignedPacketPerm m d hd hdiag a x) = W w (F x) := by
  obtain ⟨w,hw⟩ := fusionPacket_split m d hd hdiag e (K:=K) a.1
  cases hb:a.2
  · refine ⟨w.reverse.map (fun z=>(z.1,!z.2)),?_⟩
    intro x
    rw [StringFunctor.wordPacketPerm_inverse]
    apply (W w).injective
    change W w (F (fusionSignedPacketPerm m d hd hdiag a x)) = W w ((W w).symm (F x))
    rw [Equiv.apply_symm_apply]
    erw [← hw]
    simp only [fusionSignedPacketPerm,hb]
    change F (fusionPacketPerm m d hd hdiag a.1
      ((fusionPacketPerm m d hd hdiag a.1).symm x)) = F x
    rw [Equiv.apply_symm_apply]
  · refine ⟨w,?_⟩
    simpa only [fusionSignedPacketPerm,hb,↓reduceIte] using hw

lemma fusionWord_split (w:List (V × Bool)) : ∃ z:List (FusionVertex (V:=V) mr × Bool),
    ∀ x, F (fusionWordPacketPerm m d hd hdiag w x) = W z (F x) := by
  induction w with
  | nil => exact ⟨[],fun _=>rfl⟩
  | cons a w ih =>
    obtain ⟨z,hz⟩ := ih
    obtain ⟨t,ht⟩ := fusionSignedPacket_split m d hd hdiag e (K:=K) a
    refine ⟨t++z,?_⟩
    intro x
    change F (fusionSignedPacketPerm m d hd hdiag a (fusionWordPacketPerm m d hd hdiag w x)) = _
    rw [ht,hz,StringFunctor.wordPacketPerm_append]
    rfl

end HarmonicArtin

end OAI
