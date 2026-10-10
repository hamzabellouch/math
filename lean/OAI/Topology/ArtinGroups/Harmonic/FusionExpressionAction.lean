import Mathlib
import OAI.Topology.ArtinGroups.Functors.ComplexLowerTruncation
import OAI.Topology.ArtinGroups.Functors.ComplexPureLayer
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketPerm
import OAI.Topology.ArtinGroups.Harmonic.LayerExpression

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionExpressionAction : LayerExpression V →
    FiniteHomotopyClass Q (K:=K) → FiniteHomotopyClass Q (K:=K)
  | .input,x=>x
  | .word w t,x=>fusionWordPacketPerm m d hd hdiag w (fusionExpressionAction t x)
  | .low k t,x=>classLowerTruncation Q k (fusionExpressionAction t x)
  | .layer k t,x=>classLayer Q k (fusionExpressionAction t x)

variable (e:E)
local notation "mr" => (fun f:FusionRest e=>m f)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restFusion_symmetric d hd e)
local notation "hnr" => fusionQuiver_no_loops mr dr (restFusion_symmetric d hd e) (restFusion_diagonal d hdiag e)
local notation "step" => fusionFactorStep m e d
local notation "hstep" => fusionFactorStep_reverse m e d hd
local notation "N" => stringAdjacent (m e)
local notation "hN" => stringAdjacent_symm (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step hstep N hN
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=K)
local notation "T" => StringFunctor.expressionAction Qr step hstep N hN (K:=K) hnr
local notation "P" => fusionExpressionAction m d hd hdiag (K:=K)

lemma fusionExpression_split (t:LayerExpression V) :
    ∃ z:LayerExpression (FusionVertex (V:=V) mr),∀ x,F (P t x)=T z (F x) := by
  induction t with
  | input => exact ⟨.input,fun _=>rfl⟩
  | word w t ih =>
    obtain ⟨z,hz⟩:=ih
    obtain ⟨w',hw⟩:=fusionWord_split m d hd hdiag e (K:=K) w
    refine ⟨.word w' z,fun x=>?_⟩
    change F (fusionWordPacketPerm m d hd hdiag w (P t x))=
      StringFunctor.wordPacketPerm Qr step hstep N hN hnr w' (T z (F x))
    rw [hw,hz]
  | low k t ih =>
    obtain ⟨z,hz⟩:=ih
    refine ⟨.low k z,fun x=>?_⟩
    change F (classLowerTruncation Q k (P t x))=classLowerTruncation U k (T z (F x))
    rw [(fusionQuiverSplit m e d hd).classMap_lowerTruncation,hz]
  | layer k t ih =>
    obtain ⟨z,hz⟩:=ih
    refine ⟨.layer k z,fun x=>?_⟩
    change F (classLayer Q k (P t x))=classLayer U k (T z (F x))
    rw [(fusionQuiverSplit m e d hd).classMap_layer,hz]

end HarmonicArtin

end OAI
