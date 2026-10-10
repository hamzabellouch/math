import Mathlib
import OAI.Topology.ArtinGroups.Functors.ComplexInitial
import OAI.Topology.ArtinGroups.Realizations.FusionWeightSplit
import OAI.Topology.ArtinGroups.Harmonic.FusionExpressionAction

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "P" => fusionExpressionAction m d hd hdiag (K:=ℂ)

noncomputable def fusionExpressionOrbit (t:LayerExpression V) (s:V) (L:FusionLabel m) :
    FiniteHomotopyClass Q (K:=ℂ) := P t (initialClass Q (s,L))

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
local notation "F" => ReversibleQuiver.Iso.classMap (fusionQuiverSplit m e d hd) (K:=ℂ)
local notation "T" => StringFunctor.expressionAction Qr step hstep N hN (K:=ℂ) hnr
local notation "O" => fusionExpressionOrbit m d hd hdiag

lemma fusionExpressionOrbit_split (t:LayerExpression V) :
    ∃ z:LayerExpression (FusionVertex (V:=V) mr),∀ s L,
      F (O t s L)=T z (initialClass U ((s,restLabel m e L),L e)) := by
  obtain ⟨z,hz⟩:=fusionExpression_split m d hd hdiag e (K:=ℂ) t
  refine ⟨z,fun s L=>?_⟩
  rw [fusionExpressionOrbit,hz,(fusionQuiverSplit m e d hd).classMap_initial]
  rfl

variable (hm : ∀ e, 2 ≤ m e)
include hm in
lemma fusionExpressionOrbit_count_slice (t:LayerExpression V) (s v:V) (q:ℤ)
    (r a:FusionLabel mr) : ∃ c:ℝ,∀ j,
    (∑ i,stringWeight (m e) i*
      (classLevelArray Q (O t s ((labelSplit m e).symm (a,i))) ((v,(labelSplit m e).symm (r,j)),q):ℝ))=
        c*stringWeight (m e) j := by
  obtain ⟨z,hz⟩:=fusionExpressionOrbit_split m d hd hdiag e t
  obtain ⟨c,_,h⟩:=StringFunctor.string_expressionOrbit_count_proportional Qr step hstep hnr (m e) (hm e)
    z (s,a) (v,r) q
  refine ⟨c,fun j=>?_⟩
  calc
    _ = ∑ i,stringWeight (m e) i * (classLevelArray U (T z (initialClass U ((s,a),i))) (((v,r),j),q):ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (fusionQuiverSplit m e d hd).classMap_levelArray,hz]
      simp only [fusionQuiverSplit,fusionVertexSplit,Equiv.coe_fn_mk,
        labelSplit_symm_at,labelSplit_symm_rest]
    _ = _ := h j

include hm

theorem fusionExpressionOrbit_count_proportional (t:LayerExpression V) (s v:V) (q:ℤ) :
    ∃ c:ℝ,0≤c ∧ ∀ L,
      (∑ H,fusionWeight m H*(classLevelArray Q (O t s H) ((v,L),q):ℝ))=c*fusionWeight m L :=
  fusion_weighted_matrix_proportional m hm _
    (fun e=>fusionExpressionOrbit_count_slice m d hd hdiag e hm t s v q)

end HarmonicArtin

end OAI
