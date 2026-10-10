import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InitialHomSpaceNegative
import OAI.Topology.ArtinGroups.Complexes.SupportedCoefficientCycles
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketAction
import OAI.Topology.ArtinGroups.Complexes.LayerTotalHomDimension

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "C" => fusionOrdinaryMatrix m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

noncomputable def fusionOrbitModel (w:List (V × Bool)) (s:V) (L:FusionLabel m) :
    FiniteModel Q (K:=ℂ) := minimalClassModel Q (O w s L)

lemma fusionOrbitModel_minimal (w:List (V × Bool)) (s:V) (L:FusionLabel m) :
    (fusionOrbitModel m d hd hdiag w s L).complex.IsMinimal Q :=
  minimalClassModel_minimal Q _

abbrev FusionOrbitLayerIndex (w:List (V × Bool)) (s:V) (L:FusionLabel m) (q:ℤ) :=
  {i:(fusionOrbitModel m d hd hdiag w s L).Index //
    ((fusionOrbitModel m d hd hdiag w s L).complex.placement i).level=q}

noncomputable def fusionOrbitLayer (w:List (V × Bool)) (s:V) (L:FusionLabel m) (q:ℤ) :
    BasedComplex Q (K:=ℂ) (FusionOrbitLayerIndex m d hd hdiag w s L q) :=
  (fusionOrbitModel m d hd hdiag w s L).complex.pureLayer Q
     (fusionOrbitModel_minimal m d hd hdiag w s L) q

lemma fusionOrbitLayer_middle (w:List (V × Bool)) (s:V) (L H:FusionLabel m) (l k:ℤ) :
    totalHomDimension Q (fusionOrbitLayer m d hd hdiag w s L l)
      (fusionOrbitLayer m d hd hdiag w s H k) (k-l+1)=0 := by
  obtain ⟨x,hx⟩:=fusionOrbit_in_action m d hd hdiag w
  change classLayerTotalHomDimension Q (O w s L) (O w s H) l k (k-l+1)=0
  rw [hx,hx]
  by_cases he:L=H
  · subst H
    exact
      frameModel_pure_middle_dimension Q hn C (fusionOrdinaryPresentation m d hd) (K:=ℂ) x (s,L) l k
  · have hab:=fusionQuiver_same_color m d hd hdiag s L H he
    exact
      frameModel_pure_orthogonal_middle_dimension Q hn C (fusionOrdinaryPresentation m d hd)
        (K:=ℂ) x hab l k

lemma fusionOrbitModel_negative_homDimension (w:List (V × Bool)) (s t:V)
    (L H:FusionLabel m) (n v:ℤ) (h:n+v<0) :
    homDimension Q (fusionOrbitModel m d hd hdiag w s L).complex
      (fusionOrbitModel m d hd hdiag w t H).complex n v=0 := by
  obtain ⟨x,hx⟩:=fusionOrbit_in_action m d hd hdiag w
  let f (a b:FiniteHomotopyClass Q (K:=ℂ)) :=
    homDimension Q (minimalClassModel Q a).complex (minimalClassModel Q b).complex n v
  change f (O w s L) (O w t H)=0
  rw [hx,hx]
  exact
    frameModel_negative_pair_homDimension Q hn C (fusionOrdinaryPresentation m d hd)
      (K:=ℂ) x (s,L) (t,H) n v h

lemma fusionOrbit_secondary_injective (w:List (V × Bool)) (s t:V)
    (L H:FusionLabel m) (U:Set (FusionVertex (V:=V) m)) (q k n v:ℤ)
    (hcap:(fusionOrbitModel m d hd hdiag w s L).complex.CappedOn Q U q)
    (h:n+v<0) :
    Function.Injective (secondaryOnCohomology Q
      (fusionOrbitModel m d hd hdiag w s L).complex
      (fusionOrbitModel m d hd hdiag w t H).complex
      (fusionOrbitModel_minimal m d hd hdiag w s L)
      (fusionOrbitModel_minimal m d hd hdiag w t H) U q k n v) :=
  secondaryOnCohomology_injective Q _ _ _ _ U q k n v hcap
    (fusionOrbitModel_negative_homDimension m d hd hdiag w s t L H n v h)

lemma fusionOrbitLayer_cartan (w:List (V × Bool)) (s:V) (L H:FusionLabel m) (l k:ℤ) :
    generatorVector Q (fusionOrbitLayer m d hd hdiag w s L l) ⬝ᵥ
      (unfoldedCartan Q).mulVec (generatorVector Q (fusionOrbitLayer m d hd hdiag w s H k)) =
    (totalHomDimension Q (fusionOrbitLayer m d hd hdiag w s L l)
      (fusionOrbitLayer m d hd hdiag w s H k) (k-l):ℝ) +
    (totalHomDimension Q (fusionOrbitLayer m d hd hdiag w s H k)
      (fusionOrbitLayer m d hd hdiag w s L l) (l-k):ℝ) := by
  rw [pure_cartan_euler Q _ _ (fun i=>i.property) (fun i=>i.property),
    fusionOrbitLayer_middle,Nat.cast_zero,sub_zero]

end HarmonicArtin

end OAI
