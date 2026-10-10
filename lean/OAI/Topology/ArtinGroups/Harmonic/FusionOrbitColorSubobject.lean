import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionSubobjectCartanInequality

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
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "a" => fusionOrbitColorMultiplicity m d hd hdiag hm

theorem fusionOrbitColor_subobject_separation
    (w:List (V×Bool)) (s:V) (q k:ℤ) (I J:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m I))
    {B:Type} {R:B→FusionLabel m→Type} [∀ b L,Fintype (R b L)]
    (T:∀ b L,BasedComplex Q (K:=ℂ) (R b L))
    (hT:∀ b L i,((T b L).placement i).level=q)
    (incl:∀ b L,TermwiseSplitInjection Q (T b L)
      (fusionOrbitColorLayer m d hd hdiag w s q I hb L))
    (c:V→ℝ) (σ:B→V→ℝ)
    (hsvec:∀ b,(∑ L,fusionWeight m L • generatorVector Q (T b L))=fusionFold m (σ b))
    (hsupp:∀ b L i,((T b L).placement i).color.1∈J)
    (hσ:∀ b v,v∉J→σ b v=0)
    (hc:∀ v,0≤c v) (hcSupp:∀ v,v∉I→c v=0) (hcPos:∀ v,v∈I→0<c v)
    (hcNull:∀ v,v∈I→(C *ᵥ c) v=0) (hext:∀ v,v∉J→a w s q I v=c v)
    (hint:(fun j:J=>a w s q I j-c j)∈interior (convexHull ℝ (Set.range fun b:B=>(fun j:J=>σ b j))))
    (hsoc:∀ H α,α.1∈J→∀ r,coefficientSocle Q (Y w s H k) α r=⊥) :
    (∀ v∉I,(∃ u∈I,C v u<0)→μ w s k v=0) ∧
    (∀ j∈J,(C *ᵥ μ w s k) j=0) ∧
    fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L)
      (fun H=>Y w s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y w s H k)
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L) (q-k)=0 := by
  let T₀:=fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L
  let incl₀ L:=blockInclusionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  let proj₀ L:=blockProjectionMap Q (Y w s L q) _
    (pure_color_block Q _ _ (fun i=>i.property) (hb L))
  have hret:∀ L,(incl₀ L).matrix*(proj₀ L).matrix=projectiveIdentity Q (T₀ L).placement := by
    intro L
    convert block_inclusion_projection Q (Y w s L q)
      {i | ((Y w s L q).placement i).color∈fusionColorRegion m I} using 1
    · rfl
    · apply Matrix.ext
      intro i j
      simp only [projectiveIdentity,Matrix.diagonal_apply]
      by_cases h:i=j <;> simp only [h,ite_true,ite_false]
      rfl
  exact fusionOrbit_subobject_null_separation m d hd hdiag hm w s T₀ q k
    (fun L i=>i.val.property) incl₀ proj₀
    (fun L=>by
      convert hret L using 1 <;> congr 1
      exact Subsingleton.elim _ _)
    T hT incl I J c (a w s q I) σ
    (fusionOrbitColor_weightedVector m d hd hdiag hm w s q I hb)
    hsvec hsupp hσ hc hcSupp hcPos hcNull hext hint hsoc

end HarmonicArtin

end OAI
