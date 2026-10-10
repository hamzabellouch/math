import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveWord

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

theorem source_family_socle_finite_termination {R:Type*}
    (J:Set S) (hJ:IsSpherical M J) (q:ℤ)
    (x:R→FiniteHomotopyClass Q (K:=K)) (hx:∀ r,ClassLowerBound Q q (x r))
    (P:List J→Prop) (hP:P [])
    (step:∀ w,(restrictedMatrix M J).toCoxeterSystem.IsReduced w→P w→
      ∀ j:J,(∃ r L c,0<classLayerSocleDimension Q q (.inl j,L) c
        (sourceBottomWord M J q w (x r)))→P (j::w)) :
    ∃ w:List J,(restrictedMatrix M J).toCoxeterSystem.IsReduced w ∧ P w ∧
      ∀ r (j:J) L c,classLayerSocleDimension Q q (.inl j,L) c
        (sourceBottomWord M J q w (x r))=0 := by
  have : Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  let:=Fintype.ofFinite (restrictedMatrix M J).Group
  let cs:=(restrictedMatrix M J).toCoxeterSystem
  let B:=Finset.univ.sup cs.length
  let move:List J→J→Prop:=fun w j=>∃ r L c,
    0<classLayerSocleDimension Q q (.inl j,L) c (sourceBottomWord M J q w (x r))
  have bound (w:List J) (hw:cs.IsReduced w) : w.length≤B := by
    rw [← hw.eq]
    exact Finset.le_sup (f:=cs.length) (Finset.mem_univ _)
  have extend (w:List J) (hw:cs.IsReduced w) (j:J) (hj:move w j) : cs.IsReduced (j::w) := by
    obtain ⟨r,L,c,h⟩:=hj
    exact sourceBottomWord_socle_ascent M J q (x r) (hx r) w hw j ⟨L,c,h⟩
  obtain ⟨w,hw,hp,hz⟩:=bounded_word_saturation B cs.IsReduced P move
    (by simp [cs,CoxeterSystem.IsReduced]) hP bound extend step
  refine ⟨w,hw,hp,?_⟩
  intro r j L c
  apply Nat.eq_zero_of_not_pos
  intro hc
  exact hz j ⟨r,L,c,hc⟩

end HarmonicArtin

end OAI
