import Mathlib
import OAI.Topology.ArtinGroups.Complexes.BottomSocleZero
import OAI.Topology.ArtinGroups.Complexes.ComplexPacketPreserves

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem classPacketPerm_preserves_open_socle
    (hn:∀ a,Q.source a≠Q.target a) {P:Type u} [Fintype P]
    (v:P→V) (hv:Pairwise fun a b=>OrthogonalVertices Q (v a) (v b))
    (J:Set V) (hJ:∀ a,v a∈J) (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ}
    (hx:ClassLowerBound Q d x) (hs:ClassBottomSocleZero Q d J x) :
    ClassBottomSocleZero Q d J (classPacketPerm Q hn v hv x) := by
  have hh:=classPacketPerm_preserves Q hn v hv
    (fun y=>ClassLowerBound Q d y ∧ ClassBottomSocleZero Q d J y)
    (fun a y hy=>⟨classPositiveTwist_lower_bound Q (v a) y hy.1,
      classPositiveTwist_preserves_open_socle Q hn (v a) J (hJ a) y hy.1 hy.2⟩)
    x ⟨hx,hs⟩
  exact hh.2

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
