import Mathlib
import OAI.Topology.ArtinGroups.Functors.Index
import OAI.Topology.ArtinGroups.Realizations.NerveOrderMap

namespace OAI

namespace HarmonicArtin
universe u
open Simplicial CategoryTheory Opposite

lemma nerveOrderMap_comp {P Q R:Type u} [Preorder P] [Preorder Q] [Preorder R]
    (f:P→oQ) (g:Q→oR) : nerveOrderMap (g.comp f)=(nerveOrderMap g).comp (nerveOrderMap f) := by
  have he:nerveMap (g.comp f).toFunctor=nerveMap f.toFunctor≫nerveMap g.toFunctor:=by
    ext n x
    rfl
  change (SSet.toTop.map _).hom=_
  rw [he,CategoryTheory.Functor.map_comp]
  rfl

noncomputable def nerveOrderRetractionEquiv {P Q:Type u} [Preorder P] [Preorder Q]
    (r:P→oQ) (i:Q→oP) (hr:r.comp i=OrderHom.id) (hi:∀p,p≤ i (r p)) :
    ContinuousMap.HomotopyEquiv |nerve P| |nerve Q| where
  toFun:=nerveOrderMap r
  invFun:=nerveOrderMap i
  left_inv:=by
    rw [←nerveOrderMap_comp,←nerveOrderMap_id P]
    exact ⟨(nerveOrderComparisonHomotopy (OrderHom.id (α:=P)) (i.comp r) hi).symm⟩
  right_inv:=by
    rw [←nerveOrderMap_comp,hr,nerveOrderMap_id]

end HarmonicArtin

end OAI
