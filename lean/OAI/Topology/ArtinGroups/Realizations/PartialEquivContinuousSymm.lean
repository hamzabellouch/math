import Mathlib

namespace OAI

namespace HarmonicArtin
open Topology Set

lemma partialEquiv_continuousOn_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : PartialEquiv X Y) (he : IsEmbedding (e.source.domRestrict e)) :
    ContinuousOn e.symm e.target := by
  let g : e.target → e.source := fun y => ⟨e.symm y,e.map_target y.property⟩
  have hg : Continuous g := by
    apply he.continuous_iff.mpr
    have h : (e.source.domRestrict e) ∘ g=Subtype.val := by
      funext y
      exact e.right_inv y.property
    rw [h]
    exact continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hg

end HarmonicArtin

end OAI
