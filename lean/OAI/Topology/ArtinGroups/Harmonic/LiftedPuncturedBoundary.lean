import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellDeligne

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def LiftedPuncturedBoundary (c d:LiftedCell M) :=
  {a:LiftedCell M // a<c ∧ a≠d}

instance (c d:LiftedCell M) : PartialOrder (LiftedPuncturedBoundary M c d) where
  toPreorder := inferInstanceAs (Preorder {a:LiftedCell M // a<c ∧ a≠d})
  le_antisymm := fun _ _ forward backward =>
    Subtype.ext (lifted_le_antisymm M forward backward)

theorem lifted_closed_cell_finite (c:LiftedCell M) : (Set.Iic c).Finite := by
  have : Finite (coxeterParabolic M c.2.val) := c.2.property
  let f:(coxeterParabolic M c.2.val)×SphericalType M → LiftedCell M:=
    fun p=>(c.1*positiveLift M p.1.val,p.2)
  apply ((Set.toFinite (Set.univ:Set ((coxeterParabolic M c.2.val)×SphericalType M))).image f).subset
  intro a ha
  obtain ⟨_,w,hw,hr,_,he⟩:=(lifted_le_iff_face M _ _).mp ha
  refine ⟨(⟨wordCoxeter M w,wordCoxeter_mem_parabolic M c.2.val w hw⟩,a.2),Set.mem_univ _,?_⟩
  apply Prod.ext
  · change c.1*positiveLift M (wordCoxeter M w)=a.1
    rw [positiveLift_word M w hr,he]
  · rfl

theorem lifted_punctured_boundary_finite (c d:LiftedCell M) :
    {a:LiftedCell M | a<c ∧ a≠d}.Finite :=
  (lifted_closed_cell_finite M c).subset (fun _ h=>h.1.le)

end HarmonicArtin

end OAI
