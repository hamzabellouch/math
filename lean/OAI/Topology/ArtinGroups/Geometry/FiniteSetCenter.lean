import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ChamberPointUnique

namespace OAI

namespace HarmonicArtin.Geometric
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def finiteSetCenter {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Set E) (hV : V.Finite) : E :=
  letI := hV.fintype
  (Fintype.card V : ℝ)⁻¹ • ∑ v : V,v.val

theorem finiteSetCenter_product {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (V : Set E) (W : Set F)
    (hV : V.Finite) (hW : W.Finite) (hneV : V.Nonempty) (hneW : W.Nonempty) :
    finiteSetCenter (V ×ˢ W) (hV.prod hW)=(finiteSetCenter V hV,finiteSetCenter W hW) := by
  let := hV.fintype
  let := hW.fintype
  let := (hV.prod hW).fintype
  let : Nonempty V := hneV.to_subtype
  let : Nonempty W := hneW.to_subtype
  let e := Equiv.Set.prod V W
  have hs := Fintype.sum_equiv e (fun v => v.val)
    (fun p : V × W => (p.1.val,p.2.val)) (fun v => rfl)
  unfold finiteSetCenter
  rw [Fintype.card_congr e,hs]
  exact finite_average_product (fun v : V => v.val) (fun w : W => w.val)

variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S) [Finite M.Group]

lemma faceCenter_eq_geometric_average (c : CoxeterCellFace M) :
    faceCenter M c=finiteSetCenter (orbitPoint M '' c.vertexSet)
      ((Set.toFinite c.vertexSet).image (orbitPoint M)) := by
  let h := (Set.toFinite c.vertexSet).image (orbitPoint M)
  let := h.fintype
  let e := Equiv.Set.image (orbitPoint M) c.vertexSet (orbitPoint_inj M)
  have hs := Fintype.sum_equiv e (fun w : c.vertexSet => orbitPoint M w)
    (fun v : orbitPoint M '' c.vertexSet => v.val) (fun w => rfl)
  unfold faceCenter finiteSetCenter
  rw [Fintype.card_congr e,hs]

end HarmonicArtin.Geometric

end OAI
