import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionUnionBaseFilling

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def mapFamilyApplicationSetFormula {n} (output I P Q bound family : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.mapFamilyApplicationEntryFormula 0 I.succ P.succ Q.succ bound.succ family.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_mapFamilyApplicationSetFormula {n}
    (output I P Q bound family : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets)
    (bound_eq : env bound = ZFSet.sUnion (ZFSet.sUnion (env family))) :
    Realize M.sets (mapFamilyApplicationSetFormula output I P Q bound family) env ↔
      env output = mapFamilyApplicationGraph (env I) (env P) (env Q) (env family) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.mapFamilyApplicationGraph_mem pairing unions powers separation
      (members I) (members P) (members Q) (members family))
  intro z
  rw [BoundedFormula.truth_mapFamilyApplicationEntryFormula]
  change (∃ i ∈ env I, ∃ x ∈ env P, ∃ y ∈ env Q, ∃ f ∈ env bound,
    z = ZFSet.pair (ZFSet.pair i x) y ∧ ZFSet.pair i f ∈ env family ∧ ZFSet.pair x y ∈ f) ↔ _
  rw [bound_eq, mapFamilyApplicationGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨i, hi, x, hx, y, hy, _, _, rfl, _, _⟩ := witness
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩
  · exact And.right

noncomputable def definable_mapFamilyApplication : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => mapFamilyApplicationGraph (env 0) (env 1) (env 2) (env 3)) := by
  let aux := (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => (3 : Fin 4))
  refine aux.withAux (mapFamilyApplicationSetFormula 1 2 3 4 0 5) ?_ ?_
  · intro env members
    exact M.mapFamilyApplicationGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3)
  · intro env members z hz
    exact M.realize_mapFamilyApplicationSetFormula pairing unions powers separation
      1 2 3 4 0 5 _ (Fin.cases (aux.closed env members) (Fin.cases hz members)) rfl

noncomputable def definable_completedMapFamily : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => M.indexedRelationSections (env 0) (env 1) (env 1)
      (mapFamilyApplicationGraph (env 0) (env 1) (env 1) (env 2))) := by
  let v : Fin 3 → GroundSetTerm M 3 := GroundSetTerm.var M
  let flat := GroundSetTerm.app (M.definable_mapFamilyApplication pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 1) (Fin.cases (v 2) Fin.elim0))))
  let sections := GroundSetTerm.app (M.definable_indexedSections pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 1) (Fin.cases flat Fin.elim0))))
  exact sections.definition.congr (fun _ => rfl)

noncomputable def completedMapFamilyFormula {n} (output I U family : Fin n) : SetFormula n :=
  SetFormula.reindex (Fin.cases output (Fin.cases I (Fin.cases U (Fin.cases family Fin.elim0))))
    (M.definable_completedMapFamily pairing unions powers separation).formula

theorem realize_completedMapFamilyFormula {n} (output I U family : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.completedMapFamilyFormula pairing unions powers separation output I U family) env ↔
      env output = M.indexedRelationSections (env I) (env U) (env U)
        (mapFamilyApplicationGraph (env I) (env U) (env U) (env family)) := by
  let slots : Fin 3 → Fin n := Fin.cases I (Fin.cases U (Fin.cases family Fin.elim0))
  unfold completedMapFamilyFormula
  rw [realize_reindex]
  change Realize M.sets (M.definable_completedMapFamily pairing unions powers separation).formula
    (fun j => env (extend output slots j)) ↔ _
  rw [map_extend]
  exact (M.definable_completedMapFamily pairing unions powers separation).correct
    (fun j => env (slots j)) (fun j => members (slots j)) (env output) (members output)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
