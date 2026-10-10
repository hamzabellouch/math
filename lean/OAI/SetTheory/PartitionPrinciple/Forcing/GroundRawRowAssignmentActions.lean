import OAI.SetTheory.PartitionPrinciple.Definability.GroundDefinableRelationProducts

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rowAssignmentActionGraph :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      rowAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) := by
  let v := GroundSetTerm.var M (n := 7)
  let product (x y : GroundSetTerm M 7) :=
    GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x, y]
  let rowRange := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 5]
  let assignmentRange := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 6]
  let bound := product (product (v 0) (v 1)) (v 1)
  let formula : SetFormula 10 := (BoundedFormula.rowAssignmentActionEntryFormula 0 1 2 3 4 5 6 7 8 9).toFormula
  let term := GroundSetTerm.app (M.definable_separation separation formula)
    ![bound, v 0, v 1, v 2, v 3, v 4, rowRange, assignmentRange, v 5, v 6]
  refine { formula := term.definition.formula
           closed := fun env members => M.rowAssignmentActionGraph_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 9 =>
      (![bound, v 0, v 1, v 2, v 3, v 4, rowRange, assignmentRange, v 5, v 6] j.succ).eval env) =
      ![env 0, env 1, env 2, env 3, env 4, ⋃₀ ⋃₀ env 5, ⋃₀ ⋃₀ env 6, env 5, env 6] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))) j
  have equal : term.eval env = rowAssignmentActionGraph
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, rowAssignmentActionGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hw
    rw [BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive (bound.ground env members) hw)
        (Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2)
          (Fin.cases (members 3) (Fin.cases (members 4)
            (Fin.cases (M.union_mem unions (M.union_mem unions (members 5)))
              (Fin.cases (M.union_mem unions (M.union_mem unions (members 6)))
                (Fin.cases (members 5) (Fin.cases (members 6) (fun k => Fin.elim0 k))))))))))),
      BoundedFormula.truth_rowAssignmentActionEntryFormula]
    rfl
  rw [equal]

noncomputable def rowAssignmentActionOutputFormula {n : Nat}
    (output G Q C B J rowMaps assignmentMaps : Fin n) : SetFormula n :=
  SetFormula.reindex (extend output ![G, Q, C, B, J, rowMaps, assignmentMaps])
    (M.definable_rowAssignmentActionGraph pairing unions powers separation).formula

theorem realize_rowAssignmentActionOutputFormula {n : Nat}
    (output G Q C B J rowMaps assignmentMaps : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.rowAssignmentActionOutputFormula pairing unions powers separation
      output G Q C B J rowMaps assignmentMaps) env ↔
      env output = rowAssignmentActionGraph (env G) (env Q) (env C) (env B) (env J)
        (env rowMaps) (env assignmentMaps) := by
  unfold rowAssignmentActionOutputFormula
  rw [realize_reindex, map_extend]
  exact (M.definable_rowAssignmentActionGraph pairing unions powers separation).correct
    (fun j => env (![G, Q, C, B, J, rowMaps, assignmentMaps] j))
    (fun j => members _) (env output) (members output)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def rawActionSection (g A P : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.actionSectionEntryFormula 0 1 2 3)
    (extend z (extend g (extend A (extend P Fin.elim0))))) (ZFSet.prod P P)

theorem mem_rawActionSection (g A P z : ZFSet.{u}) :
    z ∈ rawActionSection g A P ↔
      BoundedFormula.Truth (BoundedFormula.actionSectionEntryFormula 0 1 2 3)
        (extend z (extend g (extend A (extend P Fin.elim0)))) := by
  rw [rawActionSection, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro meaning
    obtain ⟨x, hx, y, hy, equal, _⟩ :=
      (BoundedFormula.truth_actionSectionEntryFormula 0 1 2 3 _).1 meaning
    exact ⟨ZFSet.mem_prod.2 ⟨x, hx, y, hy, equal⟩, meaning⟩

noncomputable def rawActionMapFamily (G A P : ZFSet.{u}) : ZFSet.{u} :=
  letI := ZFSet.small_coe G
  familyCodeGraph (fun g : G.toSet => g.val) (fun g => rawActionSection g.val A P)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawActionSection :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => rawActionSection (env 0) (env 1) (env 2)) where
  formula := exactSetFormula 0 (BoundedFormula.actionSectionEntryFormula 0 2 3 4).toFormula
  closed := by
    intro env members
    exact M.bounded_separation_mem separation (BoundedFormula.actionSectionEntryFormula 0 1 2 3)
      (extend (env 0) (extend (env 1) (extend (env 2) Fin.elim0)))
      (Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2) (fun j => Fin.elim0 j))))
      (M.prod_mem pairing unions powers separation (members 2) (members 2))
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact M.transitive (M.prod_mem pairing unions powers separation (members 2) (members 2))
        (ZFSet.mem_sep.1 hw).1
    · intro w hw
      rw [mem_rawActionSection,
        BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))]
      rw [BoundedFormula.truth_actionSectionEntryFormula,
        BoundedFormula.truth_actionSectionEntryFormula]
      rfl

noncomputable def definable_rawActionMapFamily (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => rawActionMapFamily (env 0) (env 1) (env 2)) :=
  (M.definable_rawActionSection pairing unions powers separation).definable_graph pairing separation collection

end TransitiveGround

variable {H Q : Type u} [Group H] [PartialOrder Q]
variable (a : PosetAction H Q) (s : Presentation Q) (t : Presentation H)

theorem rawActionSection_eq (g : H) :
    rawActionSection (t.encode g) (a.actionGraph s t) s.carrier = s.graph s (a.iso g) := by
  apply ZFSet.ext
  intro z
  rw [mem_rawActionSection]
  exact BoundedFormula.actionSectionEntry_correct a s t g z

theorem rawActionMapFamily_eq :
    rawActionMapFamily t.carrier (a.actionGraph s t) s.carrier = a.conditionMapFamily s t := by
  let := ZFSet.small_coe t.carrier
  apply ZFSet.ext
  intro z
  rw [rawActionMapFamily, mem_familyCodeGraph, PosetAction.conditionMapFamily, ZFSet.mem_range]
  constructor
  · rintro ⟨g, equal⟩
    obtain ⟨h, eq⟩ := (t.mem_carrier g.val).1 g.property
    refine ⟨h, ?_⟩
    rw [← eq, rawActionSection_eq] at equal
    exact equal
  · rintro ⟨g, equal⟩
    refine ⟨⟨t.encode g, t.encode_mem g⟩, ?_⟩
    change ZFSet.pair (t.encode g) (rawActionSection _ _ _) = z
    rw [rawActionSection_eq]
    exact equal

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_rawActionMapFamily (G action P g f : ZFSet.{u}) :
    ZFSet.pair g f ∈ rawActionMapFamily G action P ↔
      g ∈ G ∧ f = rawActionSection g action P := by
  let := ZFSet.small_coe G
  rw [rawActionMapFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 equal
    exact ⟨keys ▸ i.property, by rw [← keys]; exact values.symm⟩
  · rintro ⟨member, rfl⟩
    exact ⟨⟨g, member⟩, rfl⟩

theorem pair_mem_rawActionSection (g action P x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ rawActionSection g action P ↔
      x ∈ P ∧ y ∈ P ∧ ZFSet.pair (ZFSet.pair g x) y ∈ action := by
  rw [mem_rawActionSection, BoundedFormula.truth_actionSectionEntryFormula]
  constructor
  · rintro ⟨a, ha, b, hb, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, entry⟩
  · rintro ⟨hx, hy, entry⟩
    exact ⟨x, hx, y, hy, rfl, entry⟩

noncomputable def rawRowAssignmentActionGraph
    (G Q C B J rowAction assignmentAction : ZFSet.{u}) : ZFSet.{u} :=
  rowAssignmentActionGraph G Q C B J (rawActionMapFamily G rowAction C)
    (rawActionMapFamily G assignmentAction J)

theorem pair_mem_rawRowAssignmentActionGraph
    (G Q C B J rowAction assignmentAction g p A q D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair p A)) (ZFSet.pair q D) ∈
      rawRowAssignmentActionGraph G Q C B J rowAction assignmentAction ↔
      g ∈ G ∧ ZFSet.pair p A ∈ Q ∧ ZFSet.pair q D ∈ Q ∧
        p ∈ C ∧ A ∈ B ∧ q ∈ C ∧ D ∈ B ∧
          ZFSet.pair (ZFSet.pair g p) q ∈ rowAction ∧
            D = relationImage A J (rawActionSection g assignmentAction J) := by
  rw [rawRowAssignmentActionGraph, pair_mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨hg, hpA, hqD, hp, hA, hq, hD, rf, af, indexed, row, indexedA, image⟩
    have rowEq := (pair_mem_rawActionMapFamily G rowAction C g rf).1 indexed |>.2
    have assignmentEq := (pair_mem_rawActionMapFamily G assignmentAction J g af).1 indexedA |>.2
    rw [rowEq] at row
    rw [assignmentEq] at image
    exact ⟨hg, hpA, hqD, hp, hA, hq, hD,
      ((pair_mem_rawActionSection g rowAction C p q).1 row).2.2, image⟩
  · rintro ⟨hg, hpA, hqD, hp, hA, hq, hD, row, image⟩
    exact ⟨hg, hpA, hqD, hp, hA, hq, hD, rawActionSection g rowAction C,
      rawActionSection g assignmentAction J,
      (pair_mem_rawActionMapFamily G rowAction C g _).2 ⟨hg, rfl⟩,
      (pair_mem_rawActionSection g rowAction C p q).2 ⟨hp, hq, row⟩,
      (pair_mem_rawActionMapFamily G assignmentAction J g _).2 ⟨hg, rfl⟩, image⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def definable_rawRowAssignmentActionGraph :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      rawRowAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) := by
  let v := GroundSetTerm.var M (n := 7)
  let maps := M.definable_rawActionMapFamily pairing unions powers separation collection
  let rowMaps := GroundSetTerm.app maps ![v 0, v 5, v 2]
  let assignmentMaps := GroundSetTerm.app maps ![v 0, v 6, v 4]
  exact (GroundSetTerm.app (M.definable_rowAssignmentActionGraph pairing unions powers separation)
    ![v 0, v 1, v 2, v 3, v 4, rowMaps, assignmentMaps]).definition

include pairing unions powers separation collection in
theorem rawRowAssignmentActionGraph_mem {G Q C B J rowAction assignmentAction : ZFSet.{u}}
    (hG : G ∈ M.sets) (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets)
    (hJ : J ∈ M.sets) (hRow : rowAction ∈ M.sets) (hAssignment : assignmentAction ∈ M.sets) :
    rawRowAssignmentActionGraph G Q C B J rowAction assignmentAction ∈ M.sets :=
  (M.definable_rawRowAssignmentActionGraph pairing unions powers separation collection).closed
    ![G, Q, C, B, J, rowAction, assignmentAction]
    (Fin.cases hG (Fin.cases hQ (Fin.cases hC (Fin.cases hB
      (Fin.cases hJ (Fin.cases hRow (Fin.cases hAssignment (fun j => Fin.elim0 j))))))))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
