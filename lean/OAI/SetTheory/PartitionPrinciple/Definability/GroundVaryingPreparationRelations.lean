import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNicePreparationWitnessBounds
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralHistoryTestUnions

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

def StoredPreparationCode (upperOrder cutGraph meet omega C E : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (p y : ZFSet.{u}) : Prop :=
  ∃ row A r k enumerations q,
    p = ZFSet.pair row A ∧ y = ZFSet.pair r (ZFSet.pair k enumerations) ∧
    ZFSet.pair r p ∈ upperOrder ∧ ZFSet.pair r q ∈ cutGraph ∧
    PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
      meet (fields 14) (fields 13) (fields 9) omega (M.storedPreparationRequests A fields)
      C E k enumerations

private def transitionShape {n} (p y upperOrder cutGraph : Fin n) : BoundedFormula (n + 8) :=
  let old := suffixIndex n 8
  let v := prefixIndex n 8
  .conj (BoundedFormula.orderedPairFormula (old p) (v 0) (v 1))
    (.conj (BoundedFormula.orderedPairFormula (old y) (v 2) (v 5))
      (.conj (BoundedFormula.orderedPairFormula (v 5) (v 3) (v 4))
        (.conj (BoundedFormula.pairMembershipFormula (v 2) (old p) (old upperOrder))
          (BoundedFormula.pairMembershipFormula (v 2) (v 6) (old cutGraph)))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private noncomputable def transitionBody {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n) : SetFormula (n + 8) :=
  let old := suffixIndex n 8
  let v := prefixIndex n 8
  .conj (transitionShape p y upperOrder cutGraph).toFormula
    (.conj (SetFormula.reindex (extend (v 7) (extend (v 1) (fun j => old (fields j))))
      (M.definable_storedPreparationRequests pairing unions powers separation).formula)
      (preparedCertificateFamilyFormula (old (fields 7)) (old (fields 8)) (v 6)
        (old (fields 10)) (old (fields 11)) (old meet) (old (fields 14))
        (old (fields 13)) (old (fields 9)) (old omega) (v 7) (old C) (old E) (v 3) (v 4)))

noncomputable def storedPreparationFormula {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n) : SetFormula n :=
  exBlock 8 (transitionBody M pairing unions powers separation p y upperOrder cutGraph meet omega C E fields)

theorem realize_storedPreparationFormula {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (meetCode : MeetOrderCode (env (fields 10)) (env (fields 11)) (env meet)) :
    Realize M.sets (M.storedPreparationFormula pairing unions powers separation
      p y upperOrder cutGraph meet omega C E fields) env ↔
    M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
      (env C) (env E) (fun j => env (fields j)) (env p) (env y) := by
  unfold storedPreparationFormula
  rw [realize_exBlock]
  have actual (w : Fin 8 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (transitionBody M pairing unions powers separation
        p y upperOrder cutGraph meet omega C E fields) (extendMany 8 w env) ↔
      (env p = ZFSet.pair (w 0) (w 1) ∧ env y = ZFSet.pair (w 2) (w 5) ∧
        w 5 = ZFSet.pair (w 3) (w 4) ∧ ZFSet.pair (w 2) (env p) ∈ env upperOrder ∧
        ZFSet.pair (w 2) (w 6) ∈ env cutGraph) ∧
      w 7 = M.storedPreparationRequests (w 1) (fun j => env (fields j)) ∧
      PreparedCertificateFamilyCode M (env (fields 7)) (env (fields 8)) (w 6)
        (env (fields 10)) (env (fields 11)) (env meet) (env (fields 14))
        (env (fields 13)) (env (fields 9)) (env omega) (w 7) (env C) (env E) (w 3) (w 4) := by
    have allGround := extendMany_members 8 w env ground members
    dsimp only [transitionBody]
    rw [Realize, Realize, BoundedFormula.realize_toFormula M _ _ allGround]
    have request : Realize M.sets (SetFormula.reindex
        (extend (prefixIndex n 8 7) (extend (prefixIndex n 8 1)
          (fun j => suffixIndex n 8 (fields j))))
        (M.definable_storedPreparationRequests pairing unions powers separation).formula)
        (extendMany 8 w env) ↔
        w 7 = M.storedPreparationRequests (w 1) (fun j => env (fields j)) := by
      rw [realize_reindex, map_extend, map_extend]
      simp only [extendMany_prefix, extendMany_suffix]
      exact (M.definable_storedPreparationRequests pairing unions powers separation).correct
        (extend (w 1) (fun j => env (fields j)))
        (Fin.cases (ground 1) (fun j => members (fields j))) (w 7) (ground 7)
    rw [request, M.realize_preparedCertificateFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ allGround (by simpa only [extendMany_suffix] using meetCode)]
    simp only [transitionShape, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨⟨input, output, tail, below, cut⟩, requests, prepared⟩ := (actual w ground).1 body
    exact ⟨w 0, w 1, w 2, w 3, w 4, w 6, input, tail ▸ output, below, cut, requests ▸ prepared⟩
  · rintro ⟨row, A, r, k, enumerations, q, input, output, below, cut, prepared⟩
    have hp := input ▸ members p
    have hy := output ▸ members y
    have hTail := M.pair_right hy
    have hq := M.pair_right (M.transitive (members cutGraph) cut)
    let J := M.storedPreparationRequests A (fun j => env (fields j))
    have hJ := M.storedPreparationRequests_mem pairing unions powers separation (M.pair_right hp)
      (fun j => env (fields j)) (fun j => members (fields j))
    let w : Fin 8 → ZFSet.{u} := ![row, A, r, k, enumerations, ZFSet.pair k enumerations, q, J]
    have ground : ∀ j, w j ∈ M.sets := Fin.cases (M.pair_left hp)
      (Fin.cases (M.pair_right hp) (Fin.cases (M.pair_left hy)
        (Fin.cases (M.pair_left hTail) (Fin.cases (M.pair_right hTail)
          (Fin.cases hTail (Fin.cases hq (Fin.cases hJ (fun j => Fin.elim0 j))))))))
    exact ⟨w, ground, (actual w ground).2 ⟨⟨input, output, rfl, below, cut⟩, rfl, prepared⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def storedPreparationRelation
    (Q upperOrder nodes T levels alpha meet : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let cut := rowAssignmentCutGraph Q (fields 7) levels alpha
  ZFSet.sep (fun z => ∃ p y, z = ZFSet.pair p y ∧
    M.StoredPreparationCode upperOrder cut meet ZFSet.omega C E fields p y)
    (ZFSet.prod Q (M.preparationWitnessBound nodes T Q))

theorem pair_mem_storedPreparationRelation
    (Q upperOrder nodes T levels alpha meet : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u})
    (p y : ZFSet.{u}) :
    ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields ↔
    p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        meet ZFSet.omega (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  rw [storedPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, hy⟩, p', y', eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hp, hy, code⟩
  · rintro ⟨hp, hy, code⟩
    exact ⟨⟨hp, hy⟩, p, y, rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private noncomputable def preparationEntryFormula {n}
    (z upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (M.storedPreparationFormula pairing unions powers separation
      (v 0) (v 1) (old upperOrder) (old cutGraph) (old meet) (old omega) (old C) (old E)
      (fun j => old (fields j))))

private theorem realize_preparationEntryFormula {n}
    (z upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (meetCode : MeetOrderCode (env (fields 10)) (env (fields 11)) (env meet)) :
    Realize M.sets (preparationEntryFormula M pairing unions powers separation
      z upperOrder cutGraph meet omega C E fields) env ↔
      ∃ p y, env z = ZFSet.pair p y ∧
        M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
          (env C) (env E) (fun j => env (fields j)) p y := by
  unfold preparationEntryFormula
  rw [realize_exBlock]
  have actual (w : Fin 2 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 2 z)
          (prefixIndex n 2 0) (prefixIndex n 2 1)).toFormula
        (M.storedPreparationFormula pairing unions powers separation
          (prefixIndex n 2 0) (prefixIndex n 2 1) (suffixIndex n 2 upperOrder)
          (suffixIndex n 2 cutGraph) (suffixIndex n 2 meet) (suffixIndex n 2 omega)
          (suffixIndex n 2 C) (suffixIndex n 2 E) (fun j => suffixIndex n 2 (fields j))))
        (extendMany 2 w env) ↔
      env z = ZFSet.pair (w 0) (w 1) ∧
        M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
          (env C) (env E) (fun j => env (fields j)) (w 0) (w 1) := by
    have allGround := extendMany_members 2 w env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_orderedPairFormula,
      M.realize_storedPreparationFormula pairing unions powers separation
        _ _ _ _ _ _ _ _ _ _ allGround (by simpa only [extendMany_suffix] using meetCode)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, body⟩
    exact ⟨w 0, w 1, (actual w ground).1 body⟩
  · rintro ⟨p, y, equal, code⟩
    have hp := M.pair_left (equal ▸ members z)
    have hy := M.pair_right (equal ▸ members z)
    exact ⟨![p, y], Fin.cases hp (Fin.cases hy (fun j => Fin.elim0 j)),
      (actual ![p, y] (Fin.cases hp (Fin.cases hy (fun j => Fin.elim0 j)))).2 ⟨equal, code⟩⟩

include pairing unions powers separation in
theorem storedPreparationRelation_mem
    {Q upperOrder nodes T levels alpha meet : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hOrder : upperOrder ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hT : T ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hMeet : meet ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (fields : Fin 15 → ZFSet.{u}) (members : ∀ j, fields j ∈ M.sets)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet) :
    M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields ∈ M.sets := by
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let cut := rowAssignmentCutGraph Q (fields 7) levels alpha
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hE := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega
  have hCut := M.rowAssignmentCutGraph_mem pairing unions powers separation hQ (members 7) hLevels hAlpha
  let params : Fin 21 → ZFSet.{u} :=
    extend upperOrder (extend cut (extend meet (extend ZFSet.omega (extend C (extend E fields)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hOrder (Fin.cases hCut
    (Fin.cases hMeet (Fin.cases omega (Fin.cases hC (Fin.cases hE members)))))
  let slots : Fin 15 → Fin 22 := fun j => j.succ.succ.succ.succ.succ.succ.succ
  let formula := preparationEntryFormula M pairing unions powers separation 0 1 2 3 4 5 6 slots
  have bound := M.prod_mem pairing unions powers separation hQ
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have selected := M.separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets formula (extend z params))
      (ZFSet.prod Q (M.preparationWitnessBound nodes T Q)) =
      M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, storedPreparationRelation, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact realize_preparationEntryFormula M pairing unions powers separation 0 1 2 3 4 5 6 slots
      (extend z params) (Fin.cases (M.transitive bound hz) ground) meetCode
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

def VaryingPreparationCode (packed Q upperOrder nodes T levels omega C E z : ZFSet.{u}) : Prop :=
  ∃ alpha p y, ∃ fields : Fin 15 → ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair alpha p) y ∧
    ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
    fields 6 = T ∧ fields 10 = nodes ∧
    MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
    M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
      (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y

theorem varyingPreparationCode_pair_iff (packed Q upperOrder nodes T levels omega C E alpha p y : ZFSet.{u}) :
    M.VaryingPreparationCode packed Q upperOrder nodes T levels omega C E
      (ZFSet.pair (ZFSet.pair alpha p) y) ↔
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y := by
  constructor
  · rintro ⟨alpha', p', y', fields, equal, rest⟩
    obtain ⟨input, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
    exact ⟨fields, rest⟩
  · rintro ⟨fields, rest⟩
    exact ⟨alpha, p, y, fields, rfl, rest⟩

private def varyingShape {n} (z packed nodes T : Fin n) : BoundedFormula (n + 22) :=
  let old := suffixIndex n 22
  let v := prefixIndex n 22
  let f := fun j : Fin 15 => v j.succ.succ.succ.succ.succ.succ.succ
  .conj (BoundedFormula.orderedPairFormula (old z) (v 3) (v 2))
    (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 1))
      (.conj (BoundedFormula.nonemptyTupleFormula 14 (v 4) f)
        (.conj (BoundedFormula.pairMembershipFormula (v 0) (v 4) (old packed))
          (.conj (.equal (f 6) (old T)) (.equal (f 10) (old nodes))))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private noncomputable def varyingBody {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n) : SetFormula (n + 22) :=
  let old := suffixIndex n 22
  let v := prefixIndex n 22
  let f := fun j : Fin 15 => v j.succ.succ.succ.succ.succ.succ.succ
  .conj (varyingShape z packed nodes T).toFormula
    (.conj (BoundedFormula.meetOrderFormula (f 10) (f 11) (v 5)).toFormula
      (.conj (rowAssignmentCutGraphFormula (v 6) (old Q) (f 7) (old levels) (v 0))
        (M.storedPreparationFormula pairing unions powers separation
          (v 1) (v 2) (old upperOrder) (v 6) (v 5) (old omega) (old C) (old E) f)))

noncomputable def varyingPreparationFormula {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n) : SetFormula n :=
  exBlock 22 (varyingBody M pairing unions powers separation z packed Q upperOrder nodes T levels omega C E)

theorem realize_varyingPreparationFormula {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.varyingPreparationFormula pairing unions powers separation
      z packed Q upperOrder nodes T levels omega C E) env ↔
    M.VaryingPreparationCode (env packed) (env Q) (env upperOrder) (env nodes) (env T)
      (env levels) (env omega) (env C) (env E) (env z) := by
  unfold varyingPreparationFormula
  rw [realize_exBlock]
  let fs := fun w : Fin 22 → ZFSet.{u} => fun j : Fin 15 =>
    w j.succ.succ.succ.succ.succ.succ.succ
  have actual (w : Fin 22 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (varyingBody M pairing unions powers separation
        z packed Q upperOrder nodes T levels omega C E) (extendMany 22 w env) ↔
      (env z = ZFSet.pair (w 3) (w 2) ∧ w 3 = ZFSet.pair (w 0) (w 1) ∧
        w 4 = refinementFormulaDataCode (fs w) ∧ ZFSet.pair (w 0) (w 4) ∈ env packed ∧
        fs w 6 = env T ∧ fs w 10 = env nodes) ∧
      MeetOrderCode (fs w 10) (fs w 11) (w 5) ∧
      w 6 = rowAssignmentCutGraph (env Q) (fs w 7) (env levels) (w 0) ∧
      M.StoredPreparationCode (env upperOrder) (w 6) (w 5) (env omega)
        (env C) (env E) (fs w) (w 1) (w 2) := by
    have allGround := extendMany_members 22 w env ground members
    dsimp only [varyingBody]
    rw [Realize, Realize, Realize,
      BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_meetOrderFormula,
      M.realize_rowAssignmentCutGraphFormula pairing unions powers separation _ _ _ _ _ _ allGround]
    simp only [varyingShape, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_nonemptyTupleFormula, BoundedFormula.truth_pairMembershipFormula,
      extendMany_prefix, extendMany_suffix]
    apply and_congr_right
    intro _shape
    apply and_congr_right
    intro meet
    apply and_congr_right
    intro _cut
    simpa only [extendMany_prefix, extendMany_suffix] using
      (M.realize_storedPreparationFormula pairing unions powers separation
        (prefixIndex n 22 1) (prefixIndex n 22 2) (suffixIndex n 22 upperOrder)
        (prefixIndex n 22 6) (prefixIndex n 22 5) (suffixIndex n 22 omega)
        (suffixIndex n 22 C) (suffixIndex n 22 E)
        (fun j : Fin 15 => prefixIndex n 22 j.succ.succ.succ.succ.succ.succ.succ)
        (extendMany 22 w env) allGround (by simpa only [extendMany_prefix] using meet))
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨⟨outer, input, tuple, stored, terms, nodesEq⟩, meet, cut, prepared⟩ :=
      (actual w ground).1 body
    have canonical := meet.eq_canonicalMeetGraph
    refine ⟨w 0, w 1, w 2, fs w, input ▸ outer, tuple ▸ stored, terms, nodesEq,
      canonical ▸ meet, ?_⟩
    rw [canonical, cut] at prepared
    exact prepared
  · rintro ⟨alpha, p, y, fields, outer, stored, terms, nodesEq, meet, prepared⟩
    have hInput := M.pair_left (outer ▸ members z)
    have hAlpha := M.pair_left hInput
    have hp := M.pair_right hInput
    have hy := M.pair_right (outer ▸ members z)
    have hRecord := M.pair_right (M.transitive (members packed) stored)
    have hFields := M.refinementFormulaDataCode_fields_mem fields hRecord
    let mu := canonicalMeetGraph (fields 10) (fields 11)
    let cut := rowAssignmentCutGraph (env Q) (fields 7) (env levels) alpha
    have hMu := M.canonicalMeetGraph_mem pairing unions powers separation (hFields 10) (hFields 11)
    have hCut := M.rowAssignmentCutGraph_mem pairing unions powers separation
      (members Q) (hFields 7) (members levels) hAlpha
    let w : Fin 22 → ZFSet.{u} := extend alpha (extend p (extend y
      (extend (ZFSet.pair alpha p) (extend (refinementFormulaDataCode fields)
        (extend mu (extend cut fields))))))
    have ground : ∀ j, w j ∈ M.sets := Fin.cases hAlpha (Fin.cases hp (Fin.cases hy
      (Fin.cases hInput (Fin.cases hRecord (Fin.cases hMu (Fin.cases hCut hFields))))))
    exact ⟨w, ground, (actual w ground).2
      ⟨⟨outer, rfl, rfl, stored, terms, nodesEq⟩, meet, rfl, prepared⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def varyingPreparationRelation
    (stages packed Q upperOrder nodes T : ZFSet.{u}) : ZFSet.{u} :=
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let levels := refinementDataHistoryLevels stages packed T
  ZFSet.sep (M.VaryingPreparationCode packed Q upperOrder nodes T levels ZFSet.omega C E)
    (ZFSet.prod (ZFSet.prod stages Q) (M.preparationWitnessBound nodes T Q))

theorem pair_mem_varyingPreparationRelation
    (stages packed Q upperOrder nodes T alpha p y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
    alpha ∈ stages ∧ p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      ∃ fields : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
        fields 6 = T ∧ fields 10 = nodes ∧
        MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
        M.StoredPreparationCode upperOrder
          (rowAssignmentCutGraph Q (fields 7) (refinementDataHistoryLevels stages packed T) alpha)
          (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega
          (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
          (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  simp only [varyingPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    M.varyingPreparationCode_pair_iff, and_assoc]

include M in
 theorem varyingPreparationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages packed Q upperOrder nodes T : ZFSet.{u}}
    (hStages : stages ∈ M.sets) (hPacked : packed ∈ M.sets)
    (hQ : Q ∈ M.sets) (hOrder : upperOrder ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.varyingPreparationRelation stages packed Q upperOrder nodes T ∈ M.sets := by
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let levels := refinementDataHistoryLevels stages packed T
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hE := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hPacked hT
  let params : Fin 9 → ZFSet.{u} := ![packed, Q, upperOrder, nodes, T, levels, ZFSet.omega, C, E]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hPacked (Fin.cases hQ
    (Fin.cases hOrder (Fin.cases hNodes (Fin.cases hT (Fin.cases hLevels
      (Fin.cases omega (Fin.cases hC (Fin.cases hE (fun j => Fin.elim0 j)))))))))
  let formula : SetFormula 10 :=
    M.varyingPreparationFormula pairing unions powers separation 0 1 2 3 4 5 6 7 8 9
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hStages hQ)
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have selected := M.separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets formula (extend z params))
      (ZFSet.prod (ZFSet.prod stages Q) (M.preparationWitnessBound nodes T Q)) =
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, varyingPreparationRelation, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_varyingPreparationFormula pairing unions powers separation
      0 1 2 3 4 5 6 7 8 9 (extend z params) (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
