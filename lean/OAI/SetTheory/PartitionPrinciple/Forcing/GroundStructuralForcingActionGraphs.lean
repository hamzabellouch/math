import OAI.SetTheory.PartitionPrinciple.Definability.RefinementHistoryOrderOutputFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.StructuralAssignmentActionFormulas

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralForcingCarrier
    (rows G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  M.refinementHistoryForcing rows T stages
    (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

include pairing unions powers separation collection in
theorem structuralForcingCarrier_mem (env : Fin 9 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.structuralForcingCarrier (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) ∈ M.sets :=
  M.refinementHistoryForcing_mem pairing unions powers separation (members 0) (members 5) (members 7)
    ((M.definable_structuralRefinementHistory pairing unions powers separation collection).closed
      (fun j => env j.succ) (fun j => members j.succ)) omega

noncomputable def structuralForcingCarrierFormula {n : Nat}
    (output rows G nodes nodeOrder basis T T2 stages history N : Fin n) : SetFormula n :=
  .ex (.conj
    (reindex (extend 0 ![G.succ, nodes.succ, nodeOrder.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
      (M.definable_structuralRefinementHistory pairing unions powers separation collection).formula)
    (refinementHistoryForcingOutputFormula output.succ rows.succ T.succ stages.succ 0 N.succ))

theorem realize_structuralForcingCarrierFormula {n : Nat}
    (output rows G nodes nodeOrder basis T T2 stages history N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) (naturals : env N = ZFSet.omega) :
    Realize M.sets (M.structuralForcingCarrierFormula pairing unions powers separation collection
      output rows G nodes nodeOrder basis T T2 stages history N) env ↔
      env output = M.structuralForcingCarrier (env rows) (env G) (env nodes) (env nodeOrder)
        (env basis) (env T) (env T2) (env stages) (env history) := by
  unfold structuralForcingCarrierFormula
  rw [realize_ex]
  let params : Fin 8 → ZFSet.{u} := ![env G, env nodes, env nodeOrder, env basis, env T, env T2, env stages, env history]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases (members G) (Fin.cases (members nodes)
    (Fin.cases (members nodeOrder) (Fin.cases (members basis) (Fin.cases (members T)
      (Fin.cases (members T2) (Fin.cases (members stages) (Fin.cases (members history) (fun j => Fin.elim0 j))))))))
  have args (H : ZFSet.{u}) :
      (fun j : Fin 8 => extend H env
        (![G.succ, nodes.succ, nodeOrder.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ] j)) = params := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) j
  have meaning (H : ZFSet.{u}) (hH : H ∈ M.sets) :
      Realize M.sets (.conj
        (reindex (extend 0 ![G.succ, nodes.succ, nodeOrder.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
          (M.definable_structuralRefinementHistory pairing unions powers separation collection).formula)
        (refinementHistoryForcingOutputFormula output.succ rows.succ T.succ stages.succ 0 N.succ))
        (extend H env) ↔
      H = M.structuralRefinementHistory (env G) (env nodes) (env nodeOrder) (env basis)
        (env T) (env T2) (env stages) (env history) ∧
      env output = M.refinementHistoryForcing (env rows) (env T) (env stages) H := by
    apply and_congr
    · rw [realize_reindex, map_extend, args]
      exact (M.definable_structuralRefinementHistory pairing unions powers separation collection).correct
        params ground H hH
    · exact M.realize_refinementHistoryForcingOutputFormula pairing unions powers separation
        output.succ rows.succ T.succ stages.succ 0 N.succ (extend H env) (Fin.cases hH members) naturals
  constructor
  · rintro ⟨H, hH, holds⟩
    obtain ⟨rfl, equal⟩ := (meaning H hH).1 holds
    exact equal
  · intro equal
    have packed := (M.definable_structuralRefinementHistory pairing unions powers separation collection).closed params ground
    exact ⟨_, packed, (meaning _ packed).2 ⟨rfl, equal⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def definable_structuralAssignments :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.structuralAssignments (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) := by
  let v := GroundSetTerm.var M (n := 8)
  let packed := GroundSetTerm.app (M.definable_structuralRefinementHistory pairing unions powers separation collection)
    ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7]
  let indices := GroundSetTerm.app (M.definable_refinementDataHistoryIndices pairing unions powers separation) ![v 6,packed]
  let product (x y : GroundSetTerm M 8) := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x,y]
  exact (product indices (product (v 4) (v 4))).definition

noncomputable def definable_structuralAssignmentActionGraph :
    GroundDefinableFunction M (fun env : Fin 9 → ZFSet.{u} =>
      M.structuralAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8)) := by
  let v := GroundSetTerm.var M (n := 9)
  let J := GroundSetTerm.app (M.definable_structuralAssignments pairing unions powers separation collection)
    ![v 0,v 1,v 2,v 4,v 5,v 6,v 7,v 8]
  let product (x y : GroundSetTerm M 9) := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x,y]
  let bound := product (product (v 0) J) J
  let term := GroundSetTerm.app (M.definable_separation separation
    (M.structuralAssignmentEntryFormula pairing unions powers separation collection))
    ![bound,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8]
  have equal (env : Fin 9 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
      term.eval env = M.structuralAssignmentActionGraph (env 0) (env 1) (env 2) (env 3)
        (env 4) (env 5) (env 6) (env 7) (env 8) := by
    have args : (fun j : Fin 9 => (![bound,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8] j.succ).eval env) = env := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))) j
    change ZFSet.sep (fun z => Realize M.sets
      (M.structuralAssignmentEntryFormula pairing unions powers separation collection) (extend z _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, holds⟩
      exact (M.realize_structuralAssignmentEntryFormula pairing unions powers separation collection
        (extend z env) (Fin.cases (M.transitive (bound.ground env members) hz) members)).1 holds
    · intro member
      have raw := member
      unfold structuralAssignmentActionGraph at raw
      have hz : z ∈ bound.eval env := (ZFSet.mem_sep.1 raw).1
      exact ⟨hz, (M.realize_structuralAssignmentEntryFormula pairing unions powers separation collection
        (extend z env) (Fin.cases (M.transitive (bound.ground env members) hz) members)).2 member⟩
  exact { formula := term.definition.formula
          closed := fun env members => equal env members ▸ term.ground env members
          correct := fun env members z hz => (term.correct env members z hz).trans
            (congrArg (fun x => z = x) (equal env members)).to_iff }

include pairing unions powers separation collection in
theorem structuralAssignmentActionGraph_mem {G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets) (hna : nodeAction ∈ M.sets)
    (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hs : stages ∈ M.sets) (hh : history ∈ M.sets) :
    M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ∈ M.sets :=
  (M.definable_structuralAssignmentActionGraph pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,nodeAction,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hna (Fin.cases hb (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j))))))))))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem structuralForcingActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {rows rowAction G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hRowAction : rowAction ∈ M.sets)
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    rawRowAssignmentActionGraph G
      (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history) rows
      (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history).sUnion.sUnion
      (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) rowAction
      (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) ∈ M.sets := by
  have hQ := M.structuralForcingCarrier_mem pairing unions powers separation collection
    ![rows,G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hRows (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))) omega
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hF := M.structuralAssignmentActionGraph_mem pairing unions powers separation collection
    hG hn hno hna hb hT hT2 hs hh
  exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection
    hG hQ hRows (M.union_mem unions (M.union_mem unions hQ)) hJ hRowAction hF

end PartitionPilot.Forcing.TransitiveGround

end OAI
