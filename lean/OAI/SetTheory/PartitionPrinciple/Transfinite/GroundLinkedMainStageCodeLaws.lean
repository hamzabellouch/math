import OAI.SetTheory.PartitionPrinciple.Definability.SerializedChronologyFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.CodedMainPrefixSystems

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

noncomputable def serializedChronologyCode (T V : ZFSet.{u}) (graphs : Fin 5 → ZFSet.{u})
    (W layers : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases (nonemptyTupleCode 6 (Fin.cases T (Fin.cases V graphs)))
    (Fin.cases W (fun _ => layers)))

theorem GroundSerializedChronology.code_eq_literal {M : TransitiveGround.{u}}
    {T C D rD : ZFSet.{u}} (serial : GroundSerializedChronology M T C D rD) :
    serial.code = serializedChronologyCode T serial.fields.bound serial.fields.graph
      serial.layerBound serial.layers := rfl

theorem SerializedChronologyCode.toGround_code {M : TransitiveGround.{u}}
    {T V C D rD N W layers : ZFSet.{u}} {graphs : Fin 5 → ZFSet.{u}}
    (code : SerializedChronologyCode T V C D rD N graphs W layers)
    (hT : T ∈ M.sets) (hV : V ∈ M.sets) (hGraphs : ∀ j, graphs j ∈ M.sets)
    (hW : W ∈ M.sets) (hLayers : layers ∈ M.sets) (omega : N = ZFSet.omega) :
    (code.toGround hT hV hGraphs hW hLayers omega).code =
      serializedChronologyCode T V graphs W layers := rfl

namespace BoundedFormula
def serializedChronologyTupleFormula {n} (z history T V : Fin n) (graphs : Fin 5 → Fin n)
    (W layers : Fin n) : BoundedFormula n :=
  .conj (nonemptyTupleFormula 6 history (Fin.cases T (Fin.cases V graphs)))
    (nonemptyTupleFormula 2 z (Fin.cases history (Fin.cases W (fun _ => layers))))

theorem truth_serializedChronologyTupleFormula {n} (z history T V : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (serializedChronologyTupleFormula z history T V graphs W layers) env ↔
      env history = nonemptyTupleCode 6 (Fin.cases (env T) (Fin.cases (env V) (fun j => env (graphs j)))) ∧
        env z = serializedChronologyCode (env T) (env V) (fun j => env (graphs j)) (env W) (env layers) := by
  simp only [serializedChronologyTupleFormula, Truth, truth_nonemptyTupleFormula]
  have map2 {k : Nat} (a : Fin n) (f : Fin k → Fin n) :
      (fun j => env (Fin.cases a f j)) = Fin.cases (env a) (fun j => env (f j)) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [map2]
  constructor
  · rintro ⟨history, code⟩
    rw [history] at code
    exact ⟨history, code⟩
  · rintro ⟨history, code⟩
    unfold serializedChronologyCode at code
    rw [← history] at code
    exact ⟨history, code⟩

end BoundedFormula

end

section
open SetFormula
universe u v

def chronologyCandidateGraphs {A : Type v} (fields : Fin 10 → A) : Fin 5 → A :=
  Fin.cases (fields 2) (Fin.cases (fields 3) (Fin.cases (fields 4)
    (Fin.cases (fields 5) (fun _ => fields 6))))

namespace SetFormula
def serializedChronologyCandidateFormula {n} (z C D rD N : Fin n) : SetFormula n :=
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  let graphs := chronologyCandidateGraphs field
  exBlock 10 (.conj
    (BoundedFormula.serializedChronologyTupleFormula (old z) (field 9) (field 0) (field 1)
      graphs (field 7) (field 8)).toFormula
    (serializedChronologyFormula (field 0) (field 1) (old C) (old D) (old rD) (old N)
      graphs (field 7) (field 8)))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_serializedChronologyCandidateFormula_raw {n} (z C D rD N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (serializedChronologyCandidateFormula z C D rD N) env ↔
      ∃ fields : Fin 10 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        fields 9 = nonemptyTupleCode 6 (Fin.cases (fields 0) (Fin.cases (fields 1)
          (chronologyCandidateGraphs fields))) ∧
        env z = serializedChronologyCode (fields 0) (fields 1)
          (chronologyCandidateGraphs fields) (fields 7) (fields 8) ∧
        SerializedChronologyCode (fields 0) (fields 1) (env C) (env D) (env rD) (env N)
          (chronologyCandidateGraphs fields) (fields 7) (fields 8) := by
  rw [serializedChronologyCandidateFormula, realize_exBlock]
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  let graphs := chronologyCandidateGraphs field
  have actual (values : Fin 10 → ZFSet.{u}) (ground : ∀ j, values j ∈ M.sets) :
      (Realize M.sets
        (BoundedFormula.serializedChronologyTupleFormula (old z) (field 9) (field 0) (field 1)
          graphs (field 7) (field 8)).toFormula (extendMany 10 values env) ∧
       Realize M.sets
        (serializedChronologyFormula (field 0) (field 1) (old C) (old D) (old rD) (old N)
          graphs (field 7) (field 8)) (extendMany 10 values env)) ↔
      values 9 = nonemptyTupleCode 6 (Fin.cases (values 0) (Fin.cases (values 1)
        (chronologyCandidateGraphs values))) ∧
      env z = serializedChronologyCode (values 0) (values 1)
        (chronologyCandidateGraphs values) (values 7) (values 8) ∧
      SerializedChronologyCode (values 0) (values 1) (env C) (env D) (env rD) (env N)
        (chronologyCandidateGraphs values) (values 7) (values 8) := by
    have mems := extendMany_members 10 values env ground members
    have tuple := (BoundedFormula.realize_toFormula M _ _ mems).trans
      (BoundedFormula.truth_serializedChronologyTupleFormula (old z) (field 9) (field 0)
        (field 1) graphs (field 7) (field 8) (extendMany 10 values env))
    have code := M.realize_serializedChronologyFormula pairing unions powers separation
      (field 0) (field 1) (old C) (old D) (old rD) (old N) graphs (field 7) (field 8)
      (extendMany 10 values env) mems
    have graphMap : (fun j => extendMany 10 values env (graphs j)) = chronologyCandidateGraphs values := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
    rw [tuple, code, graphMap]
    simp only [field, old, extendMany_prefix, extendMany_suffix, and_assoc]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).2 recognized⟩

theorem realize_serializedChronologyCandidateFormula {n} (z C D rD N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (serializedChronologyCandidateFormula z C D rD N) env ↔
      ∃ T, ∃ serial : GroundSerializedChronology M T (env C) (env D) (env rD), serial.code = env z := by
  rw [M.realize_serializedChronologyCandidateFormula_raw pairing unions powers separation z C D rD N env members]
  constructor
  · rintro ⟨fields, ground, _, equal, code⟩
    have hGraphs : ∀ j, chronologyCandidateGraphs fields j ∈ M.sets :=
      Fin.cases (ground 2) (Fin.cases (ground 3) (Fin.cases (ground 4)
        (Fin.cases (ground 5) (fun _ => ground 6))))
    exact ⟨fields 0, code.toGround (ground 0) (ground 1) hGraphs (ground 7) (ground 8) omega,
      (code.toGround_code (ground 0) (ground 1) hGraphs (ground 7) (ground 8) omega).trans equal.symm⟩
  · rintro ⟨T, serial, equal⟩
    let fields : Fin 10 → ZFSet.{u} := Fin.cases T (Fin.cases serial.fields.bound
      (Fin.cases (serial.fields.graph 0) (Fin.cases (serial.fields.graph 1)
        (Fin.cases (serial.fields.graph 2) (Fin.cases (serial.fields.graph 3)
          (Fin.cases (serial.fields.graph 4) (Fin.cases serial.layerBound
            (Fin.cases serial.layers (fun _ => serial.fields.code)))))))))
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases serial.fields.time_ground
      (Fin.cases serial.fields.bound_ground (Fin.cases (serial.fields.graph_ground 0)
        (Fin.cases (serial.fields.graph_ground 1) (Fin.cases (serial.fields.graph_ground 2)
          (Fin.cases (serial.fields.graph_ground 3) (Fin.cases (serial.fields.graph_ground 4)
            (Fin.cases serial.layer_bound_ground (Fin.cases serial.layers_ground
              (fun _ => serial.fields.code_ground pairing)))))))))
    have graphEq : chronologyCandidateGraphs fields = serial.fields.graph := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun i => Fin.elim0 i))))) j
    refine ⟨fields, ground, ?_, ?_, ?_⟩
    · rw [graphEq]
      rfl
    · rw [graphEq]
      exact equal.symm.trans serial.code_eq_literal
    · rw [graphEq, omega]
      exact serial.raw_code

noncomputable def serializedChronologyCandidates (B C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ T, ∃ serial : GroundSerializedChronology M T C D rD, serial.code = z) B

omit pairing unions powers separation in
theorem mem_serializedChronologyCandidates (B C D rD z : ZFSet.{u}) :
    z ∈ M.serializedChronologyCandidates B C D rD ↔
      z ∈ B ∧ ∃ T, ∃ serial : GroundSerializedChronology M T C D rD, serial.code = z := ZFSet.mem_sep

theorem serializedChronologyCandidates_mem
    (infinite : Realize M.sets infinity Fin.elim0) {B C D rD : ZFSet.{u}}
    (hB : B ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    M.serializedChronologyCandidates B C D rD ∈ M.sets := by
  let params := extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))
  have ground : ∀ i, params i ∈ M.sets := Fin.cases hC (Fin.cases hD (Fin.cases hrD
    (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))
  have selected := M.separation_mem separation (serializedChronologyCandidateFormula 0 1 2 3 4)
    params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (serializedChronologyCandidateFormula 0 1 2 3 4)
      (extend z params)) B = M.serializedChronologyCandidates B C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_serializedChronologyCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_serializedChronologyCandidateFormula pairing unions powers separation
      0 1 2 3 4 (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl
  exact equal ▸ selected

omit pairing unions powers separation in
theorem serializedChronology_code_mem_candidates {B T C D rD : ZFSet.{u}}
    (serial : GroundSerializedChronology M T C D rD) (bound : serial.code ∈ B) :
    serial.code ∈ M.serializedChronologyCandidates B C D rD :=
  (M.mem_serializedChronologyCandidates B C D rD serial.code).2 ⟨bound, T, serial, rfl⟩

end TransitiveGround

def linkedChronologyGraphs {A : Type v} (f : Fin 24 → A) : Fin 5 → A :=
  Fin.cases (f 14) (Fin.cases (f 15) (Fin.cases (f 16) (Fin.cases (f 17) (fun _ => f 18))))

def LinkedMainStageRawCode (M : TransitiveGround.{u}) (K Labels C D rD N z : ZFSet.{u})
    (f : Fin 24 → ZFSet.{u}) : Prop :=
  z = linkedMainStageCode (f 22) (f 11) (f 23) ∧
  f 22 = mainStageCode (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) ∧
  MainStageValidity M (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) C D rD ∧
  f 21 = nonemptyTupleCode 6 (Fin.cases (f 12) (Fin.cases (f 13) (linkedChronologyGraphs f))) ∧
  f 23 = serializedChronologyCode (f 12) (f 13) (linkedChronologyGraphs f) (f 19) (f 20) ∧
  SerializedChronologyCode (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20) ∧
  ordinalSetProperty (f 11) ∧ f 12 = insert (f 11) (f 11) ∧
  ZFSet.pair (f 11) (f 0) ∈ f 14 ∧ ZFSet.pair (f 11) (f 1) ∈ f 15 ∧
  ZFSet.pair (f 11) (f 2) ∈ f 16 ∧ ZFSet.pair (f 11) (f 10) ∈ f 18 ∧
  LinkedMainInvariantCode M K Labels C D (f 0) (f 3) (f 11) (f 23)

namespace BoundedFormula

def linkedMainStageTupleFormula {n} (z a t h : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 2 z (Fin.cases a (Fin.cases t (fun _ => h)))

theorem truth_linkedMainStageTupleFormula {n} (z a t h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (linkedMainStageTupleFormula z a t h) env ↔
      env z = linkedMainStageCode (env a) (env t) (env h) := by
  rw [linkedMainStageTupleFormula, truth_nonemptyTupleFormula]
  have map : (fun j : Fin 3 => env (Fin.cases a (Fin.cases t (fun _ => h)) j)) =
      Fin.cases (env a) (Fin.cases (env t) (fun _ => env h)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) j
  rw [map]
  rfl

def linkedTerminalFormula {n} (t T P r μ h : Fin n) (graphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (ordinalFormula t) (.conj (successorFormula T t)
    (.conj (pairMembershipFormula t P (graphs 0)) (.conj (pairMembershipFormula t r (graphs 1))
      (.conj (pairMembershipFormula t μ (graphs 2)) (pairMembershipFormula t h (graphs 4))))))

theorem truth_linkedTerminalFormula {n} (t T P r μ h : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (linkedTerminalFormula t T P r μ h graphs) env ↔
      ordinalSetProperty (env t) ∧ env T = insert (env t) (env t) ∧
      ZFSet.pair (env t) (env P) ∈ env (graphs 0) ∧
      ZFSet.pair (env t) (env r) ∈ env (graphs 1) ∧
      ZFSet.pair (env t) (env μ) ∈ env (graphs 2) ∧
      ZFSet.pair (env t) (env h) ∈ env (graphs 4) := by
  simp only [linkedTerminalFormula, Truth, truth_ordinalFormula, truth_successorFormula,
    truth_pairMembershipFormula, ← ordinalSetProperty_iff]
end BoundedFormula

namespace SetFormula

def linkedMainStageRawFormula {n} (K Labels C D rD N z : Fin n) (f : Fin 24 → Fin n) : SetFormula n :=
  .conj (BoundedFormula.linkedMainStageTupleFormula z (f 22) (f 11) (f 23)).toFormula
    (.conj (validMainStageCodeFormula (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
      (f 7) (f 8) (f 9) (f 10) C D rD N)
    (.conj (BoundedFormula.serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20)).toFormula
    (.conj (serializedChronologyFormula (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20))
    (.conj (BoundedFormula.linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f)).toFormula
      (linkedMainInvariantFormula K Labels C D (f 0) (f 3) (f 11) (f 23))))))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainStageRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (f : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageRawFormula K Labels C D rD N z f) env ↔
      LinkedMainStageRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N) (env z)
        (fun j => env (f j)) := by
  have outer := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedMainStageTupleFormula z (f 22) (f 11) (f 23) env)
  have stage := M.realize_validMainStageCodeFormula pairing unions powers separation
    (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) C D rD N env members omega
  have tuple := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20) env)
  have serial := M.realize_serializedChronologyFormula pairing unions powers separation
    (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20) env members
  have terminal := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f) env)
  have invariant := M.realize_linkedMainInvariantFormula pairing unions powers separation collection
    K Labels C D (f 0) (f 3) (f 11) (f 23) env members ordinal
  have map : (fun j => env (linkedChronologyGraphs f j)) = linkedChronologyGraphs (fun j => env (f j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  change (Realize M.sets (BoundedFormula.linkedMainStageTupleFormula z (f 22) (f 11) (f 23)).toFormula env ∧
    Realize M.sets (validMainStageCodeFormula (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
      (f 7) (f 8) (f 9) (f 10) C D rD N) env ∧
    Realize M.sets (BoundedFormula.serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20)).toFormula env ∧
    Realize M.sets (serializedChronologyFormula (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20)) env ∧
    Realize M.sets (BoundedFormula.linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f)).toFormula env ∧
    Realize M.sets (linkedMainInvariantFormula K Labels C D (f 0) (f 3) (f 11) (f 23)) env) ↔ _
  rw [outer, stage, tuple, serial, terminal, invariant, map]
  simp only [LinkedMainStageRawCode, and_assoc]
  rfl

end TransitiveGround

end

section
open SetFormula
universe u

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}} {f : Fin 24 → ZFSet.{u}}

theorem exists_linked
    (raw : LinkedMainStageRawCode M K Labels C D rD N z f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : ∀ j, f j ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (omega : N = ZFSet.omega) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z := by
  obtain ⟨outer, stageEq, valid, _, serialEq, code, ordinal, domain, eP, er, eμ, eh, inv⟩ := raw
  let stage := GroundMainStage.ofValidity pairing unions powers separation
    (ground 0) (ground 1) (ground 2) (ground 3) (ground 4) (ground 5) (ground 7) (ground 10) hC hD hrD valid
  have code' : SerializedChronologyCode (insert (f 11) (f 11)) (f 13) C D rD N
      (linkedChronologyGraphs f) (f 19) (f 20) := domain ▸ code
  have graphsGround : ∀ j, linkedChronologyGraphs f j ∈ M.sets :=
    Fin.cases (ground 14) (Fin.cases (ground 15) (Fin.cases (ground 16)
      (Fin.cases (ground 17) (fun _ => ground 18))))
  let serial := code'.toGround (domain ▸ ground 12) (ground 13) graphsGround (ground 19) (ground 20) omega
  let main : GroundChronologicalMainStage M C D rD :=
    { stage := stage
      cutoff := f 11
      cutoff_ground := ground 11
      cutoff_ordinal := ordinal
      history := serial.toHistory
      carrier_eq := serial.fields.value_eq_of_entry 0 eP
      order_eq := serial.fields.value_eq_of_entry 1 er
      meet_eq := serial.fields.value_eq_of_entry 2 eμ
      height_eq := serial.fields.value_eq_of_entry 4 eh }
  have serialCode : serial.code = f 23 := by
    change serializedChronologyCode (insert (f 11) (f 11)) (f 13) (linkedChronologyGraphs f) (f 19) (f 20) = f 23
    rw [← domain]
    exact serialEq.symm
  obtain ⟨ps, gs, ls, pr, gr, lr, tm, cr, dr, sr⟩ := inv
  let linked : GroundLinkedMainStage M K Labels C D rD :=
    { main := main
      serial := serial
      agreement := fun j _ _ => Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j
      invariant := ⟨ps, gs, ls, pr, gr, lr, tm, cr, dr⟩
      serial_rank := serialCode ▸ sr }
  refine ⟨linked, ?_⟩
  change linkedMainStageCode stage.code (f 11) serial.code = z
  have scode : stage.code = f 22 := stageEq.symm
  rw [scode, serialCode]
  exact outer.symm

end LinkedMainStageRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

noncomputable def rawFields : Fin 24 → ZFSet.{u} :=
  (Fin.cases (linked.main.stage.carrier) (Fin.cases (linked.main.stage.order) (Fin.cases (linked.main.stage.meetGraph) (Fin.cases (linked.main.stage.actors) (Fin.cases (linked.main.stage.multiplication) (Fin.cases (linked.main.stage.inverse) (Fin.cases (linked.main.stage.identity) (Fin.cases (linked.main.stage.action) (Fin.cases (linked.main.stage.bottom) (Fin.cases (linked.main.stage.top) (Fin.cases (linked.main.stage.height) (Fin.cases (linked.main.cutoff) (Fin.cases (insert linked.main.cutoff linked.main.cutoff) (Fin.cases (linked.serial.fields.bound) (Fin.cases (linked.serial.fields.graph 0) (Fin.cases (linked.serial.fields.graph 1) (Fin.cases (linked.serial.fields.graph 2) (Fin.cases (linked.serial.fields.graph 3) (Fin.cases (linked.serial.fields.graph 4) (Fin.cases (linked.serial.layerBound) (Fin.cases (linked.serial.layers) (Fin.cases (linked.serial.fields.code) (Fin.cases (linked.main.stage.code) (fun _ => linked.serial.code))))))))))))))))))))))))

theorem rawFields_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    ∀ j, linked.rawFields j ∈ M.sets :=
  (Fin.cases (linked.main.stage.carrier_ground) (Fin.cases (linked.main.stage.order_ground) (Fin.cases (linked.main.stage.meet_ground) (Fin.cases (linked.main.stage.actors_ground) (Fin.cases (linked.main.stage.multiplication_ground) (Fin.cases (linked.main.stage.inverse_ground) (Fin.cases (linked.main.stage.identity_ground) (Fin.cases (linked.main.stage.action_ground) (Fin.cases (linked.main.stage.bottom_ground) (Fin.cases (linked.main.stage.top_ground) (Fin.cases (linked.main.stage.height_ground) (Fin.cases (linked.main.cutoff_ground) (Fin.cases (linked.serial.fields.time_ground) (Fin.cases (linked.serial.fields.bound_ground) (Fin.cases (linked.serial.fields.graph_ground 0) (Fin.cases (linked.serial.fields.graph_ground 1) (Fin.cases (linked.serial.fields.graph_ground 2) (Fin.cases (linked.serial.fields.graph_ground 3) (Fin.cases (linked.serial.fields.graph_ground 4) (Fin.cases (linked.serial.layer_bound_ground) (Fin.cases (linked.serial.layers_ground) (Fin.cases (linked.serial.fields.code_ground pairing) (Fin.cases (linked.main.stage.code_mem pairing) (fun _ => linked.serial.code_ground pairing))))))))))))))))))))))))

theorem rawFields_graphs : linkedChronologyGraphs linked.rawFields = linked.serial.fields.graph := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun i => Fin.elim0 i))))) j

theorem rawFields_code : LinkedMainStageRawCode M K Labels C D rD ZFSet.omega linked.code linked.rawFields := by
  unfold LinkedMainStageRawCode
  rw [linked.rawFields_graphs]
  refine ⟨rfl, rfl, linked.main.stage.validity, rfl, rfl, linked.serial.raw_code,
    linked.main.cutoff_ordinal, rfl, ?_, ?_, ?_, ?_, linked.invariant_code⟩
  · change ZFSet.pair linked.main.cutoff linked.main.stage.carrier ∈ linked.serial.fields.graph 0
    rw [← linked.terminal_values.1]
    exact linked.serial.fields.value_entry 0 (ZFSet.mem_insert _ _)
  · change ZFSet.pair linked.main.cutoff linked.main.stage.order ∈ linked.serial.fields.graph 1
    rw [← linked.terminal_values.2.1]
    exact linked.serial.fields.value_entry 1 (ZFSet.mem_insert _ _)
  · change ZFSet.pair linked.main.cutoff linked.main.stage.meetGraph ∈ linked.serial.fields.graph 2
    rw [← linked.terminal_values.2.2.1]
    exact linked.serial.fields.value_entry 2 (ZFSet.mem_insert _ _)
  · change ZFSet.pair linked.main.cutoff linked.main.stage.height ∈ linked.serial.fields.graph 4
    rw [← linked.terminal_values.2.2.2.2]
    exact linked.serial.fields.value_entry 4 (ZFSet.mem_insert _ _)

end GroundLinkedMainStage

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}}
variable {f g : Fin 24 → ZFSet.{u}}

theorem fields_unique (first : LinkedMainStageRawCode M K Labels C D rD N z f)
    (second : LinkedMainStageRawCode M K Labels C D rD N z g) : f = g := by
  obtain ⟨fo, fa, _, fh, fs, _⟩ := first
  obtain ⟨go, ga, _, gh, gs, _⟩ := second
  have outer := linkedMainStageCode_inj.1 (fo.symm.trans go)
  have stage := nonemptyTupleCode_injective 10 (fa.symm.trans (outer.1.trans ga))
  have serial := nonemptyTupleCode_injective 2 (fs.symm.trans (outer.2.2.trans gs))
  have history := nonemptyTupleCode_injective 6 (congrFun serial 0)
  have h21 : f 21 = g 21 := fh.trans ((congrFun serial 0).trans gh.symm)
  funext j
  exact (show ∀ j : Fin 24, f j = g j from (Fin.cases (congrFun stage 0) (Fin.cases (congrFun stage 1) (Fin.cases (congrFun stage 2) (Fin.cases (congrFun stage 3) (Fin.cases (congrFun stage 4) (Fin.cases (congrFun stage 5) (Fin.cases (congrFun stage 6) (Fin.cases (congrFun stage 7) (Fin.cases (congrFun stage 8) (Fin.cases (congrFun stage 9) (Fin.cases (congrFun stage 10) (Fin.cases (outer.2.1) (Fin.cases (congrFun history 0) (Fin.cases (congrFun history 1) (Fin.cases (congrFun history 2) (Fin.cases (congrFun history 3) (Fin.cases (congrFun history 4) (Fin.cases (congrFun history 5) (Fin.cases (congrFun history 6) (Fin.cases (congrFun serial 1) (Fin.cases (congrFun serial 2) (Fin.cases (h21) (Fin.cases (outer.1) (Fin.cases (outer.2.2) (fun i => Fin.elim0 i)))))))))))))))))))))))))) j

theorem exists_linked_fields
    (raw : LinkedMainStageRawCode M K Labels C D rD N z f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : ∀ j, f j ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (omega : N = ZFSet.omega) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z ∧ linked.rawFields = f := by
  obtain ⟨linked, equal⟩ := raw.exists_linked pairing unions powers separation ground hC hD hrD omega
  refine ⟨linked, equal, ?_⟩
  rw [omega] at raw
  have actual := linked.rawFields_code
  rw [equal] at actual
  exact actual.fields_unique raw

end LinkedMainStageRawCode
end

namespace GroundLinkedMainStage
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}

structure SameCode (first second : GroundLinkedMainStage M K Labels C D rD) : Prop where
  stage : first.main.stage = second.main.stage
  cutoff : first.main.cutoff = second.main.cutoff
  serial_code : first.serial.code = second.serial.code
  raw_fields : first.rawFields = second.rawFields
  field_graphs : first.serial.fields.graph = second.serial.fields.graph

theorem same_code (first second : GroundLinkedMainStage M K Labels C D rD)
    (equal : first.code = second.code) : SameCode first second := by
  have outer := linkedMainStageCode_inj.1 equal
  have other : LinkedMainStageRawCode M K Labels C D rD ZFSet.omega first.code second.rawFields :=
    equal.symm ▸ second.rawFields_code
  have fields := first.rawFields_code.fields_unique other
  refine ⟨GroundMainStage.code_injective outer.1, outer.2.1, outer.2.2, fields, ?_⟩
  rw [← first.rawFields_graphs, ← second.rawFields_graphs, fields]

namespace SameCode
variable {first second : GroundLinkedMainStage M K Labels C D rD}
variable (same : SameCode first second)
include same

theorem field_bound : first.serial.fields.bound = second.serial.fields.bound :=
  congrFun same.raw_fields 13

theorem layer_bound : first.serial.layerBound = second.serial.layerBound :=
  congrFun same.raw_fields 19

theorem layers : first.serial.layers = second.serial.layers :=
  congrFun same.raw_fields 20

theorem serial_values (j : Fin 5) (s : ZFSet.{u}) :
    first.serial.fields.value j s = second.serial.fields.value j s := by
  classical
  by_cases hs : s ∈ insert first.main.cutoff first.main.cutoff
  · have entry := first.serial.fields.value_entry j hs
    rw [same.field_graphs] at entry
    exact (second.serial.fields.value_eq_of_entry j entry).symm
  · have ht : s ∉ insert second.main.cutoff second.main.cutoff := by
      simpa only [same.cutoff] using hs
    change (first.serial.fields.graphFunction j).totalValue s =
      (second.serial.fields.graphFunction j).totalValue s
    rw [FunctionGraphOn.totalValue_outside _ hs, FunctionGraphOn.totalValue_outside _ ht]

theorem history_values (j : Fin 5) (s : ZFSet.{u})
    (hs : s ∈ insert first.main.cutoff first.main.cutoff) :
    first.main.history.fieldValue j s = second.main.history.fieldValue j s := by
  have ht : s ∈ insert second.main.cutoff second.main.cutoff := by
    simpa only [same.cutoff] using hs
  rw [← first.agreement j s hs, ← second.agreement j s ht]
  exact same.serial_values j s

theorem birth : first.main.birth = second.main.birth := by
  have equal := same.history_values 3 first.main.cutoff (ZFSet.mem_insert _ _)
  exact equal.trans (congrArg second.main.history.birth same.cutoff)

theorem history_five (s : ZFSet.{u}) (before : s = first.main.cutoff ∨ s ∈ first.main.cutoff) :
    first.main.history.space s = second.main.history.space s ∧
    first.main.history.order s = second.main.history.order s ∧
    first.main.history.meetGraph s = second.main.history.meetGraph s ∧
    first.main.history.birth s = second.main.history.birth s ∧
    first.main.history.height s = second.main.history.height s :=
  ⟨same.history_values 0 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 1 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 2 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 3 s (ZFSet.mem_insert_iff.2 before),
    same.history_values 4 s (ZFSet.mem_insert_iff.2 before)⟩

end SameCode

end GroundLinkedMainStage

end PartitionPilot.Forcing

end OAI
