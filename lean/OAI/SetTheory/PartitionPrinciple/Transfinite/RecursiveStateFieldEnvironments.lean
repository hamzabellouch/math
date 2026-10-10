import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInvariantSuccessors

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

structure RecursiveStateData where
  D : ZFSet.{u}
  rD : ZFSet.{u}
  μD : ZFSet.{u}
  J : ZFSet.{u}
  Qs : ZFSet.{u}
  rs : ZFSet.{u}
  μs : ZFSet.{u}
  As : ZFSet.{u}
  Es : ZFSet.{u}
  Fs : ZFSet.{u}
  Ss : ZFSet.{u}
  Maps : ZFSet.{u}
  A : ZFSet.{u}

namespace RecursiveStateData

def field (state : RecursiveStateData.{u}) : Fin 13 → ZFSet.{u} :=
  Fin.cases state.D (Fin.cases state.rD (Fin.cases state.μD (Fin.cases state.J (Fin.cases state.Qs (Fin.cases state.rs (Fin.cases state.μs (Fin.cases state.As (Fin.cases state.Es (Fin.cases state.Fs (Fin.cases state.Ss (Fin.cases state.Maps (Fin.cases state.A (Fin.elim0)))))))))))))

noncomputable def code (state : RecursiveStateData.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 12 state.field

theorem field_injective : Function.Injective field.{u} := by
  intro first second equal
  cases first
  cases second
  congr 1
  · exact congrFun equal (0 : Fin 13)
  · exact congrFun equal (1 : Fin 13)
  · exact congrFun equal (2 : Fin 13)
  · exact congrFun equal (3 : Fin 13)
  · exact congrFun equal (4 : Fin 13)
  · exact congrFun equal (5 : Fin 13)
  · exact congrFun equal (6 : Fin 13)
  · exact congrFun equal (7 : Fin 13)
  · exact congrFun equal (8 : Fin 13)
  · exact congrFun equal (9 : Fin 13)
  · exact congrFun equal (10 : Fin 13)
  · exact congrFun equal (11 : Fin 13)
  · exact congrFun equal (12 : Fin 13)

theorem code_injective : Function.Injective code.{u} := by
  intro first second equal
  exact field_injective (nonemptyTupleCode_injective 12 equal)

noncomputable def decode (z : ZFSet.{u}) (valid : ∃ state : RecursiveStateData.{u}, state.code = z) :
    RecursiveStateData.{u} := Classical.choose valid

theorem code_decode (z : ZFSet.{u}) (valid : ∃ state : RecursiveStateData.{u}, state.code = z) :
    (decode z valid).code = z := Classical.choose_spec valid

theorem decode_code (state : RecursiveStateData.{u}) :
    decode state.code ⟨state, rfl⟩ = state := code_injective (code_decode _ _)

theorem decode_field (state : RecursiveStateData.{u}) (j : Fin 13) :
    (decode state.code ⟨state, rfl⟩).field j = state.field j := by rw [decode_code]

end RecursiveStateData

noncomputable def recursiveStateCode (D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}) : ZFSet.{u} :=
  (RecursiveStateData.mk D rD μD J Qs rs μs As Es Fs Ss Maps A).code

theorem recursiveStateCode_inj
    {D rD μD J Qs rs μs As Es Fs Ss Maps A D' rD' μD' J' Qs' rs' μs' As' Es' Fs' Ss' Maps' A' : ZFSet.{u}} :
    recursiveStateCode D rD μD J Qs rs μs As Es Fs Ss Maps A = recursiveStateCode D' rD' μD' J' Qs' rs' μs' As' Es' Fs' Ss' Maps' A' ↔
      D = D' ∧ rD = rD' ∧ μD = μD' ∧ J = J' ∧ Qs = Qs' ∧ rs = rs' ∧ μs = μs' ∧ As = As' ∧ Es = Es' ∧ Fs = Fs' ∧ Ss = Ss' ∧ Maps = Maps' ∧ A = A' := by
  constructor
  · intro equal
    exact RecursiveStateData.mk.inj (RecursiveStateData.code_injective equal)
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

namespace BoundedFormula

open SetFormula

def recursiveStateFormula {n} (z D rD μD J Qs rs μs As Es Fs Ss Maps A : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 12 z
    (Fin.cases D (Fin.cases rD (Fin.cases μD (Fin.cases J (Fin.cases Qs (Fin.cases rs (Fin.cases μs (Fin.cases As (Fin.cases Es (Fin.cases Fs (Fin.cases Ss (Fin.cases Maps (Fin.cases A (Fin.elim0))))))))))))))

theorem truth_recursiveStateFormula {n} (z D rD μD J Qs rs μs As Es Fs Ss Maps A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (recursiveStateFormula z D rD μD J Qs rs μs As Es Fs Ss Maps A) env ↔
      env z = recursiveStateCode (env D) (env rD) (env μD) (env J) (env Qs) (env rs) (env μs) (env As) (env Es) (env Fs) (env Ss) (env Maps) (env A) := by
  rw [recursiveStateFormula, truth_nonemptyTupleFormula]
  rfl

theorem realize_recursiveStateFormula (M : TransitiveGround.{u}) {n}
    (z D rD μD J Qs rs μs As Es Fs Ss Maps A : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (recursiveStateFormula z D rD μD J Qs rs μs As Es Fs Ss Maps A).toFormula env ↔
      env z = recursiveStateCode (env D) (env rD) (env μD) (env J) (env Qs) (env rs) (env μs) (env As) (env Es) (env Fs) (env Ss) (env Maps) (env A) :=
  (realize_toFormula M _ env members).trans (truth_recursiveStateFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env)

end BoundedFormula

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem recursiveStateData_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (state : RecursiveStateData.{u}) (ground : ∀ j, state.field j ∈ M.sets) :
    state.code ∈ M.sets := M.nonemptyTupleCode_mem pairing 12 state.field ground

theorem recursiveStateData_field_mem (state : RecursiveStateData.{u})
    (ground : state.code ∈ M.sets) : ∀ j, state.field j ∈ M.sets :=
  M.nonemptyTupleCode_field_mem 12 state.field ground

theorem recursiveStateData_code_mem_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (state : RecursiveStateData.{u}) :
    state.code ∈ M.sets ↔ ∀ j, state.field j ∈ M.sets :=
  ⟨M.recursiveStateData_field_mem state, M.recursiveStateData_code_mem pairing state⟩

theorem recursiveStateCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
    (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets)
    (hμD : μD ∈ M.sets)
    (hJ : J ∈ M.sets)
    (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets)
    (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets)
    (hEs : Es ∈ M.sets)
    (hFs : Fs ∈ M.sets)
    (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets)
    (hA : A ∈ M.sets)
    : recursiveStateCode D rD μD J Qs rs μs As Es Fs Ss Maps A ∈ M.sets :=
  M.recursiveStateData_code_mem pairing ⟨D, rD, μD, J, Qs, rs, μs, As, Es, Fs, Ss, Maps, A⟩
    (Fin.cases hD (Fin.cases hrD (Fin.cases hμD (Fin.cases hJ (Fin.cases hQs (Fin.cases hrs (Fin.cases hμs (Fin.cases hAs (Fin.cases hEs (Fin.cases hFs (Fin.cases hSs (Fin.cases hMaps (Fin.cases hA ((fun i => Fin.elim0 i)))))))))))))))

theorem recursiveStateCode_mem_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}) :
    recursiveStateCode D rD μD J Qs rs μs As Es Fs Ss Maps A ∈ M.sets ↔
      D ∈ M.sets ∧ rD ∈ M.sets ∧ μD ∈ M.sets ∧ J ∈ M.sets ∧ Qs ∈ M.sets ∧ rs ∈ M.sets ∧ μs ∈ M.sets ∧ As ∈ M.sets ∧ Es ∈ M.sets ∧ Fs ∈ M.sets ∧ Ss ∈ M.sets ∧ Maps ∈ M.sets ∧ A ∈ M.sets := by
  constructor
  · intro ground
    have fields := M.recursiveStateData_field_mem ⟨D, rD, μD, J, Qs, rs, μs, As, Es, Fs, Ss, Maps, A⟩ ground
    exact ⟨fields 0, fields 1, fields 2, fields 3, fields 4, fields 5, fields 6, fields 7, fields 8, fields 9, fields 10, fields 11, fields 12⟩
  · rintro ⟨hD, hrD, hμD, hJ, hQs, hrs, hμs, hAs, hEs, hFs, hSs, hMaps, hA⟩
    exact M.recursiveStateCode_mem pairing hD hrD hμD hJ hQs hrs hμs hAs hEs hFs hSs hMaps hA

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

namespace CodedRecursiveMapInputs
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}

def toState (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) : RecursiveStateData :=
  ⟨D, rD, μD, J, Qs, rs, μs, As, Es, Fs, Ss, Maps, A⟩

end CodedRecursiveMapInputs

namespace RecursiveStateData
noncomputable def fresh (state : RecursiveStateData.{u}) :=
  indexedAttachmentFresh state.J state.Qs state.rs state.As

noncomputable def currentCarrier (state : RecursiveStateData.{u}) :=
  taggedExtension state.D state.fresh

noncomputable def currentOrder (state : RecursiveStateData.{u}) :=
  codedAttachmentOrder state.D state.fresh state.rD
    (batchAttachmentInsideGraph state.J state.Qs state.rs)
    (batchAttachmentShadowGraph state.J state.D state.Qs state.μs state.As state.Es)
    (batchAttachmentUpperGraph state.J state.D state.Qs state.Fs)

noncomputable def currentMeet (state : RecursiveStateData.{u}) :=
  canonicalMeetGraph state.currentCarrier state.currentOrder

noncomputable def successor (state : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) : RecursiveStateData.{u} :=
  let K := recursiveAttachmentIndices I state.J state.D (⋃₀ ⋃₀ state.Fs) Sources state.Fs
  let Qs := pairSecondField I state.J K state.Qs
  let rs := pairSecondField I state.J K state.rs
  let μs := pairSecondField I state.J K state.μs
  let As := pairSecondField I state.J K state.As
  let N := indexedAttachmentFresh K Qs rs As
  let C := taggedExtension state.currentCarrier N
  { D := state.currentCarrier
    rD := state.currentOrder
    μD := state.currentMeet
    J := K
    Qs := Qs
    rs := rs
    μs := μs
    As := As
    Es := M.groundPairCompositions K I state.J (familyPointBound state.Qs)
      state.D state.currentCarrier state.Es state.Maps
    Fs := M.groundPairPushFilters K I state.J state.currentCarrier state.currentOrder state.Maps state.Fs
    Ss := recursiveSeparatorFamily K I state.J state.D state.currentCarrier state.Maps state.Ss
    Maps := M.groundLiftedCompressionFamily I state.J state.D state.currentCarrier C state.fresh
      (familyPointBound state.Qs) state.Maps Sources state.Fs Reps G state.A
    A := taggedActionGraph G state.currentCarrier N state.A
      (indexedTaskActionGraph G K (familyPointBound state.Qs) N
        (indexedTaskActionGraph G I state.J K T)) }

end RecursiveStateData

namespace CodedRecursiveMapInputs
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

theorem toState_currentCarrier : h.toState.currentCarrier = d.batchCarrier := rfl
theorem toState_currentOrder : h.toState.currentOrder = d.batchOrder := rfl
theorem toState_currentMeet : h.toState.currentMeet = d.batchMeetGraph := rfl

theorem toState_successor (M : TransitiveGround.{u}) (next : h.NextInputs M)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) :
    inputs.toState = h.toState.successor M I Sources Reps G T := rfl

end CodedRecursiveMapInputs

structure RecursiveStateCoherence (I : ZFSet.{u}) (first second : RecursiveStateData.{u}) : Prop where
  carrier : first.D ⊆ second.D
  order : ∀ x ∈ first.D, ∀ y ∈ first.D,
    ZFSet.pair x y ∈ second.rD ↔ ZFSet.pair x y ∈ first.rD
  meet : ∀ x ∈ first.D, ∀ y ∈ first.D, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ second.μD ↔ ZFSet.pair (ZFSet.pair x y) z ∈ first.μD
  currentCarrier : first.currentCarrier ⊆ second.currentCarrier
  currentOrder : ∀ x ∈ first.currentCarrier, ∀ y ∈ first.currentCarrier,
    ZFSet.pair x y ∈ second.currentOrder ↔ ZFSet.pair x y ∈ first.currentOrder
  currentMeet : ∀ x ∈ first.currentCarrier, ∀ y ∈ first.currentCarrier, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ second.currentMeet ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ first.currentMeet
  action : ∀ g x, x ∈ first.currentCarrier → ∀ y,
    ZFSet.pair (ZFSet.pair g x) y ∈ second.A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ first.A
  maps : ∀ i ∈ I, ∀ S S', ZFSet.pair i S ∈ first.Maps → ZFSet.pair i S' ∈ second.Maps →
    ∀ x ∈ first.D, ∀ y, ZFSet.pair x y ∈ S' ↔ ZFSet.pair x y ∈ S

namespace RecursiveStateCoherence
variable {I : ZFSet.{u}} {first middle last : RecursiveStateData.{u}}

theorem refl (maps : FunctionGraphOn I first.Maps) : RecursiveStateCoherence I first first where
  carrier := fun _ hx => hx
  order := fun _ _ _ _ => Iff.rfl
  meet := fun _ _ _ _ _ => Iff.rfl
  currentCarrier := fun _ hx => hx
  currentOrder := fun _ _ _ _ => Iff.rfl
  currentMeet := fun _ _ _ _ _ => Iff.rfl
  action := fun _ _ _ _ => Iff.rfl
  maps := by
    intro _ _ S S' firstEntry secondEntry _ _ _
    exact maps.unique firstEntry secondEntry ▸ Iff.rfl

theorem trans (left : RecursiveStateCoherence I first middle)
    (right : RecursiveStateCoherence I middle last) (middleMaps : FunctionGraphOn I middle.Maps) :
    RecursiveStateCoherence I first last where
  carrier := fun _ hx => right.carrier (left.carrier hx)
  order := fun _ hx _ hy => (right.order _ (left.carrier hx) _ (left.carrier hy)).trans (left.order _ hx _ hy)
  meet := fun _ hx _ hy _ => (right.meet _ (left.carrier hx) _ (left.carrier hy) _).trans (left.meet _ hx _ hy _)
  currentCarrier := fun _ hx => right.currentCarrier (left.currentCarrier hx)
  currentOrder := fun _ hx _ hy =>
    (right.currentOrder _ (left.currentCarrier hx) _ (left.currentCarrier hy)).trans (left.currentOrder _ hx _ hy)
  currentMeet := fun _ hx _ hy _ =>
    (right.currentMeet _ (left.currentCarrier hx) _ (left.currentCarrier hy) _).trans (left.currentMeet _ hx _ hy _)
  action := fun _ _ hx _ => (right.action _ _ (left.currentCarrier hx) _).trans (left.action _ _ hx _)
  maps := by
    intro i hi S S' oldEntry newEntry x hx y
    obtain ⟨B, middleEntry⟩ := middleMaps.total hi
    exact (right.maps i hi B S' middleEntry newEntry x (left.carrier hx) y).trans
      (left.maps i hi S B oldEntry middleEntry x hx y)

end RecursiveStateCoherence

namespace CodedRecursiveMapInputs
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem next_coherent
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) : RecursiveStateCoherence I h.toState inputs.toState where
  carrier := fun _ hx => old_mem_taggedExtension hx
  order := fun _ hx _ hy => d.old_order_iff hx hy
  meet := fun _ hx _ hy _ => d.old_meet_iff hx hy
  currentCarrier := fun _ hx => old_mem_taggedExtension hx
  currentOrder := fun _ hx _ hy => next.old_order_iff hx hy
  currentMeet := fun _ hx _ hy _ => next.old_meet_iff hx hy
  action := fun _ _ hx _ => h.nextAction_old_iff hx
  maps := by
    intro i _ S S' oldEntry newEntry x hx y
    obtain ⟨_, rfl⟩ := (entries i S').1 newEntry
    exact h.liftSection_old_iff M next oldEntry hx

end CodedRecursiveMapInputs

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.RecursiveStateData
universe u

def ofFields (fields : Fin 13 → ZFSet.{u}) : RecursiveStateData.{u} :=
  ⟨fields 0, fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
    fields 7, fields 8, fields 9, fields 10, fields 11, fields 12⟩

theorem ofFields_field (state : RecursiveStateData.{u}) : ofFields state.field = state := by
  cases state
  rfl

theorem field_ofFields (fields : Fin 13 → ZFSet.{u}) : (ofFields fields).field = fields := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  exact Fin.elim0 j

theorem code_ofFields (fields : Fin 13 → ZFSet.{u}) :
    (ofFields fields).code = nonemptyTupleCode 12 fields := by
  rw [code, field_ofFields]

def successorEnvironment (state : RecursiveStateData.{u}) (I Sources Reps G T : ZFSet.{u}) :
    Fin 18 → ZFSet.{u} :=
  Fin.addCases (m := 13) (n := 5) state.field (SetFormula.extend I (SetFormula.extend Sources
    (SetFormula.extend Reps (SetFormula.extend G (SetFormula.extend T Fin.elim0)))))

noncomputable def successorCodeFromEnvironment (M : TransitiveGround.{u})
    (env : Fin 18 → ZFSet.{u}) : ZFSet.{u} :=
  ((ofFields (fun j => env (j.castAdd 5))).successor M
    (env 13) (env 14) (env 15) (env 16) (env 17)).code

theorem successorCodeFromEnvironment_spec (state : RecursiveStateData.{u})
    (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) :
    successorCodeFromEnvironment M (state.successorEnvironment I Sources Reps G T) =
      (state.successor M I Sources Reps G T).code := by
  simp only [successorCodeFromEnvironment, successorEnvironment, Fin.addCases_left]
  rw [ofFields_field]
  rfl

end PartitionPilot.Forcing.RecursiveStateData

end OAI
