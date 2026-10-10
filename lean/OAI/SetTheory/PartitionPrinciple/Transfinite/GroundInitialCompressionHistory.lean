import OAI.SetTheory.PartitionPrinciple.Definability.GroundCompositionFamilyFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSeparatorFamilyFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionStampBounds
import OAI.SetTheory.PartitionPrinciple.Geometry.InitialCompressionAccounting

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_pairCompositions :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.groundPairCompositions (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) where
  formula := compositionFamilyFormula 0 1 2 3 4 5 6 7 8
  closed _env members := M.pairCompositionFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6) (members 7)
    (M.groundRelations_mem pairing unions powers separation (members 3) (members 5))
  correct env members z hz := M.realize_compositionFamilyFormula pairing 0 1 2 3 4 5 6 7 8
    (extend z env) (Fin.cases hz members)

noncomputable def definable_pairPushFilters :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      M.groundPairPushFilters (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) where
  formula := pushFilterFamilyFormula 0 1 2 3 4 5 6 7
  closed _env members := M.pairPushFilterFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
    (M.groundPower_mem powers (members 3))
  correct env members z hz := M.realize_pushFilterFamilyFormula pairing 0 1 2 3 4 5 6 7
    (extend z env) (Fin.cases hz members)

noncomputable def definable_recursiveSeparators :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      recursiveSeparatorFamily (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) where
  formula := recursiveSeparatorFamilyFormula 0 1 2 3 4 5 6 7
  closed _env members := M.recursiveSeparatorFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
  correct env members z hz := M.realize_recursiveSeparatorFamilyFormula pairing 0 1 2 3 4 5 6 7
    (extend z env) (Fin.cases hz members)

noncomputable def definable_recursiveAction :
    GroundDefinableFunction M (fun env : Fin 9 → ZFSet.{u} =>
      taggedActionGraph (env 0) (env 1) (env 6) (env 7)
        (indexedTaskActionGraph (env 0) (env 4) (env 5) (env 6)
          (indexedTaskActionGraph (env 0) (env 2) (env 3) (env 4) (env 8)))) where
  formula := recursiveActionGraphFormula 0 1 2 3 4 5 6 7 8 9
  closed env members := by
    have index := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members 0) (members 2) (members 3) (members 4) (members 8)
    have fresh := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members 0) (members 4) (members 5) (members 6) index
    exact M.taggedActionGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 6) (members 7) fresh
  correct env members z hz := M.realize_recursiveActionGraphFormula pairing unions powers separation
    0 1 2 3 4 5 6 7 8 9 (extend z env) (Fin.cases hz members)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace RecursiveStateData
noncomputable def iterate (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) : Nat → RecursiveStateData.{u}
  | 0 => initial
  | n + 1 => (iterate initial M I Sources Reps G T n).successor M I Sources Reps G T

theorem iterate_zero (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) : initial.iterate M I Sources Reps G T 0 = initial := rfl

theorem iterate_succ (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) (n : Nat) :
    initial.iterate M I Sources Reps G T (n + 1) =
      (initial.iterate M I Sources Reps G T n).successor M I Sources Reps G T := rfl

end RecursiveStateData

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)

noncomputable def next : GroundCompressionState M seed :=
  Classical.choose (state.exists_successor pairing unions powers separation hI hSources hReps hG hT)

theorem next_data :
    (state.next pairing unions powers separation hI hSources hReps hG hT).data =
      state.data.successor M I Sources Reps G T :=
  Classical.choose_spec (state.exists_successor pairing unions powers separation hI hSources hReps hG hT)

noncomputable def iterate : Nat → GroundCompressionState M seed
  | 0 => state
  | n + 1 => (iterate n).next pairing unions powers separation hI hSources hReps hG hT

theorem iterate_data (n : Nat) :
    (state.iterate pairing unions powers separation hI hSources hReps hG hT n).data =
      state.data.iterate M I Sources Reps G T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((state.iterate pairing unions powers separation hI hSources hReps hG hT n).next
      pairing unions powers separation hI hSources hReps hG hT).data = _
    rw [next_data, ih, RecursiveStateData.iterate_succ]

include pairing unions powers separation hI hSources hReps hG hT in
theorem canonical_iterate_code_mem (n : Nat) :
    (state.data.iterate M I Sources Reps G T n).code ∈ M.sets := by
  rw [← state.iterate_data pairing unions powers separation hI hSources hReps hG hT n]
  exact (state.iterate pairing unions powers separation hI hSources hReps hG hT n).code_mem pairing

include pairing unions powers separation hI hSources hReps hG hT in
theorem canonical_iterate_valid (n : Nat) :
    ∃ current : GroundCompressionState M seed,
      current.data = state.data.iterate M I Sources Reps G T n :=
  ⟨state.iterate pairing unions powers separation hI hSources hReps hG hT n,
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n⟩

end GroundCompressionState
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
universe u

theorem pairSecondField_constant {I J K : ZFSet.{u}} (value : ZFSet.{u})
    (subset : K ⊆ ZFSet.prod I J) :
    pairSecondField I J K (constantFamilyGraph J value) = constantFamilyGraph K value := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    unfold pairSecondField pairFieldGraph at entry
    obtain ⟨k, hk, x, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
    have old := ((pairSecondField_entry_iff hi hj).1 entry).2
    exact (pair_mem_constantFamilyGraph K value _ x).2
      ⟨hk, ((pair_mem_constantFamilyGraph J value j x).1 old).2⟩
  · intro entry
    change z ∈ ZFSet.prod K {value} at entry
    obtain ⟨k, hk, x, _, rfl⟩ := ZFSet.mem_prod.1 entry
    have equal := ((pair_mem_constantFamilyGraph K value k x).1 entry).2
    obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
    exact (pairSecondField_entry_iff hi hj).2
      ⟨hk, (pair_mem_constantFamilyGraph J value j x).2 ⟨hj, equal⟩⟩

structure RecursiveTemplateConstancy (P r μ : ZFSet.{u}) (state : RecursiveStateData.{u}) : Prop where
  spaces : state.Qs = constantFamilyGraph state.J P
  relations : state.rs = constantFamilyGraph state.J r
  meets : state.μs = constantFamilyGraph state.J μ

namespace RecursiveTemplateConstancy
variable {P r μ : ZFSet.{u}} {state : RecursiveStateData.{u}}
variable (constant : RecursiveTemplateConstancy P r μ state)
include constant

theorem space_entry_iff (i Q : ZFSet.{u}) :
    ZFSet.pair i Q ∈ state.Qs ↔ i ∈ state.J ∧ Q = P := by
  rw [constant.spaces, pair_mem_constantFamilyGraph]

theorem relation_entry_iff (i relation : ZFSet.{u}) :
    ZFSet.pair i relation ∈ state.rs ↔ i ∈ state.J ∧ relation = r := by
  rw [constant.relations, pair_mem_constantFamilyGraph]

theorem meet_entry_iff (i operation : ZFSet.{u}) :
    ZFSet.pair i operation ∈ state.μs ↔ i ∈ state.J ∧ operation = μ := by
  rw [constant.meets, pair_mem_constantFamilyGraph]

theorem successor (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) :
    RecursiveTemplateConstancy P r μ (state.successor M I Sources Reps G T) := by
  let K := recursiveAttachmentIndices I state.J state.D (⋃₀ ⋃₀ state.Fs) Sources state.Fs
  have subset : K ⊆ ZFSet.prod I state.J := recursiveAttachmentIndices_subset _ _ _ _ _ _
  constructor
  · change pairSecondField I state.J K state.Qs = constantFamilyGraph K P
    rw [constant.spaces]
    exact pairSecondField_constant P subset
  · change pairSecondField I state.J K state.rs = constantFamilyGraph K r
    rw [constant.relations]
    exact pairSecondField_constant r subset
  · change pairSecondField I state.J K state.μs = constantFamilyGraph K μ
    rw [constant.meets]
    exact pairSecondField_constant μ subset

theorem iterate (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) (n : Nat) :
    RecursiveTemplateConstancy P r μ (state.iterate M I Sources Reps G T n) := by
  induction n with
  | zero => exact constant
  | succ n ih => exact ih.successor M I Sources Reps G T

end RecursiveTemplateConstancy

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def decodedSuccessorFormula (definition : SetFormula 19) : SetFormula 7 :=
  exBlock 13 (.conj
    (BoundedFormula.nonemptyTupleFormula 12 (suffixIndex 7 13 0) (prefixIndex 7 13)).toFormula
    (reindex (extend (suffixIndex 7 13 1)
      (Fin.addCases (m := 13) (n := 5) (prefixIndex 7 13)
        (fun j => suffixIndex 7 13 j.succ.succ))) definition))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_decodedSuccessorFormula
    (definition : GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M))
    (params : Fin 5 → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets (decodedSuccessorFormula definition.formula) (extend x (extend y params)) ↔
      ∃ fields : Fin 13 → ZFSet.{u}, (∀ i, fields i ∈ M.sets) ∧
        x = nonemptyTupleCode 12 fields ∧
        y = RecursiveStateData.successorCodeFromEnvironment M
          (Fin.addCases (m := 13) (n := 5) fields params) := by
  rw [decodedSuccessorFormula, realize_exBlock]
  apply exists_congr
  intro fields
  apply and_congr_right
  intro hfields
  have henv : ∀ i, extendMany 13 fields (extend x (extend y params)) i ∈ M.sets :=
    extendMany_members 13 fields _ hfields (Fin.cases hx (Fin.cases hy members))
  change (Realize M.sets (BoundedFormula.nonemptyTupleFormula 12
      (suffixIndex 7 13 0) (prefixIndex 7 13)).toFormula _ ∧ _) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ henv, BoundedFormula.truth_nonemptyTupleFormula,
    realize_reindex, map_extend]
  have fieldsEqual : (fun i => extendMany 13 fields (extend x (extend y params))
      (prefixIndex 7 13 i)) = fields := by
    funext i
    exact extendMany_prefix 13 fields _ i
  have envEqual : (fun i => extendMany 13 fields (extend x (extend y params))
      (Fin.addCases (m := 13) (n := 5) (prefixIndex 7 13)
        (fun j => suffixIndex 7 13 j.succ.succ) i)) =
      Fin.addCases (m := 13) (n := 5) fields params := by
    funext i
    refine Fin.addCases (m := 13) (n := 5) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      exact extendMany_prefix 13 fields _ j
    · simp only [Fin.addCases_right]
      exact extendMany_suffix 13 fields _ j.succ.succ
  rw [fieldsEqual, envEqual, extendMany_suffix, extendMany_suffix]
  change (x = nonemptyTupleCode 12 fields ∧
    Realize M.sets definition.formula
      (extend y (Fin.addCases (m := 13) (n := 5) fields params))) ↔ _
  rw [definition.correct _ (fun i =>
    Fin.addCases (m := 13) (n := 5)
      (fun j => by simpa only [Fin.addCases_left] using hfields j)
      (fun j => by simpa only [Fin.addCases_right] using members j) i) y hy]

theorem realize_recursiveSuccessorCode
    (definition : GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M))
    (state : RecursiveStateData.{u}) (hstate : state.code ∈ M.sets)
    {I Sources Reps G T y : ZFSet.{u}}
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets (decodedSuccessorFormula definition.formula)
      (extend state.code (extend y (extend I (extend Sources
        (extend Reps (extend G (extend T Fin.elim0))))))) ↔
      y = (state.successor M I Sources Reps G T).code := by
  rw [M.realize_decodedSuccessorFormula definition _
    (Fin.cases hI (Fin.cases hSources (Fin.cases hReps (Fin.cases hG (Fin.cases hT
      (fun i => Fin.elim0 i)))))) hstate hy]
  constructor
  · rintro ⟨fields, _, code, next⟩
    have equal : RecursiveStateData.ofFields fields = state :=
      RecursiveStateData.code_injective ((RecursiveStateData.code_ofFields fields).trans code.symm)
    have fieldsEqual : fields = state.field := by
      rw [← RecursiveStateData.field_ofFields fields, equal]
    rw [fieldsEqual] at next
    exact next.trans (state.successorCodeFromEnvironment_spec M I Sources Reps G T)
  · intro next
    refine ⟨state.field, M.recursiveStateData_field_mem state hstate, rfl, ?_⟩
    exact next.trans (state.successorCodeFromEnvironment_spec M I Sources Reps G T).symm

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def recursiveSuccessorTerm : GroundSetTerm M 18 :=
  let v : Fin 18 → GroundSetTerm M 18 := GroundSetTerm.var M
  let union (term : GroundSetTerm M 18) :=
    GroundSetTerm.app (M.definable_sUnion unions) (Fin.cases term Fin.elim0)
  let bound := union (union (union (v 4)))
  let oldFresh := GroundSetTerm.app
    (M.definable_indexedFresh pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 4) (Fin.cases (v 5) (Fin.cases (v 7) (Fin.elim0)))))
  let carrier := GroundSetTerm.app
    (M.definable_taggedExtension pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (oldFresh) (Fin.elim0)))
  let inside := GroundSetTerm.app
    (M.definable_batchInside pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 4) (Fin.cases (v 5) (Fin.elim0))))
  let shadow := GroundSetTerm.app
    (M.definable_batchShadow pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (v 4) (Fin.cases (v 6) (Fin.cases (v 7) (Fin.cases (v 8) (Fin.elim0)))))))
  let upper := GroundSetTerm.app
    (M.definable_batchUpper pairing unions powers separation)
    (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (v 4) (Fin.cases (v 9) (Fin.elim0)))))
  let order := GroundSetTerm.app
    (M.definable_codedAttachmentOrder pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (oldFresh) (Fin.cases (v 1) (Fin.cases (inside) (Fin.cases (shadow) (Fin.cases (upper) (Fin.elim0)))))))
  let meet := GroundSetTerm.app
    (M.definable_canonicalMeet pairing unions powers separation)
    (Fin.cases (carrier) (Fin.cases (order) (Fin.elim0)))
  let indices := GroundSetTerm.app
    (M.definable_recursiveIndices pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (union (union (v 9))) (Fin.cases (v 14) (Fin.cases (v 9) (Fin.elim0)))))))
  let spaces := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 4) (Fin.elim0)))))
  let relations := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 5) (Fin.elim0)))))
  let meets := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 6) (Fin.elim0)))))
  let anchors := GroundSetTerm.app
    (M.definable_pairSecondField pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (v 7) (Fin.elim0)))))
  let fresh := GroundSetTerm.app
    (M.definable_indexedFresh pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (spaces) (Fin.cases (relations) (Fin.cases (anchors) (Fin.elim0)))))
  let nextCarrier := GroundSetTerm.app
    (M.definable_taggedExtension pairing unions powers separation)
    (Fin.cases (carrier) (Fin.cases (fresh) (Fin.elim0)))
  let embeddings := GroundSetTerm.app
    (M.definable_pairCompositions pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (bound) (Fin.cases (v 0) (Fin.cases (carrier) (Fin.cases (v 8) (Fin.cases (v 11) (Fin.elim0)))))))))
  let filters := GroundSetTerm.app
    (M.definable_pairPushFilters pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (v 11) (Fin.cases (v 9) (Fin.elim0))))))))
  let separators := GroundSetTerm.app
    (M.definable_recursiveSeparators pairing unions powers separation)
    (Fin.cases (indices) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (carrier) (Fin.cases (v 11) (Fin.cases (v 10) (Fin.elim0))))))))
  let maps := GroundSetTerm.app
    (M.definable_liftedCompressionFamily pairing unions powers separation)
    (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (v 0) (Fin.cases (carrier) (Fin.cases (nextCarrier) (Fin.cases (oldFresh) (Fin.cases (bound) (Fin.cases (v 11) (Fin.cases (v 14) (Fin.cases (v 9) (Fin.cases (v 15) (Fin.cases (v 16) (Fin.cases (v 12) (Fin.elim0))))))))))))))
  let action := GroundSetTerm.app
    (M.definable_recursiveAction pairing unions powers separation)
    (Fin.cases (v 16) (Fin.cases (carrier) (Fin.cases (v 13) (Fin.cases (v 3) (Fin.cases (indices) (Fin.cases (bound) (Fin.cases (fresh) (Fin.cases (v 12) (Fin.cases (v 17) (Fin.elim0))))))))))
  GroundSetTerm.app (M.definable_nonemptyTuple pairing 12)
    (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (meet) (Fin.cases (indices) (Fin.cases (spaces) (Fin.cases (relations) (Fin.cases (meets) (Fin.cases (anchors) (Fin.cases (embeddings) (Fin.cases (filters) (Fin.cases (separators) (Fin.cases (maps) (Fin.cases (action) (Fin.elim0))))))))))))))

theorem recursiveSuccessorTerm_eval (env : Fin 18 → ZFSet.{u}) :
    (M.recursiveSuccessorTerm pairing unions powers separation).eval env =
      RecursiveStateData.successorCodeFromEnvironment M env := by
  rfl

noncomputable def definable_recursiveSuccessorCode :
    GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M) :=
  (M.recursiveSuccessorTerm pairing unions powers separation).definition.congr
    (M.recursiveSuccessorTerm_eval pairing unions powers separation)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
noncomputable def compressionSuccessorFormula (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) : SetFormula 7 :=
  decodedSuccessorFormula (M.definable_recursiveSuccessorCode pairing unions powers separation).formula

end TransitiveGround

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    let φ := M.compressionSuccessorFormula pairing unions powers separation
    let params := extend state.data.code
      (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M (naturalStepFormula φ) params) ZFSet.omega history ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔
        y = (state.data.iterate M I Sources Reps G T n).code) ∧
      (∀ other, OrdinalRecursionTrace (groundRecursionStep M (naturalStepFormula φ) params)
        ZFSet.omega other → other = history) ∧
      ∀ n, ∃ current : GroundCompressionState M seed,
        current.data = state.data.iterate M I Sources Reps G T n := by
  dsimp only
  let φ := M.compressionSuccessorFormula pairing unions powers separation
  let params := extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hI (Fin.cases hSources (Fin.cases hReps (Fin.cases hG
      (Fin.cases hT (fun i => Fin.elim0 i)))))
  let value (n : Nat) := (state.data.iterate M I Sources Reps G T n).code
  have values : ∀ n, value n ∈ M.sets :=
    state.canonical_iterate_code_mem pairing unions powers separation hI hSources hReps hG hT
  have nextValue : ∀ n y, y ∈ M.sets →
      (Realize M.sets φ (extend (value n) (extend y params)) ↔ y = value (n + 1)) := by
    intro n y hy
    exact M.realize_recursiveSuccessorCode
      (M.definable_recursiveSuccessorCode pairing unions powers separation)
      (state.data.iterate M I Sources Reps G T n) (values n) hI hSources hReps hG hT hy
  obtain ⟨history, hh, trace, entries, unique⟩ :=
    M.exists_definableNaturalHistory φ params members value values nextValue
      pairing unions separation collection infinite
  exact ⟨history, hh, trace, entries, unique,
    state.canonical_iterate_valid pairing unions powers separation hI hSources hReps hG hT⟩

end GroundCompressionState
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ history ∈ M.sets, FunctionGraphOn ZFSet.omega history ∧
          (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔
            y = ((M.initialCompressionData P G r μ A Labels).iterate M I Sources Reps G T n).code) ∧
          ∀ n, ∃ current : GroundCompressionState M seed,
            current.data = (M.initialCompressionData P G r μ A Labels).iterate M I Sources Reps G T n := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, initial, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  obtain ⟨history, hh, trace, entries, _, valid⟩ := initial.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, seed, history, hh, trace.1, ?_, ?_⟩
  · simpa only [initialData] using entries
  · simpa only [initialData] using valid

end PartitionPilot.Forcing.TransitiveGround

end OAI
