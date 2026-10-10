import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowNameCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundIndexedGraphNameFamilies
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundOutsideRowNames
import OAI.SetTheory.PartitionPrinciple.Models.GroundOrdinalPartitionInjectionAssembly

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalRowTupleName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (δ : ZFSet.{u}) (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact Name.indexedTuple ⊤ δ (fun i => M.internalRowName s C hL (positions i))

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowTupleName_action (g : G) (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowTupleName s C hL δ positions) =
      M.internalRowTupleName s C hL δ (fun i => a.nonbottom.iso g (positions i)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (Name.indexedTuple ⊤ δ _) = Name.indexedTuple ⊤ δ _
  rw [Name.act_indexedTuple]
  apply congrArg (Name.indexedTuple ⊤ δ)
  funext i
  exact M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph g (positions i)

theorem internalRowTupleName_supported (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) (D : L)
    (bounded : ∀ i, (positions i).val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    a.principalFix D ≤ act.stabilizer c (M.internalRowTupleName s C hL δ positions) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c g fixed
  change act.act c g (M.internalRowTupleName s C hL δ positions) = _
  rw [M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph]
  apply congrArg (M.internalRowTupleName s C hL δ)
  funext i
  exact Subtype.ext (fixed (positions i).val (bounded i))

theorem internalRowTupleName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (δ : ZFSet.{u}) (positions : δ.toSet → {i : L // i ≠ ⊥}) (D : L)
    (bounded : ∀ i, (positions i).val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed)
      (M.internalRowTupleName s C hL δ positions) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  apply Name.indexedTuple_hs act (a.principalSupportFamily ⊥ directed) δ
    (fun i => M.internalRowName s C hL (positions i)) (a.principalFix D) ⟨D, le_rfl⟩
  · intro g fixed i
    rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
    apply congrArg (M.internalRowName s C hL)
    exact Subtype.ext (fixed (positions i).val (bounded i))
  · intro i
    exact M.internalRowName_hs a s b C pairing unions powers separation infinite
      hL hC hG graph directed (positions i)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) : ZFSet.{u} :=
  ZFSet.range (fun i : I => ZFSet.pair i.val (M.binaryRowName I C one i.val).val)

theorem mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) : z ∈ M.binaryRowNameGraph I C one ↔
      ∃ i ∈ I, z = ZFSet.pair i (M.binaryRowName I C one i).val := by
  rw [binaryRowNameGraph, ZFSet.mem_range]
  exact ⟨fun ⟨i, eq⟩ => ⟨i.val, i.property, eq.symm⟩,
    fun ⟨i, hi, eq⟩ => ⟨⟨i, hi⟩, eq.symm⟩⟩

theorem pair_mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i x : ZFSet.{u}) : ZFSet.pair i x ∈ M.binaryRowNameGraph I C one ↔
      i ∈ I ∧ x = (M.binaryRowName I C one i).val := by
  rw [M.mem_binaryRowNameGraph I C one]
  constructor
  · rintro ⟨j, hj, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem binaryRowNameGraph_function (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    FunctionGraphOn I (M.binaryRowNameGraph I C one) := by
  refine ⟨ZFSet.range (fun i : I => (M.binaryRowName I C one i.val).val), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := (M.mem_binaryRowNameGraph I C one z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hi, ZFSet.mem_range.2 ⟨⟨i, hi⟩, rfl⟩⟩
  · intro i hi
    refine ⟨(M.binaryRowName I C one i).val,
      (M.pair_mem_binaryRowNameGraph I C one i _).2 ⟨hi, rfl⟩, ?_⟩
    intro x hx
    exact ((M.pair_mem_binaryRowNameGraph I C one i x).1 hx).2

theorem binaryRowNameGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    M.binaryRowNameGraph I C one ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.exists_binaryRowName_bound pairing unions powers separation collection infinite hI hC one
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  let params := extend C (extend Q (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hC (Fin.cases hQ
    (Fin.cases (M.transitive hQ (SetMembers.raw_mem one))
      (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j))))
  have grounded := M.definableRelation_mem pairing unions powers separation binaryRowCodeFormula params members hI hW
  have equal : M.definableRelation binaryRowCodeFormula params I W = M.binaryRowNameGraph I C one := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨i, hi, x, hx, rfl, formula⟩ := (ZFSet.mem_sep.1 hz).2
      have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i x (M.transitive hI hi) (M.transitive hW hx)).1 formula
      exact (M.pair_mem_binaryRowNameGraph I C one i x).2 ⟨hi, eq⟩
    · intro hz
      obtain ⟨i, hi, rfl⟩ := (M.mem_binaryRowNameGraph I C one z).1 hz
      exact (M.pair_mem_definableRelation binaryRowCodeFormula params I W i _).2
        ⟨hi, bounds i hi, (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
          hI hC one i _ (M.transitive hI hi) (M.transitive hW (bounds i hi))).2 rfl⟩
  exact equal ▸ grounded

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def rowTupleCode (one mu I W rows f : ZFSet.{u}) : ZFSet.{u} :=
  indexedGraphNameCode one mu (relationCompose mu I W f rows)

noncomputable def rowTupleFamily (one mu I W rows S : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun f : S => f.val) (fun f => rowTupleCode one mu I W rows f.val)

theorem pair_mem_rowTupleFamily (one mu I W rows S f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ rowTupleFamily one mu I W rows S ↔
      f ∈ S ∧ z = rowTupleCode one mu I W rows f := by
  rw [rowTupleFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨g, eq⟩
    obtain ⟨input, output⟩ := ZFSet.pair_inj.1 eq
    exact ⟨input ▸ g.property, output.symm.trans (congrArg (rowTupleCode one mu I W rows) input)⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

theorem rowTupleFamily_function (one mu I W rows S : ZFSet.{u}) :
    FunctionGraphOn S (rowTupleFamily one mu I W rows S) := by
  have eq : ZFSet.range (fun f : S => f.val) = S := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_range]
    exact ⟨fun ⟨g, eq⟩ => eq ▸ g.property, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩
  have function := familyCodeGraph_function (fun f : S => f.val)
    (fun f => rowTupleCode one mu I W rows f.val) Subtype.val_injective
  simp only [eq] at function
  exact function

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

noncomputable def definable_rowTupleCode : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => rowTupleCode (env 1) (env 2) (env 3) (env 4) (env 5) (env 0)) := by
  let composed := (M.definable_relationCompose pairing unions powers separation).reindex
    (extend (2 : Fin 6) (extend 3 (extend 4 (extend 0 (extend 5 Fin.elim0)))))
  let inner (j : Fin 3) (env : Fin 6 → ZFSet.{u}) : ZFSet.{u} :=
    Fin.cases (env 1) (Fin.cases (env 2)
      (Fin.cases (relationCompose (env 2) (env 3) (env 4) (env 0) (env 5))
        (fun i => Fin.elim0 i))) j
  apply (M.definable_indexedGraphNameCode pairing unions powers separation collection).comp (g := inner)
  intro j
  refine Fin.cases (GroundDefinableFunction.projection M 1) (fun j => ?_) j
  refine Fin.cases (GroundDefinableFunction.projection M 2) (fun j => ?_) j
  exact Fin.cases composed (fun i => Fin.elim0 i) j

theorem rowTupleFamily_mem {one mu I W rows S : ZFSet.{u}}
    (hone : one ∈ M.sets) (hmu : mu ∈ M.sets) (hI : I ∈ M.sets)
    (hW : W ∈ M.sets) (hrows : rows ∈ M.sets) (hS : S ∈ M.sets) :
    rowTupleFamily one mu I W rows S ∈ M.sets :=
  (M.definable_rowTupleCode pairing unions powers separation collection).graph_mem pairing separation collection
    (extend one (extend mu (extend I (extend W (extend rows Fin.elim0)))))
    (Fin.cases hone (Fin.cases hmu (Fin.cases hI (Fin.cases hW
      (Fin.cases hrows (fun j => Fin.elim0 j)))))) hS

theorem binaryRowTupleFamily_mem (infinite : Realize M.sets infinity Fin.elim0)
    {L r I C mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    let rows := M.binaryRowNameGraph I C one
    rowTupleFamily (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows
      (M.rowPositionSequences L r I mu) ∈ M.sets := by
  have hrows := M.binaryRowNameGraph_mem pairing unions powers separation collection infinite hI hC one
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  exact M.rowTupleFamily_mem pairing unions powers separation collection
    (M.transitive hQ (SetMembers.raw_mem one)) hmu hI
    (M.union_mem unions (M.union_mem unions hrows)) hrows
    (M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu)

end TransitiveGround





namespace Name
theorem mem_indexedTuple_code {P : Type u} {s : Presentation P} (one : P)
    (δ : ZFSet.{u}) (names : δ.toSet → Name s) (z : ZFSet.{u}) :
    z ∈ (indexedTuple one δ names).val ↔ ∃ i : δ.toSet,
      z = ZFSet.pair (orderedPairNameCode (s.encode one) (check s one i.val).val (names i).val)
        (s.encode one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  simp only [orderedPair_code]
  exact exists_congr (fun _ => eq_comm)

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem binaryRowTupleCode_eq {I C mu δ f : ZFSet.{u}}
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (range : ∀ i, function.value i ∈ I) :
    let rows := M.binaryRowNameGraph I C one
    rowTupleCode (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows f =
      (Name.indexedTuple one δ (fun i => M.binaryRowName I C one (function.value i))).val := by
  dsimp only
  apply ZFSet.ext
  intro z
  rw [rowTupleCode, mem_indexedGraphNameCode, Name.mem_indexedTuple_code]
  constructor
  · rintro ⟨i, _, v, entry, equal⟩
    obtain ⟨_, _, x, hx, old, row⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have hi := function.pair_source old
    have value := function.value_eq_of_entry ⟨i, hi⟩ old
    have rowValue := ((M.pair_mem_binaryRowNameGraph I C one x v).1 row).2
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [Name.check_code_eq, value]
    exact rowValue ▸ equal
  · rintro ⟨i, equal⟩
    have row := (M.pair_mem_binaryRowNameGraph I C one (function.value i) _).2 ⟨range i, rfl⟩
    refine ⟨i.val, subset i.property, (M.binaryRowName I C one (function.value i)).val,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨subset i.property, pair_second_mem_doubleUnion row, function.value i, range i,
          function.value_entry i, row⟩, ?_⟩
    rwa [Name.check_code_eq] at equal

theorem internalRowTupleCode_eq {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (C : ZFSet.{u}) (hL : s.carrier ∈ M.sets)
    {mu δ f : ZFSet.{u}} (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (positions : δ.toSet → {i : L // i ≠ ⊥})
    (values : ∀ i, function.value i = s.encode (positions i).val) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    rowTupleCode (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows f = (M.internalRowTupleName s C hL δ positions).val := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier := by
    rw [values i]
    exact s.nonbottom.encode_mem (positions i)
  have eq := M.binaryRowTupleCode_eq (C := C) ⊤ function subset range
  dsimp only at eq
  have names : (fun i => M.binaryRowName s.nonbottom.carrier C ⊤ (function.value i)) =
      (fun i => M.internalRowName s C hL (positions i)) := by
    funext i
    rw [values i]
    rfl
  exact eq.trans (congrArg Subtype.val (congrArg (Name.indexedTuple ⊤ δ) names))

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def rowTupleTerms (one mu I W rows S : ZFSet.{u}) : ZFSet.{u} :=
  functionGraphRange S (rowTupleFamily one mu I W rows S)

theorem mem_rowTupleTerms (one mu I W rows S z : ZFSet.{u}) :
    z ∈ rowTupleTerms one mu I W rows S ↔
      ∃ f ∈ S, z = rowTupleCode one mu I W rows f := by
  rw [rowTupleTerms, mem_functionGraphRange]
  constructor
  · rintro ⟨f, hf, entry⟩
    exact ⟨f, hf, ((pair_mem_rowTupleFamily one mu I W rows S f z).1 entry).2⟩
  · rintro ⟨f, hf, equal⟩
    exact ⟨f, hf, (pair_mem_rowTupleFamily one mu I W rows S f z).2 ⟨hf, equal⟩⟩

theorem rowTupleTerms_function (one mu I W rows S : ZFSet.{u}) :
    ZFSet.IsFunc S (rowTupleTerms one mu I W rows S) (rowTupleFamily one mu I W rows S) :=
  functionGraphRange_function (rowTupleFamily_function one mu I W rows S)

theorem rowTupleTerms_surjective (one mu I W rows S : ZFSet.{u}) :
    ∀ z ∈ rowTupleTerms one mu I W rows S,
      ∃ f ∈ S, ZFSet.pair f z ∈ rowTupleFamily one mu I W rows S :=
  fun z hz => (mem_functionGraphRange S (rowTupleFamily one mu I W rows S) z).1 hz

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowTupleTerms_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {one mu I W rows S : ZFSet.{u}} (hS : S ∈ M.sets)
    (family : rowTupleFamily one mu I W rows S ∈ M.sets) :
    rowTupleTerms one mu I W rows S ∈ M.sets :=
  M.functionGraphRange_mem unions separation hS family

theorem rowTupleTerms_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one mu I W rows S K : ZFSet.{u}} (hS : S ∈ M.sets) (hK : K ∈ M.sets)
    (family : rowTupleFamily one mu I W rows S ∈ M.sets) (small : GroundBelow M S K) :
    GroundBelow M (rowTupleTerms one mu I W rows S) K :=
  small.function_image pairing unions powers separation choice hS
    (M.union_mem unions (M.union_mem unions family)) hK family
    (rowTupleFamily_function one mu I W rows S).to_isFunc

theorem binaryRowTupleTerms_mem_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L r I C mu K : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hmu : mu ∈ M.sets) (hK : K ∈ M.sets)
    (small : GroundBelow M (M.rowPositionSequences L r I mu) K)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    let S := M.rowPositionSequences L r I mu
    let rows := M.binaryRowNameGraph I C one
    let family := rowTupleFamily (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S
    let T := rowTupleTerms (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S
    family ∈ M.sets ∧ T ∈ M.sets ∧ ZFSet.IsFunc S T family ∧ GroundBelow M T K := by
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu
  have family := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite
    hL hr hI hC hmu one
  exact ⟨family, M.rowTupleTerms_mem unions separation hS family,
    rowTupleTerms_function _ _ _ _ _ _,
    M.rowTupleTerms_below pairing unions powers separation choice hS hK family small⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]

theorem internalRowTupleName_mem
    (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets)
    (delta f : ZFSet.{u}) (hDelta : delta ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn delta f) (positions : delta.toSet → {i : L // i ≠ ⊥})
    (values : ∀ i, function.value i = s.encode (positions i).val) :
    (M.internalRowTupleName s C hL delta positions).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let Q := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let rows := M.binaryRowNameGraph s.nonbottom.carrier C (⊤ : SetMembers Q)
  have nonbottom := M.nonbottom_carrier_mem s separation hL
  have carrier : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation nonbottom hC) (M.natSetCode_mem separation infinite 2)
  have topGround : SetMembers.raw (⊤ : SetMembers Q) ∈ M.sets :=
    M.transitive carrier (SetMembers.raw_mem ⊤)
  have rowGround : rows ∈ M.sets := M.binaryRowNameGraph_mem pairing unions powers separation collection
    infinite nonbottom hC ⊤
  have boundGround : (⋃₀ ⋃₀ rows) ∈ M.sets := M.union_mem unions (M.union_mem unions rowGround)
  have tupleGround : rowTupleCode (SetMembers.raw (⊤ : SetMembers Q)) delta s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows f ∈ M.sets :=
    (M.definable_rowTupleCode pairing unions powers separation collection).closed
      (extend f (extend (SetMembers.raw (⊤ : SetMembers Q)) (extend delta
        (extend s.nonbottom.carrier (extend (⋃₀ ⋃₀ rows) (extend rows Fin.elim0))))))
      (Fin.cases hf (Fin.cases topGround (Fin.cases hDelta (Fin.cases nonbottom
        (Fin.cases boundGround (Fin.cases rowGround (fun j => Fin.elim0 j)))))))
  have exactCode := M.internalRowTupleCode_eq s C hL (mu := delta) function
    (fun _ h => h) positions values
  dsimp only at exactCode
  exact exactCode ▸ tupleGround

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L) (C : ZFSet.{u})
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem exists_groundSupportTupleFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (order : b.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable b.nonbottom.carrier mu)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W →
      HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) tau) :
    letI := M.smallFunctionOrder (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨b.carrier, nodes⟩
    let rows := M.binaryRowNameGraph b.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences b.carrier b.conditionOrder b.nonbottom.carrier mu
    let T := rowTupleTerms (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu b.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∃ supportChoice ∈ M.sets, ∃ positionChoice ∈ M.sets, ∃ tupleChoice ∈ M.sets,
      ZFSet.IsFunc W b.carrier supportChoice ∧ ZFSet.IsFunc b.carrier S positionChoice ∧
      ZFSet.IsFunc W T tupleChoice ∧
      ∀ (tau : Name s) z, ZFSet.pair tau.val z ∈ tupleChoice →
        ∃ D : L, ∃ f ∈ S,
          ZFSet.pair tau.val (b.encode D) ∈ supportChoice ∧
          ZFSet.pair (b.encode D) f ∈ positionChoice ∧
          d.principalFix D ≤ a.stabilizer s tau ∧
          ∃ delta ∈ M.sets, ordinalSetProperty delta ∧ delta ⊆ mu ∧
          ∃ function : FunctionGraphOn delta f, ∃ positions : delta.toSet → {v : L // v ≠ ⊥},
            (∀ i, function.value i = b.encode (positions i).val) ∧
            (∀ i, (positions i).val ≤ D) ∧
            (∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v) ∧
            z = (M.internalRowTupleName b C nodes delta positions).val := by
  let := M.smallFunctionOrder (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨b.carrier, nodes⟩
  intro rows S T
  have hI := M.nonbottom_carrier_mem b separation nodes
  have hS := M.rowPositionSequences_mem pairing unions powers separation nodes order hI hmu
  let tuples := rowTupleFamily (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
    (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu b.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  have hTuples : tuples ∈ M.sets := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite
    nodes order hI hC hmu ⊤
  have hT : T ∈ M.sets := M.rowTupleTerms_mem unions separation hS hTuples
  have tupleFunction : ZFSet.IsFunc S T tuples := rowTupleTerms_function _ _ _ _ _ _
  obtain ⟨supportChoice, hSupport, supportFunction, supported⟩ := M.exists_groundNameSupportChoice
    a s t b d ⊥ directed pairing unions powers separation collection choice carrier group nodes
    supports maps W hW valid symmetric
  obtain ⟨positionChoice, hPosition, positionFunction, positionValues⟩ := M.exists_groundCoveringRowPositions
    b pairing unions powers separation choice nodes order mu hmu ordinal small
  let positionForName := relationCompose W b.carrier S supportChoice positionChoice
  have hPositionForName : positionForName ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW nodes hS hSupport hPosition
  have positionForNameFunction : ZFSet.IsFunc W S positionForName :=
    relationCompose_function_of_subset supportFunction positionFunction (fun _ h => h)
  let tupleChoice := relationCompose W S T positionForName tuples
  have hTupleChoice : tupleChoice ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW hS hT hPositionForName hTuples
  refine ⟨supportChoice, hSupport, positionChoice, hPosition, tupleChoice, hTupleChoice,
    supportFunction, positionFunction,
    relationCompose_function_of_subset positionForNameFunction tupleFunction (fun _ h => h), ?_⟩
  intro tau z entry
  obtain ⟨_, _, f, hf, namePosition, tupleEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
  obtain ⟨_, _, v, hv, supportEntry, positionEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 namePosition
  obtain ⟨D, rfl⟩ := (b.mem_carrier v).1 hv
  obtain ⟨_, delta, domain, function, bounds, onto⟩ := positionValues D f positionEntry
  have hDelta : delta ∈ M.sets := domain.elim (fun equal => equal.symm ▸ M.empty_mem ⟨mu, hmu⟩)
    (fun equal => equal.symm ▸ hmu)
  have deltaOrdinal : ordinalSetProperty delta := domain.elim
    (fun equal => equal.symm ▸ ordinalSetProperty_empty) (fun equal => equal.symm ▸ ordinal)
  have subset : delta ⊆ mu := domain.elim
    (fun equal => equal.symm ▸ ZFSet.empty_subset mu) (fun equal => equal.symm ▸ (fun _ h => h))
  have each (i : delta.toSet) : ∃ v : {v : L // v ≠ ⊥}, b.encode v.val = function.value i :=
    (b.nonbottom.mem_carrier _).1 (bounds i.val (function.value i) (function.value_entry i)).1
  let positions (i : delta.toSet) := Classical.choose (each i)
  have values (i : delta.toSet) : function.value i = b.encode (positions i).val :=
    (Classical.choose_spec (each i)).symm
  have bounded (i : delta.toSet) : (positions i).val ≤ D := by
    have bound := (bounds i.val (function.value i) (function.value_entry i)).2
    rw [values i] at bound
    exact (b.pair_mem_conditionOrder _ _).1 bound
  have covers (v : L) (hv : v ≠ ⊥) (below : v ≤ D) : ∃ i, (positions i).val = v := by
    obtain ⟨i, hi, entry⟩ := onto v hv below
    let j : delta.toSet := ⟨i, hi⟩
    refine ⟨j, b.injective ?_⟩
    exact (values j).symm.trans (function.value_eq_of_entry j entry)
  have code := ((pair_mem_rowTupleFamily _ _ _ _ _ _ f z).1 tupleEntry).2
  have exactTuple := M.internalRowTupleCode_eq b C nodes function subset positions values
  dsimp only at exactTuple
  exact ⟨D, f, hf, supportEntry, positionEntry, (supported tau D supportEntry).2,
    delta, hDelta, deltaOrdinal, subset, function, positions, values, bounded, covers,
    code.trans exactTuple⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
