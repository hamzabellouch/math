import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTemplateHeightRanges
import OAI.SetTheory.PartitionPrinciple.Geometry.TaggedGrowthLayerRanks
import OAI.SetTheory.PartitionPrinciple.Transfinite.NonzeroLimitOrdinalCodes

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization
universe u v

theorem familyCodeGraph_eq_of_entries {I : Type v} [Small.{u} I]
    {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (key value : I → ZFSet.{u}) (domain : ZFSet.range key = A)
    (entries : ∀ i, ZFSet.pair (key i) (value i) ∈ f) :
    familyCodeGraph key value = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph key value z).1 hz
    exact entries i
  · intro hz
    obtain ⟨x, hx, y, rfl⟩ := function.shape _ hz
    rw [← domain] at hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    have equal := function.unique (entries i) hz
    exact (mem_familyCodeGraph key value _).2 ⟨i, congrArg (ZFSet.pair (key i)) equal⟩

theorem familyCodeGraph_ground_of_entries {M : TransitiveGround.{u}}
    {I : Type v} [Small.{u} I] {A f : ZFSet.{u}} (ground : f ∈ M.sets)
    (function : FunctionGraphOn A f) (key value : I → ZFSet.{u})
    (domain : ZFSet.range key = A) (entries : ∀ i, ZFSet.pair (key i) (value i) ∈ f) :
    familyCodeGraph key value ∈ M.sets :=
  (familyCodeGraph_eq_of_entries function key value domain entries).symm ▸ ground

noncomputable def decodedFamilyValue {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (i : SetMembers A) : ZFSet.{u} :=
  function.value ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

theorem decodedFamilyValue_entry {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (i : SetMembers A) : ZFSet.pair (SetMembers.raw i) (decodedFamilyValue function i) ∈ f :=
  function.value_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

theorem decodedFamilyValue_eq {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (i : SetMembers A) {z : ZFSet.{u}} (entry : ZFSet.pair (SetMembers.raw i) z ∈ f) :
    decodedFamilyValue function i = z :=
  function.value_eq_of_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩ entry

theorem decodedFamilyValue_ground {M : TransitiveGround.{u}} {A f : ZFSet.{u}}
    (function : FunctionGraphOn A f) (ground : f ∈ M.sets) (i : SetMembers A) :
    decodedFamilyValue function i ∈ M.sets :=
  function.value_mem M ground ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

theorem decodedFamilyCodeGraph_eq {A f : ZFSet.{u}} (function : FunctionGraphOn A f) :
    familyCodeGraph (@SetMembers.raw A) (decodedFamilyValue function) = f :=
  familyCodeGraph_eq_of_entries function _ _ (ordinalMainIndex_key_range A)
    (decodedFamilyValue_entry function)

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem familyCodeGraph_pair_projections {I : Type v} [Small.{u} I]
    (key left right : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (whole : familyCodeGraph key (fun i => ZFSet.pair (left i) (right i)) ∈ M.sets) :
    familyCodeGraph key left ∈ M.sets ∧ familyCodeGraph key right ∈ M.sets := by
  let F := familyCodeGraph key (fun i => ZFSet.pair (left i) (right i))
  let V := ⋃₀ ⋃₀ F
  let B := ⋃₀ ⋃₀ V
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions whole)
  have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions hV)
  have bounds (i : I) : left i ∈ B ∧ right i ∈ B := by
    have entry : ZFSet.pair (left i) (right i) ∈ V :=
      pair_second_mem_doubleUnion ((pair_mem_familyCodeGraph key _ injective i _).2 rfl)
    exact ⟨pair_first_mem_doubleUnion entry, pair_second_mem_doubleUnion entry⟩
  have function : ZFSet.IsFunc (ZFSet.range key) (ZFSet.prod B B) F := by
    refine ⟨?_, (familyCodeGraph_isFunc key _ injective).2⟩
    intro z hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph key _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩,
      ZFSet.pair_mem_prod.2 (bounds i)⟩
  let first := relationCompose (ZFSet.range key) (ZFSet.prod B B) B F (productFirst B B)
  let second := relationCompose (ZFSet.range key) (ZFSet.prod B B) B F (productSecond B B)
  have firstGround : first ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    domain (M.prod_mem pairing unions powers separation hB hB) hB whole
      (M.productFirst_mem pairing unions powers separation hB hB)
  have secondGround : second ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    domain (M.prod_mem pairing unions powers separation hB hB) hB whole
      (M.productSecond_mem pairing unions powers separation hB hB)
  have firstFunction : FunctionGraphOn (ZFSet.range key) first := ⟨B,
    relationCompose_function_of_subset function (productFirst_function B B) (fun _ h => h)⟩
  have secondFunction : FunctionGraphOn (ZFSet.range key) second := ⟨B,
    relationCompose_function_of_subset function (productSecond_function B B) (fun _ h => h)⟩
  constructor
  · apply familyCodeGraph_ground_of_entries firstGround firstFunction key left rfl
    intro i
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, (bounds i).1, _, ZFSet.pair_mem_prod.2 (bounds i),
        (pair_mem_familyCodeGraph key _ injective i _).2 rfl,
        (mem_productFirst B B _).2 ⟨left i, (bounds i).1, right i, (bounds i).2, rfl⟩⟩
  · apply familyCodeGraph_ground_of_entries secondGround secondFunction key right rfl
    intro i
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, (bounds i).2, _, ZFSet.pair_mem_prod.2 (bounds i),
        (pair_mem_familyCodeGraph key _ injective i _).2 rfl,
        (mem_productSecond B B _).2 ⟨left i, (bounds i).1, right i, (bounds i).2, rfl⟩⟩

theorem familyCodeGraph_tuple_fields {I : Type v} [Small.{u} I]
    (key : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets) (k : Nat)
    (fields : I → Fin (k + 1) → ZFSet.{u})
    (whole : familyCodeGraph key (fun i => nonemptyTupleCode k (fields i)) ∈ M.sets) :
    ∀ j, familyCodeGraph key (fun i => fields i j) ∈ M.sets := by
  induction k with
  | zero => exact Fin.cases whole (fun j => Fin.elim0 j)
  | succ k ih =>
    have both := M.familyCodeGraph_pair_projections pairing unions powers separation key
      (fun i => fields i 0) (fun i => nonemptyTupleCode k (fun j => fields i j.succ))
      injective domain whole
    exact Fin.cases both.1 (ih (fun i j => fields i j.succ) both.2)

end TransitiveGround

theorem familyCodeGraph_rank_mono {I : Type v} [Small.{u} I]
    (key left right : I → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (left i) ≤ ZFSet.rank (right i)) :
    ZFSet.rank (familyCodeGraph key left) ≤ ZFSet.rank (familyCodeGraph key right) := by
  rw [familyCodeGraph, familyCodeGraph, ZFSet.rank_range, ZFSet.rank_range]
  apply Ordinal.iSup_le
  intro i
  have point : ZFSet.rank (ZFSet.pair (key i) (left i)) ≤
      ZFSet.rank (ZFSet.pair (key i) (right i)) := by
    change ZFSet.rank {{key i}, {key i, left i}} ≤ ZFSet.rank {{key i}, {key i, right i}}
    simp only [ZFSet.rank_pair, ZFSet.rank_singleton]
    exact max_le_max le_rfl (Order.succ_le_succ (max_le_max le_rfl (Order.succ_le_succ (bounds i))))
  exact (Order.succ_le_succ point).trans (Ordinal.le_iSup _ i)

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u v
variable {I : Type v} [Small.{u} I]

theorem TransitiveGround.familyCodeGraph_functionRanges_ground (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (key carriers graphs : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (carriersGround : familyCodeGraph key carriers ∈ M.sets)
    (graphsGround : familyCodeGraph key graphs ∈ M.sets) :
    familyCodeGraph key (fun i => functionGraphRange (carriers i) (graphs i)) ∈ M.sets := by
  let T := ZFSet.range key
  let As := familyCodeGraph key carriers
  let Fs := familyCodeGraph key graphs
  let V := ⋃₀ ⋃₀ Fs
  let B := ⋃₀ ⋃₀ ⋃₀ V
  let Bs := constantFamilyGraph T B
  let W := M.groundPower B
  let result := heightImageFamily T W As Bs Fs
  have hAs := M.union_mem unions (M.union_mem unions carriersGround)
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions graphsGround)
  have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions (M.union_mem unions hV))
  have hBs : Bs ∈ M.sets := M.constantFamilyGraph_mem pairing unions powers separation domain hB
  have hW : W ∈ M.sets := M.groundPower_mem powers hB
  have ground : result ∈ M.sets :=
    M.heightImageFamily_mem pairing unions powers separation domain hW carriersGround hBs graphsGround
  have aEntry (i : I) : ZFSet.pair (key i) (carriers i) ∈ As :=
    (pair_mem_familyCodeGraph key carriers injective i _).2 rfl
  have fEntry (i : I) : ZFSet.pair (key i) (graphs i) ∈ Fs :=
    (pair_mem_familyCodeGraph key graphs injective i _).2 rfl
  have bEntry (i : I) : ZFSet.pair (key i) B ∈ Bs :=
    (pair_mem_constantFamilyGraph T B _ _).2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, rfl⟩
  have valueBound (i : I) {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ graphs i) : y ∈ B := by
    have graphBound : graphs i ∈ V := pair_second_mem_doubleUnion (fEntry i)
    exact pair_second_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨graphs i, graphBound, entry⟩)
  have imageEqual (i : I) :
      functionGraphRange (carriers i) (graphs i) = relationImage (carriers i) B (graphs i) := by
    apply ZFSet.ext
    intro y
    rw [mem_functionGraphRange, mem_relationImage]
    exact ⟨fun h => ⟨valueBound i h.choose_spec.2, h⟩, And.right⟩
  have candidate (i : I) (R : ZFSet.{u}) : heightImageCandidate As Bs Fs (key i) R ↔
      R = functionGraphRange (carriers i) (graphs i) := by
    constructor
    · rintro ⟨A, _, B', _, f, _, ea, eb, ef, equal⟩
      have a := (pair_mem_familyCodeGraph key carriers injective i A).1 ea
      have b := ((pair_mem_constantFamilyGraph T B _ _).1 eb).2
      have f := (pair_mem_familyCodeGraph key graphs injective i f).1 ef
      simpa only [a, b, f, imageEqual i] using equal
    · intro equal
      exact ⟨carriers i, pair_second_mem_doubleUnion (aEntry i),
        B, pair_second_mem_doubleUnion (bEntry i), graphs i, pair_second_mem_doubleUnion (fEntry i),
        aEntry i, bEntry i, fEntry i, equal.trans (imageEqual i)⟩
  have rangeBound (i : I) : functionGraphRange (carriers i) (graphs i) ∈ W := by
    apply (M.mem_groundPower B _).2
    refine ⟨M.functionGraphRange_mem unions separation
      (M.transitive hAs (pair_second_mem_doubleUnion (aEntry i)))
      (M.transitive hV (pair_second_mem_doubleUnion (fEntry i))), ?_⟩
    intro y hy
    obtain ⟨x, _, entry⟩ := (mem_functionGraphRange _ _ y).1 hy
    exact valueBound i entry
  have entries (i : I) (R : ZFSet.{u}) : ZFSet.pair (key i) R ∈ result ↔
      R = functionGraphRange (carriers i) (graphs i) := by
    rw [pair_mem_heightImageFamily, candidate]
    exact ⟨fun h => h.2.2, fun equal =>
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, equal.symm ▸ rangeBound i, equal⟩⟩
  have function : FunctionGraphOn T result := by
    refine ⟨W, fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ⟨functionGraphRange (carriers i) (graphs i), (entries i _).2 rfl,
      fun R entry => (entries i R).1 entry⟩
  exact familyCodeGraph_ground_of_entries ground function key _ rfl (fun i => (entries i _).2 rfl)

theorem familyCodeGraph_functionRanges_rank_le (key carriers graphs : I → ZFSet.{u}) :
    ZFSet.rank (familyCodeGraph key (fun i => functionGraphRange (carriers i) (graphs i))) ≤
      ZFSet.rank (familyCodeGraph key graphs) :=
  familyCodeGraph_rank_mono key _ graphs (fun i => functionGraphRange_rank_le (carriers i) (graphs i))

end PartitionPilot.Forcing

end OAI
