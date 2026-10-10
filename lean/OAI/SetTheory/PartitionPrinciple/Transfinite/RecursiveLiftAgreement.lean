import OAI.SetTheory.PartitionPrinciple.Definability.CodedBatchDecoding
import OAI.SetTheory.PartitionPrinciple.Definability.GroundPushFilterFamilyFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundVaryingFamilyEvaluation
import OAI.SetTheory.PartitionPrinciple.Geometry.DecodedMeetMaps
import OAI.SetTheory.PartitionPrinciple.Geometry.LiftedCompressionFunctions

namespace OAI


namespace PartitionPilot.Forcing

universe u

def recursiveAttachmentIndices (I J P U As Fs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun k => ∃ i ∈ I, ∃ j ∈ J, ∃ a ∈ P, ∃ F ∈ U,
    k = ZFSet.pair i j ∧ ZFSet.pair i a ∈ As ∧ ZFSet.pair j F ∈ Fs ∧ a ∉ F)
    (ZFSet.prod I J)

theorem recursiveAttachmentIndices_subset (I J P U As Fs : ZFSet.{u}) :
    recursiveAttachmentIndices I J P U As Fs ⊆ ZFSet.prod I J :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_recursiveAttachmentIndices (I J P U As Fs i j : ZFSet.{u}) :
    ZFSet.pair i j ∈ recursiveAttachmentIndices I J P U As Fs ↔
      i ∈ I ∧ j ∈ J ∧ ∃ a ∈ P, ∃ F ∈ U,
        ZFSet.pair i a ∈ As ∧ ZFSet.pair j F ∈ Fs ∧ a ∉ F := by
  rw [recursiveAttachmentIndices, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hj⟩, i', _, j', _, a, ha, F, hF, eq, ai, Fj, neg⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, hj, a, ha, F, hF, ai, Fj, neg⟩
  · rintro ⟨hi, hj, a, ha, F, hF, ai, Fj, neg⟩
    exact ⟨⟨hi, hj⟩, i, hi, j, hj, a, ha, F, hF, rfl, ai, Fj, neg⟩

def pairFieldGraph (left : Bool) (I J K B H : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ k ∈ K, ∃ i ∈ I, ∃ j ∈ J, ∃ x ∈ B,
    z = ZFSet.pair k x ∧ k = ZFSet.pair i j ∧
      ZFSet.pair (if left then i else j) x ∈ H) (ZFSet.prod K B)

theorem pair_mem_pairFieldGraph (left : Bool) (I J K B H k x : ZFSet.{u}) :
    ZFSet.pair k x ∈ pairFieldGraph left I J K B H ↔
      k ∈ K ∧ x ∈ B ∧ ∃ i ∈ I, ∃ j ∈ J,
        k = ZFSet.pair i j ∧ ZFSet.pair (if left then i else j) x ∈ H := by
  rw [pairFieldGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hk, hx⟩, k', _, i, hi, j, hj, x', _, eq, kij, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hk, hx, i, hi, j, hj, kij, entry⟩
  · rintro ⟨hk, hx, i, hi, j, hj, kij, entry⟩
    exact ⟨⟨hk, hx⟩, k, hk, i, hi, j, hj, x, hx, rfl, kij, entry⟩

theorem pairFieldGraph_entry_iff (left : Bool) {I J K B H i j x : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) x ∈ pairFieldGraph left I J K B H ↔
      ZFSet.pair i j ∈ K ∧ x ∈ B ∧ ZFSet.pair (if left then i else j) x ∈ H := by
  rw [pair_mem_pairFieldGraph]
  constructor
  · rintro ⟨hk, hx, i', _, j', _, eq, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hk, hx, entry⟩
  · rintro ⟨hk, hx, entry⟩
    exact ⟨hk, hx, i, hi, j, hj, rfl, entry⟩

theorem pairFieldGraph_function (left : Bool) {I J K B H : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J)
    (function : ZFSet.IsFunc (if left then I else J) B H) :
    ZFSet.IsFunc K B (pairFieldGraph left I J K B H) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  have hs : (if left then i else j) ∈ (if left then I else J) := by
    cases left <;> assumption
  obtain ⟨x, entry, unique⟩ := function.2 _ hs
  have hx := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  refine ⟨x, (pairFieldGraph_entry_iff left hi hj).2 ⟨hk, hx, entry⟩, ?_⟩
  intro y hy
  exact unique y ((pairFieldGraph_entry_iff left hi hj).1 hy).2.2






namespace BoundedFormula

open SetFormula

def recursiveAttachmentIndexFormula {n} (k i j p u a f : Fin n) : BoundedFormula n :=
  exMem i (exMem j.succ (exMem p.succ.succ (exMem u.succ.succ.succ
    (.conj (orderedPairFormula k.succ.succ.succ.succ 3 2)
      (.conj (pairMembershipFormula 3 1 a.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 2 0 f.succ.succ.succ.succ) (.neg (.mem 1 0))))))))

theorem truth_recursiveAttachmentIndexFormula {n} (k i j p u a f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (recursiveAttachmentIndexFormula k i j p u a f) env ↔
      ∃ x ∈ env i, ∃ y ∈ env j, ∃ b ∈ env p, ∃ F ∈ env u,
        env k = ZFSet.pair x y ∧ ZFSet.pair x b ∈ env a ∧
          ZFSet.pair y F ∈ env f ∧ b ∉ F := by
  simp only [recursiveAttachmentIndexFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

def pairFieldEntryFormula {n} (left : Bool) (z k i j b h : Fin n) : BoundedFormula n :=
  exMem k (exMem i.succ (exMem j.succ.succ (exMem b.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 0)
      (.conj (orderedPairFormula 3 2 1)
        (pairMembershipFormula (if left then 2 else 1) 0 h.succ.succ.succ.succ))))))

theorem truth_pairFieldEntryFormula {n} (left : Bool) (z k i j b h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairFieldEntryFormula left z k i j b h) env ↔
      ∃ t ∈ env k, ∃ x ∈ env i, ∃ y ∈ env j, ∃ v ∈ env b,
        env z = ZFSet.pair t v ∧ t = ZFSet.pair x y ∧
          ZFSet.pair (if left then x else y) v ∈ env h := by
  cases left <;>
    simp only [pairFieldEntryFormula, truth_exMem, Truth,
      truth_orderedPairFormula, truth_pairMembershipFormula, Bool.false_eq_true, ↓reduceIte] <;> rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem recursiveAttachmentIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J P U As Fs : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hP : P ∈ M.sets) (hU : U ∈ M.sets) (hAs : As ∈ M.sets) (hFs : Fs ∈ M.sets) :
    recursiveAttachmentIndices I J P U As Fs ∈ M.sets := by
  let params := extend I (extend J (extend P (extend U (extend As (extend Fs Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.recursiveAttachmentIndexFormula 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hJ (Fin.cases hP (Fin.cases hU (Fin.cases hAs
      (Fin.cases hFs (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hI hJ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.recursiveAttachmentIndexFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod I J) = recursiveAttachmentIndices I J P U As Fs := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, recursiveAttachmentIndices, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_recursiveAttachmentIndexFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem pairFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (left : Bool) {I J K B H : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hK : K ∈ M.sets) (hB : B ∈ M.sets) (hH : H ∈ M.sets) :
    pairFieldGraph left I J K B H ∈ M.sets := by
  let params := extend K (extend I (extend J (extend B (extend H Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairFieldEntryFormula left 0 1 2 3 4 5) params
    (Fin.cases hK (Fin.cases hI (Fin.cases hJ (Fin.cases hB
      (Fin.cases hH (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hK hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairFieldEntryFormula left 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod K B) = pairFieldGraph left I J K B H := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, pairFieldGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairFieldEntryFormula left 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem pairFieldGraph_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (left : Bool) {I J K H : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hK : K ∈ M.sets) (hH : H ∈ M.sets) (subset : K ⊆ ZFSet.prod I J)
    (function : FunctionGraphOn (if left then I else J) H) :
    pairFieldGraph left I J K (ZFSet.sUnion (ZFSet.sUnion H)) H ∈ M.sets ∧
      FunctionGraphOn K (pairFieldGraph left I J K (ZFSet.sUnion (ZFSet.sUnion H)) H) ∧
      ∀ i ∈ I, ∀ j ∈ J, ∀ x,
        ZFSet.pair (ZFSet.pair i j) x ∈ pairFieldGraph left I J K (ZFSet.sUnion (ZFSet.sUnion H)) H ↔
          ZFSet.pair i j ∈ K ∧ ZFSet.pair (if left then i else j) x ∈ H := by
  refine ⟨M.pairFieldGraph_mem pairing unions powers separation left hI hJ hK
    (M.union_mem unions (M.union_mem unions hH)) hH,
    ⟨_, pairFieldGraph_function left subset function.to_isFunc⟩, ?_⟩
  intro i hi j hj x
  rw [pairFieldGraph_entry_iff left hi hj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, pair_second_mem_doubleUnion h.2, h.2⟩⟩

end TransitiveGround






def pairSecondField (I J K H : ZFSet.{u}) : ZFSet.{u} :=
  pairFieldGraph false I J K (ZFSet.sUnion (ZFSet.sUnion H)) H

def pairFirstField (I J K H : ZFSet.{u}) : ZFSet.{u} :=
  pairFieldGraph true I J K (ZFSet.sUnion (ZFSet.sUnion H)) H

def recursiveSeparatorFamily (K I J D L Maps Ss : ZFSet.{u}) : ZFSet.{u} :=
  familyEvaluationGraph K D L (ZFSet.sUnion (ZFSet.sUnion Maps))
    (pairFirstField I J K Maps) (pairFieldGraph false I J K D Ss)

theorem pairSecondField_entry_iff {I J K H i j x : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) x ∈ pairSecondField I J K H ↔
      ZFSet.pair i j ∈ K ∧ ZFSet.pair j x ∈ H := by
  rw [pairSecondField, pairFieldGraph_entry_iff false hi hj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, pair_second_mem_doubleUnion h.2, h.2⟩⟩

theorem pairFirstField_entry_iff {I J K H i j x : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) x ∈ pairFirstField I J K H ↔
      ZFSet.pair i j ∈ K ∧ ZFSet.pair i x ∈ H := by
  rw [pairFirstField, pairFieldGraph_entry_iff true hi hj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, pair_second_mem_doubleUnion h.2, h.2⟩⟩

theorem AttachmentBatchInputs.separator_function
    {D rD μD J Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss) : ZFSet.IsFunc J D Ss := by
  refine ⟨?_, d.separators.to_isFunc.2⟩
  intro z hz
  obtain ⟨j, hj, e, rfl⟩ := d.separators.shape z hz
  have equal := d.separators.value_eq_of_entry ⟨j, hj⟩ hz
  exact ZFSet.pair_mem_prod.2 ⟨hj, equal ▸ (d.fiber ⟨j, hj⟩).separator_mem⟩

theorem recursiveSeparatorFamily_function {K I J D L Maps Ss : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J) (maps : FunctionGraphOn I Maps)
    (separators : ZFSet.IsFunc J D Ss)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → ZFSet.IsFunc D L S) :
    ZFSet.IsFunc K L (recursiveSeparatorFamily K I J D L Maps Ss) := by
  apply familyEvaluationGraph_function (pairFieldGraph_function true subset maps.to_isFunc)
    (pairFieldGraph_function false subset separators)
  intro k S entry
  obtain ⟨_, _, i, hi, j, hj, rfl, selected⟩ := (pair_mem_pairFieldGraph true _ _ _ _ _ _ _).1 entry
  exact valid i S selected

theorem recursiveSeparatorFamily_entry_iff {K I J D L Maps Ss i j S e y : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J) (maps : FunctionGraphOn I Maps)
    (separators : ZFSet.IsFunc J D Ss) (hk : ZFSet.pair i j ∈ K)
    (mapEntry : ZFSet.pair i S ∈ Maps) (sepEntry : ZFSet.pair j e ∈ Ss) :
    ZFSet.pair (ZFSet.pair i j) y ∈ recursiveSeparatorFamily K I J D L Maps Ss ↔
      y ∈ L ∧ ZFSet.pair e y ∈ S := by
  have shape := ZFSet.pair_mem_prod.1 (subset hk)
  exact familyEvaluationGraph_entry_iff
    (pairFieldGraph_function true subset maps.to_isFunc)
    (pairFieldGraph_function false subset separators)
    ((pairFirstField_entry_iff shape.1 shape.2).2 ⟨hk, mapEntry⟩)
    ((pairFieldGraph_entry_iff false shape.1 shape.2).2
      ⟨hk, (ZFSet.pair_mem_prod.1 (separators.1 sepEntry)).2, sepEntry⟩)

theorem recursiveAttachmentIndices_entry_iff {I J D U Sources Fs i j a F : ZFSet.{u}}
    (sources : ZFSet.IsFunc I D Sources) (filters : ZFSet.IsFunc J U Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs) :
    ZFSet.pair i j ∈ recursiveAttachmentIndices I J D U Sources Fs ↔ a ∉ F := by
  rw [pair_mem_recursiveAttachmentIndices]
  constructor
  · rintro ⟨_, _, b, _, V, _, ib, jV, negative⟩
    have equalA := (show FunctionGraphOn I Sources from ⟨D, sources⟩).unique ib source
    have equalF := (show FunctionGraphOn J Fs from ⟨U, filters⟩).unique jV filter
    exact equalA ▸ equalF ▸ negative
  · intro negative
    have sa := ZFSet.pair_mem_prod.1 (sources.1 source)
    have sf := ZFSet.pair_mem_prod.1 (filters.1 filter)
    exact ⟨sa.1, sf.1, a, sa.2, F, sf.2, source, filter, negative⟩






theorem recursiveFresh_iff {I J K Qs rs As i j q : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) q ∈ indexedAttachmentFresh K
      (pairSecondField I J K Qs) (pairSecondField I J K rs) (pairSecondField I J K As) ↔
      ZFSet.pair i j ∈ K ∧ ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As := by
  rw [pair_mem_indexedAttachmentFresh, pair_mem_indexedAttachmentFresh]
  constructor
  · rintro ⟨hk, Q, r, a, eq, er, ea, hq, fresh⟩
    exact ⟨hk, hj, Q, r, a, ((pairSecondField_entry_iff hi hj).1 eq).2,
      ((pairSecondField_entry_iff hi hj).1 er).2,
      ((pairSecondField_entry_iff hi hj).1 ea).2, hq, fresh⟩
  · rintro ⟨hk, _, Q, r, a, eq, er, ea, hq, fresh⟩
    exact ⟨hk, Q, r, a, (pairSecondField_entry_iff hi hj).2 ⟨hk, eq⟩,
      (pairSecondField_entry_iff hi hj).2 ⟨hk, er⟩,
      (pairSecondField_entry_iff hi hj).2 ⟨hk, ea⟩, hq, fresh⟩

theorem recursiveFresh_shape {I J K Qs rs As z : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J)
    (fresh : z ∈ indexedAttachmentFresh K
      (pairSecondField I J K Qs) (pairSecondField I J K rs) (pairSecondField I J K As)) :
    ∃ i ∈ I, ∃ j ∈ J, ∃ q, z = ZFSet.pair (ZFSet.pair i j) q ∧
      ZFSet.pair i j ∈ K ∧ ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As := by
  obtain ⟨k, hk, q, rfl, _⟩ := (mem_indexedAttachmentFresh _ _ _ _ z).1 fresh
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  exact ⟨i, hi, j, hj, q, rfl, (recursiveFresh_iff hi hj).1 fresh⟩

theorem negativeRecursiveFresh_mem
    {I J D L Qs rs As Sources Fs i j q a F : ZFSet.{u}}
    (sources : ZFSet.IsFunc I D Sources) (filters : FunctionGraphOn J Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (fresh : ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As) (negative : a ∉ F) :
    let K := recursiveAttachmentIndices I J D (ZFSet.sUnion (ZFSet.sUnion Fs)) Sources Fs
    ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q) ∈ taggedExtension L
      (indexedAttachmentFresh K (pairSecondField I J K Qs)
        (pairSecondField I J K rs) (pairSecondField I J K As)) := by
  apply pair_mem_taggedExtension.2
  apply (recursiveFresh_iff (ZFSet.pair_mem_prod.1 (sources.1 source)).1 (filters.pair_source filter)).2
  exact ⟨(recursiveAttachmentIndices_entry_iff sources filters.to_isFunc source filter).2 negative, fresh⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem recursiveSeparatorFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J D L Maps Ss : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hL : L ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSs : Ss ∈ M.sets) :
    recursiveSeparatorFamily K I J D L Maps Ss ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions hMaps)
  exact M.familyEvaluationGraph_mem pairing unions powers separation hK hD hL bound
    (M.pairFieldGraph_mem pairing unions powers separation true hI hJ hK bound hMaps)
    (M.pairFieldGraph_mem pairing unions powers separation false hI hJ hK hD hSs)

theorem groundRecursiveBatchInputs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J D L rD rL μD μL Qs rs μs As Es Fs Ss Maps : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)
    (target : MeetOrderCode L rL μL) (maps : FunctionGraphOn I Maps)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → MeetEmbeddingCode D L rD rL μD μL S)
    (subset : K ⊆ ZFSet.prod I J)
    (hK : K ∈ M.sets) (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hD : D ∈ M.sets) (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hMaps : Maps ∈ M.sets) :
    AttachmentBatchInputs L rL μL K
      (pairSecondField I J K Qs) (pairSecondField I J K rs)
      (pairSecondField I J K μs) (pairSecondField I J K As)
      (M.groundPairCompositions K I J (familyPointBound Qs) D L Es Maps)
      (M.groundPairPushFilters K I J L rL Maps Fs)
      (recursiveSeparatorFamily K I J D L Maps Ss) := by
  obtain ⟨_, composites, compositeEntries⟩ := M.groundPairCompositions_spec
    pairing unions powers separation hK hI hJ (M.familyPointBound_mem unions hQs)
    hD hL hEs hMaps d.embeddings maps subset
  obtain ⟨_, filters, filterEntries⟩ := M.groundPairPushFilters_spec
    pairing unions powers separation hK hI hJ hL hrL hMaps hFs maps d.filters subset
  refine ⟨target, ⟨_, pairFieldGraph_function false subset d.spaces.to_isFunc⟩,
    ⟨_, pairFieldGraph_function false subset d.relations.to_isFunc⟩,
    ⟨_, pairFieldGraph_function false subset d.meets.to_isFunc⟩,
    ⟨_, pairFieldGraph_function false subset d.anchors.to_isFunc⟩,
    ⟨_, composites⟩, ⟨_, filters⟩,
    ⟨_, recursiveSeparatorFamily_function subset maps d.separator_function
      (fun i S entry => (valid i S entry).injection.function)⟩, ?_⟩
  intro k hk Q r μ a ell' F' e' qEntry rEntry μEntry aEntry ellEntry FEntry eEntry
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  have qOriginal := ((pairSecondField_entry_iff hi hj).1 qEntry).2
  have rOriginal := ((pairSecondField_entry_iff hi hj).1 rEntry).2
  have μOriginal := ((pairSecondField_entry_iff hi hj).1 μEntry).2
  have aOriginal := ((pairSecondField_entry_iff hi hj).1 aEntry).2
  obtain ⟨ell, oldEll⟩ := d.embeddings.total hj
  obtain ⟨F, oldF⟩ := d.filters.total hj
  obtain ⟨e, oldE⟩ := d.separators.total hj
  obtain ⟨S, oldS⟩ := maps.total hi
  have old := d.valid j hj Q r μ a ell F e qOriginal rOriginal μOriginal aOriginal oldEll oldF oldE
  have ellEq := ((compositeEntries i j ell S ell' oldEll oldS).1 ellEntry).2
  have filterEq := ((filterEntries i j S F F' oldS oldF).1 FEntry).2
  have image := ((recursiveSeparatorFamily_entry_iff subset maps d.separator_function hk oldS oldE).1 eEntry).2
  have domainEq : relationCompose (familyPointBound Qs) D L ell S =
      relationCompose (attachmentIdeal Q r a) D L ell S :=
    relationCompose_domain_eq
      (fun _ hz => mem_familyPointBound_of_entry qOriginal ((mem_attachmentIdeal Q r a _).1 hz).1)
      old.base_function.1
  rw [ellEq, domainEq, filterEq]
  exact old.pushforward target (valid i S oldS) image

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

structure CodedRecursiveMapInputs
    {D rD μD J Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)
    (I Maps Sources Reps G m inv one A : ZFSet.{u}) : Prop where
  maps : FunctionGraphOn I Maps
  sources : ZFSet.IsFunc I D Sources
  representatives : ZFSet.IsFunc I G Reps
  group : GroupCode G m inv one
  action : PosetActionCode G d.batchCarrier m one d.batchOrder A
  valid : ∀ i S, ZFSet.pair i S ∈ Maps →
    MeetEmbeddingCode D d.batchCarrier rD d.batchOrder μD d.batchMeetGraph S
  agreement : ∀ i a g S x y, ZFSet.pair i a ∈ Sources → ZFSet.pair i g ∈ Reps →
    ZFSet.pair i S ∈ Maps → x ∈ D → ZFSet.pair x a ∈ rD →
      (ZFSet.pair x y ∈ S ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A)

namespace CodedRecursiveMapInputs

variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

noncomputable def source (i : {i : ZFSet.{u} // i ∈ I}) : {x : ZFSet.{u} // x ∈ D} :=
  let graph : FunctionGraphOn I Sources := ⟨D, h.sources⟩
  ⟨graph.value i, (ZFSet.pair_mem_prod.1 (h.sources.1 (graph.value_entry i))).2⟩

theorem source_entry (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair i.val (h.source i).val ∈ Sources :=
  (show FunctionGraphOn I Sources from ⟨D, h.sources⟩).value_entry i

noncomputable def actor (i : {i : ZFSet.{u} // i ∈ I}) : {g : ZFSet.{u} // g ∈ G} :=
  let graph : FunctionGraphOn I Reps := ⟨G, h.representatives⟩
  ⟨graph.value i, (ZFSet.pair_mem_prod.1 (h.representatives.1 (graph.value_entry i))).2⟩

theorem actor_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (h.actor i).val ∈ Reps :=
  (show FunctionGraphOn I Reps from ⟨G, h.representatives⟩).value_entry i

noncomputable def previous (i : {i : ZFSet.{u} // i ∈ I}) :
    MeetEmbedding d.oldOrder.toMeetOrder d.templates.extension :=
  compose ((h.valid i.val _ (h.maps.value_entry i)).toMeetEmbedding d.oldOrder d.batch_meetOrder)
    d.coding.decodingIso.toMeetEmbedding

theorem previous_entry (i : {i : ZFSet.{u} // i ∈ I}) (x : {x : ZFSet.{u} // x ∈ D}) :
    ZFSet.pair x.val (d.coding.encode ((h.previous i).toFun x)) ∈ h.maps.value i := by
  change ZFSet.pair x.val (d.coding.encode (d.coding.decodingIso.toFun
    (((h.valid i.val _ (h.maps.value_entry i)).toMeetEmbedding d.oldOrder d.batch_meetOrder).toFun x))) ∈ _
  rw [d.coding.decodingIso_encode]
  exact (h.valid i.val _ (h.maps.value_entry i)).toMeetEmbedding_entry d.oldOrder d.batch_meetOrder x

noncomputable def representative (i : {i : ZFSet.{u} // i ∈ I}) :
    Compression.MeetIso d.templates.extension d.templates.extension := by
  let encoding := d.coding.encodingIso
  let acted := h.action.toMeetIso h.group d.batch_meetOrder (h.actor i)
  refine isoOfOrder
    (fun x => encoding.inverse (acted.toFun (encoding.toFun x)))
    (fun x => encoding.inverse (acted.inverse (encoding.toFun x))) ?_ ?_ ?_
  · intro x
    rw [encoding.right_inverse, acted.left_inverse, encoding.left_inverse]
  · intro x
    rw [encoding.right_inverse, acted.right_inverse, encoding.left_inverse]
  · intro x y
    exact ((inverseIso encoding).le_iff _ _).trans
      ((acted.le_iff _ _).trans (encoding.le_iff x y))

theorem representative_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair (h.actor i).val (d.coding.encode x))
      (d.coding.encode ((h.representative i).toFun x)) ∈ A := by
  change ZFSet.pair (ZFSet.pair (h.actor i).val (d.coding.encode x))
    (d.coding.encode (d.coding.decode
      ((h.action.toMeetIso h.group d.batch_meetOrder (h.actor i)).toFun
        ⟨d.coding.encode x, d.coding.encode_mem x⟩))) ∈ A
  rw [d.coding.encode_decode]
  exact h.action.toMeetIso_entry h.group d.batch_meetOrder (h.actor i)
    ⟨d.coding.encode x, d.coding.encode_mem x⟩

noncomputable def toInputs : Inputs d.templates {i : ZFSet.{u} // i ∈ I} where
  source := h.source
  previous := h.previous
  representative := h.representative
  agree := by
    intro i x lower
    apply d.coding.encode_injective
    have previous := (h.agreement i.val (h.source i).val (h.actor i).val (h.maps.value i)
      x.val _ (h.source_entry i) (h.actor_entry i) (h.maps.value_entry i) x.property lower).1
        (h.previous_entry i x)
    exact (show FunctionGraphOn (ZFSet.prod G d.batchCarrier) A from
      ⟨d.batchCarrier, h.action.function⟩).unique previous (h.representative_entry i (.inl x))

theorem toInputs_source (i : {i : ZFSet.{u} // i ∈ I}) : h.toInputs.source i = h.source i := rfl

theorem toInputs_previous_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D}) :
    ZFSet.pair x.val (d.coding.encode ((h.toInputs.previous i).toFun x)) ∈ h.maps.value i :=
  h.previous_entry i x

theorem toInputs_representative_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair (h.actor i).val (d.coding.encode x))
      (d.coding.encode ((h.toInputs.representative i).toFun x)) ∈ A :=
  h.representative_entry i x

end CodedRecursiveMapInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open Compression.RecursiveMaps
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

noncomputable abbrev nextIndices (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) :=
  recursiveAttachmentIndices I J D (ZFSet.sUnion (ZFSet.sUnion Fs)) Sources Fs

noncomputable abbrev NextInputs (M : TransitiveGround.{u}) :=
  AttachmentBatchInputs d.batchCarrier d.batchOrder d.batchMeetGraph h.nextIndices
    (pairSecondField I J h.nextIndices Qs) (pairSecondField I J h.nextIndices rs)
    (pairSecondField I J h.nextIndices μs) (pairSecondField I J h.nextIndices As)
    (M.groundPairCompositions h.nextIndices I J (familyPointBound Qs) D d.batchCarrier Es Maps)
    (M.groundPairPushFilters h.nextIndices I J d.batchCarrier d.batchOrder Maps Fs)
    (recursiveSeparatorFamily h.nextIndices I J D d.batchCarrier Maps Ss)

noncomputable def nextIndex (label : h.toInputs.Labels) :
    {k : ZFSet.{u} // k ∈ h.nextIndices} :=
  ⟨ZFSet.pair label.1.val label.2.val.val,
    (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
      (h.source_entry label.1) (d.filter_entry label.2.val)).2 label.2.property⟩

theorem nextIndex_injective : Function.Injective h.nextIndex := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ equal
  have parts := ZFSet.pair_inj.1 (congrArg Subtype.val equal)
  have left : i = i' := Subtype.ext parts.1
  subst i'
  have right : j = j' := Subtype.ext (Subtype.ext parts.2)
  subst j'
  rfl

theorem nextIndex_surjective : Function.Surjective h.nextIndex := by
  intro k
  obtain ⟨i, hi, j, hj, equal⟩ := ZFSet.mem_prod.1
    (recursiveAttachmentIndices_subset I J D (ZFSet.sUnion (ZFSet.sUnion Fs)) Sources Fs k.property)
  let i' : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  let j' : {j : ZFSet.{u} // j ∈ J} := ⟨j, hj⟩
  have negative : ¬ d.templates.upper j' (h.toInputs.source i') :=
    (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
      (h.source_entry i') (d.filter_entry j')).1 (equal ▸ k.property)
  exact ⟨⟨i', ⟨j', negative⟩⟩, Subtype.ext equal.symm⟩

variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem next_space (label : h.toInputs.Labels) :
    next.space (h.nextIndex label) = d.space label.2.val :=
  d.spaces.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.space_entry (h.nextIndex label))).2 (d.space_entry label.2.val)

theorem next_rel (label : h.toInputs.Labels) :
    next.rel (h.nextIndex label) = d.rel label.2.val :=
  d.relations.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.rel_entry (h.nextIndex label))).2 (d.rel_entry label.2.val)

theorem next_meet (label : h.toInputs.Labels) :
    next.meet (h.nextIndex label) = d.meet label.2.val :=
  d.meets.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.meet_entry (h.nextIndex label))).2 (d.meet_entry label.2.val)

theorem next_anchor (label : h.toInputs.Labels) :
    next.anchor (h.nextIndex label) = d.anchor label.2.val :=
  d.anchors.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.anchor_entry (h.nextIndex label))).2 (d.anchor_entry label.2.val)

theorem next_embed (label : h.toInputs.Labels) :
    next.embed (h.nextIndex label) = relationCompose (familyPointBound Qs) D d.batchCarrier
      (d.embed label.2.val) (h.maps.value label.1) :=
  ((pairCompositionFamily_entry_iff d.embeddings h.maps
    (d.embed_entry label.2.val) (h.maps.value_entry label.1)).1
      (next.embed_entry (h.nextIndex label))).2.2

theorem next_filter (label : h.toInputs.Labels) :
    next.filter (h.nextIndex label) = pushFilterCode d.batchCarrier d.batchOrder
      (h.maps.value label.1) (d.filter label.2.val) :=
  ((pairPushFilterFamily_entry_iff h.maps d.filters
    (h.maps.value_entry label.1) (d.filter_entry label.2.val)).1
      (next.filter_entry (h.nextIndex label))).2.2

noncomputable def nextFresh (q : h.toInputs.nextBatch.Fresh) : next.templates.Fresh :=
  ⟨h.nextIndex q.1, ⟨⟨q.2.val.val, (h.next_space M next q.1).symm ▸ q.2.val.property⟩,
    fun lower => q.2.property (by
      change ZFSet.pair q.2.val.val (next.anchor (h.nextIndex q.1)) ∈
        next.rel (h.nextIndex q.1) at lower
      rwa [h.next_anchor M next, h.next_rel M next] at lower)⟩⟩

theorem nextFresh_injective : Function.Injective (h.nextFresh M next) := by
  rintro ⟨a, q⟩ ⟨b, t⟩ equal
  have same : a = b := h.nextIndex_injective (congrArg Sigma.fst equal)
  subst b
  have values : q.val.val = t.val.val :=
    congrArg (fun z : next.templates.Fresh => z.2.val.val) equal
  exact congrArg (Sigma.mk a) (Subtype.ext (Subtype.ext values))

theorem nextFresh_surjective : Function.Surjective (h.nextFresh M next) := by
  rintro ⟨k, q⟩
  obtain ⟨label, equal⟩ := h.nextIndex_surjective k
  subst k
  have member : q.val.val ∈ d.space label.2.val :=
    h.next_space M next label ▸ q.val.property
  have outside : ZFSet.pair q.val.val (d.anchor label.2.val) ∉ d.rel label.2.val := by
    intro lower
    apply q.property
    change ZFSet.pair q.val.val (next.anchor (h.nextIndex label)) ∈ next.rel (h.nextIndex label)
    rwa [h.next_anchor M next, h.next_rel M next]
  exact ⟨⟨label, ⟨⟨q.val.val, member⟩, outside⟩⟩, rfl⟩

theorem nextFresh_inside_iff (q t : h.toInputs.nextBatch.Fresh) :
    next.templates.Inside (h.nextFresh M next q) (h.nextFresh M next t) ↔
      h.toInputs.nextBatch.Inside q t := by
  rcases q with ⟨a, q⟩
  rcases t with ⟨b, t⟩
  constructor
  · rintro ⟨same, lower⟩
    have eq : a = b := h.nextIndex_injective same
    subst b
    refine ⟨rfl, ?_⟩
    change ZFSet.pair q.val.val t.val.val ∈ next.rel (h.nextIndex a) at lower
    change ZFSet.pair q.val.val t.val.val ∈ d.rel a.2.val
    rwa [h.next_rel M next] at lower
  · rintro ⟨same, lower⟩
    change a = b at same
    subst b
    refine ⟨rfl, ?_⟩
    change ZFSet.pair q.val.val t.val.val ∈ next.rel (h.nextIndex a)
    rw [h.next_rel M next]
    exact lower

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

noncomputable abbrev liftGraph :=
  liftedCompressionGraph I J D d.batchCarrier next.batchCarrier
    (indexedAttachmentFresh J Qs rs As) (familyPointBound Qs) Maps Sources Fs Reps G A

noncomputable abbrev liftSection (i : ZFSet.{u}) :=
  indexedRelationSection d.batchCarrier next.batchCarrier (h.liftGraph M next) i

theorem liftGraph_function :
    ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) :=
  liftedCompressionGraph_function rfl
    (fun _ hz => indexedAttachmentDomain_subset J Qs (indexedAttachmentFresh_subset J Qs rs As hz))
    (fun _ hz => old_mem_taggedExtension hz) h.maps
    (fun i S entry => (h.valid i S entry).injection.function)
    h.sources d.filters h.representatives h.action.function
    (fun _ _ _ _ _ _ _ _ fresh source filter negative =>
      negativeRecursiveFresh_mem h.sources d.filters source filter fresh negative)

theorem liftSection_function {i : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.IsFunc d.batchCarrier next.batchCarrier (h.liftSection M next i) :=
  indexedRelationSection_function (h.liftGraph_function M next) hi

theorem liftGraph_old_iff {i S x y : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    ZFSet.pair (ZFSet.pair i x) y ∈ h.liftGraph M next ↔ ZFSet.pair x y ∈ S := by
  rw [liftGraph, liftedCompressionGraph_old_iff h.maps mapEntry hx]
  constructor
  · exact fun entry => entry.2.2
  · intro entry
    exact ⟨old_mem_taggedExtension hx, old_mem_taggedExtension
      (ZFSet.pair_mem_prod.1 ((h.valid i S mapEntry).injection.function.1 entry)).2, entry⟩

theorem liftGraph_positive_iff {i j q a F g y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (representative : ZFSet.pair i g ∈ Reps)
    (fresh : ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As) (positive : a ∈ F) :
    ZFSet.pair (ZFSet.pair i (ZFSet.pair D (ZFSet.pair j q))) y ∈ h.liftGraph M next ↔
      ZFSet.pair (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) y ∈ A := by
  have bounds := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset J Qs
    (indexedAttachmentFresh_subset J Qs rs As fresh))
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have sourceFunc : FunctionGraphOn I Sources := ⟨D, h.sources⟩
  rw [liftGraph, liftedCompressionGraph_fresh_iff sourceFunc d.filters source filter
    bounds.1 bounds.2 ha fresh]
  constructor
  · rintro ⟨_, _, ⟨_, g', _, representative', acted⟩ | ⟨negative, _⟩⟩
    · exact (show FunctionGraphOn I Reps from ⟨G, h.representatives⟩).unique
        representative' representative ▸ acted
    · exact False.elim (negative positive)
  · intro acted
    have hy := (ZFSet.pair_mem_prod.1 (h.action.function.1 acted)).2
    exact ⟨pair_mem_taggedExtension.2 fresh, old_mem_taggedExtension hy,
      Or.inl ⟨positive, g, (ZFSet.pair_mem_prod.1 (h.representatives.1 representative)).2,
        representative, acted⟩⟩

theorem liftGraph_negative_iff {i j q a F y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (fresh : ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As) (negative : a ∉ F) :
    ZFSet.pair (ZFSet.pair i (ZFSet.pair D (ZFSet.pair j q))) y ∈ h.liftGraph M next ↔
      y = ZFSet.pair d.batchCarrier (ZFSet.pair (ZFSet.pair i j) q) := by
  have bounds := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset J Qs
    (indexedAttachmentFresh_subset J Qs rs As fresh))
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have sourceFunc : FunctionGraphOn I Sources := ⟨D, h.sources⟩
  rw [liftGraph, liftedCompressionGraph_fresh_iff sourceFunc d.filters source filter
    bounds.1 bounds.2 ha fresh]
  constructor
  · rintro ⟨_, _, ⟨positive, _⟩ | ⟨_, equal⟩⟩
    · exact False.elim (negative positive)
    · exact equal
  · intro equal
    exact ⟨pair_mem_taggedExtension.2 fresh,
      equal.symm ▸ negativeRecursiveFresh_mem h.sources d.filters source filter fresh negative,
      Or.inr ⟨negative, equal⟩⟩






theorem liftGraph_agrees_on_base {i a g x y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (representative : ZFSet.pair i g ∈ Reps)
    (hx : x ∈ d.batchCarrier) (below : ZFSet.pair x a ∈ d.batchOrder) :
    ZFSet.pair (ZFSet.pair i x) y ∈ h.liftGraph M next ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  have hi := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).1
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  have lower := (d.coding.le_encode X (.inl ⟨a, ha⟩)).1 below
  cases X with
  | inl p =>
    obtain ⟨S, mapEntry⟩ := h.maps.total hi
    exact (h.liftGraph_old_iff M next mapEntry p.property).trans
      (h.agreement i a g S p.val y source representative mapEntry p.property lower)
  | inr q =>
    exact h.liftGraph_positive_iff M next source (d.filter_entry q.1) representative
      (d.freshCode_mem q) lower

theorem liftSection_agrees_on_base {i a g x y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (representative : ZFSet.pair i g ∈ Reps)
    (hx : x ∈ d.batchCarrier) (below : ZFSet.pair x a ∈ d.batchOrder) :
    ZFSet.pair x y ∈ h.liftSection M next i ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  rw [liftSection, pair_mem_indexedRelationSection, h.liftGraph_agrees_on_base M next source representative hx below]
  constructor
  · exact fun h => h.2.2
  · intro acted
    exact ⟨hx, old_mem_taggedExtension (ZFSet.pair_mem_prod.1 (h.action.function.1 acted)).2, acted⟩

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
