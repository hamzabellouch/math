import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairCompositions
import OAI.SetTheory.PartitionPrinciple.Definability.MapFamilyApplicationGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.TaggedExtensionCodes

namespace OAI

namespace PartitionPilot.Forcing

universe u

def liftOldEntry (D Maps i x y : ZFSet.{u}) : Prop :=
  x ∈ D ∧ ∃ S ∈ ZFSet.sUnion (ZFSet.sUnion Maps), ZFSet.pair i S ∈ Maps ∧ ZFSet.pair x y ∈ S

def liftFreshEntry (D L J B N Sources Fs Reps G A i x y : ZFSet.{u}) : Prop :=
  ∃ j ∈ J, ∃ q ∈ B, ∃ a ∈ D, ∃ F ∈ ZFSet.sUnion (ZFSet.sUnion Fs),
    x = ZFSet.pair D (ZFSet.pair j q) ∧ ZFSet.pair j q ∈ N ∧
    ZFSet.pair i a ∈ Sources ∧ ZFSet.pair j F ∈ Fs ∧
    ((a ∈ F ∧ ∃ g ∈ G, ZFSet.pair i g ∈ Reps ∧ ZFSet.pair (ZFSet.pair g x) y ∈ A) ∨
      (a ∉ F ∧ y = ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q)))

def liftedCompressionGraph (I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ x ∈ L, ∃ y ∈ C,
    z = ZFSet.pair (ZFSet.pair i x) y ∧
      (liftOldEntry D Maps i x y ∨ liftFreshEntry D L J B N Sources Fs Reps G A i x y))
    (ZFSet.prod (ZFSet.prod I L) C)

theorem pair_mem_liftedCompressionGraph (I J D L C N B Maps Sources Fs Reps G A i x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) y ∈ liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ↔
      i ∈ I ∧ x ∈ L ∧ y ∈ C ∧
        (liftOldEntry D Maps i x y ∨ liftFreshEntry D L J B N Sources Fs Reps G A i x y) := by
  rw [liftedCompressionGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, i', hi, x', hx, y', hy, eq, entry⟩
    obtain ⟨ix, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ix
    exact ⟨hi, hx, hy, entry⟩
  · rintro ⟨hi, hx, hy, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩,
      i, hi, x, hx, y, hy, rfl, entry⟩

theorem liftFreshEntry_not_old {D L J B N Sources Fs Reps G A i x y : ZFSet.{u}}
    (entry : liftFreshEntry D L J B N Sources Fs Reps G A i x y) : x ∉ D := by
  obtain ⟨j, _, q, _, _, _, _, _, eq, _⟩ := entry
  rw [eq]
  exact pair_tag_not_mem D (ZFSet.pair j q)

theorem liftOldEntry_iff {I D Maps i S x y : ZFSet.{u}}
    (maps : FunctionGraphOn I Maps) (entry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    liftOldEntry D Maps i x y ↔ ZFSet.pair x y ∈ S := by
  constructor
  · rintro ⟨_, T, _, iT, xy⟩
    exact maps.unique iT entry ▸ xy
  · intro xy
    exact ⟨hx, S, pair_second_mem_doubleUnion entry, entry, xy⟩

theorem liftedCompressionGraph_old_iff {I J D L C N B Maps Sources Fs Reps G A i S x y : ZFSet.{u}}
    (maps : FunctionGraphOn I Maps) (entry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    ZFSet.pair (ZFSet.pair i x) y ∈ liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ↔
      x ∈ L ∧ y ∈ C ∧ ZFSet.pair x y ∈ S := by
  rw [pair_mem_liftedCompressionGraph]
  constructor
  · rintro ⟨_, hxL, hy, old | fresh⟩
    · exact ⟨hxL, hy, (liftOldEntry_iff maps entry hx).1 old⟩
    · exact False.elim (liftFreshEntry_not_old fresh hx)
  · rintro ⟨hxL, hy, xy⟩
    exact ⟨maps.pair_source entry, hxL, hy, Or.inl ((liftOldEntry_iff maps entry hx).2 xy)⟩

theorem liftFreshEntry_iff {I D L J B N Sources Fs Reps G A i j q a F y : ZFSet.{u}}
    (sources : FunctionGraphOn I Sources) (filters : FunctionGraphOn J Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (hj : j ∈ J) (hq : q ∈ B) (ha : a ∈ D) (fresh : ZFSet.pair j q ∈ N) :
    liftFreshEntry D L J B N Sources Fs Reps G A i (ZFSet.pair D (ZFSet.pair j q)) y ↔
      ((a ∈ F ∧ ∃ g ∈ G, ZFSet.pair i g ∈ Reps ∧
        ZFSet.pair (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) y ∈ A) ∨
      (a ∉ F ∧ y = ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q))) := by
  constructor
  · rintro ⟨j', _, q', _, a', _, F', _, eq, _, source', filter', output⟩
    have jq := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 eq).2
    obtain ⟨rfl, rfl⟩ := jq
    have aEq := sources.unique source' source
    have FEq := filters.unique filter' filter
    exact aEq ▸ FEq ▸ output
  · intro output
    exact ⟨j, hj, q, hq, a, ha, F, pair_second_mem_doubleUnion filter,
      rfl, fresh, source, filter, output⟩

theorem liftedCompressionGraph_fresh_iff
    {I J D L C N B Maps Sources Fs Reps G A i j q a F y : ZFSet.{u}}
    (sources : FunctionGraphOn I Sources) (filters : FunctionGraphOn J Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (hj : j ∈ J) (hq : q ∈ B) (ha : a ∈ D) (fresh : ZFSet.pair j q ∈ N) :
    ZFSet.pair (ZFSet.pair i (ZFSet.pair D (ZFSet.pair j q))) y ∈
      liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ↔
      ZFSet.pair D (ZFSet.pair j q) ∈ L ∧ y ∈ C ∧
      ((a ∈ F ∧ ∃ g ∈ G, ZFSet.pair i g ∈ Reps ∧
        ZFSet.pair (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) y ∈ A) ∨
      (a ∉ F ∧ y = ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q))) := by
  rw [pair_mem_liftedCompressionGraph]
  constructor
  · rintro ⟨_, hx, hy, old | entry⟩
    · exact False.elim (pair_tag_not_mem D (ZFSet.pair j q) old.1)
    · exact ⟨hx, hy, (liftFreshEntry_iff sources filters source filter hj hq ha fresh).1 entry⟩
  · rintro ⟨hx, hy, output⟩
    exact ⟨sources.pair_source source, hx, hy,
      Or.inr ((liftFreshEntry_iff sources filters source filter hj hq ha fresh).2 output)⟩

theorem liftedCompressionGraph_function
    {I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}}
    (current : L = taggedExtension D N) (freshShape : N ⊆ ZFSet.prod J B)
    (extension : L ⊆ C) (maps : FunctionGraphOn I Maps)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → ZFSet.IsFunc D L S)
    (sources : ZFSet.IsFunc I D Sources) (filters : FunctionGraphOn J Fs)
    (reps : ZFSet.IsFunc I G Reps) (action : ZFSet.IsFunc (ZFSet.prod G L) L A)
    (negativeTargets : ∀ i ∈ I, ∀ j ∈ J, ∀ q ∈ B, ∀ a F,
      ZFSet.pair j q ∈ N → ZFSet.pair i a ∈ Sources → ZFSet.pair j F ∈ Fs →
        a ∉ F → ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q) ∈ C) :
    ZFSet.IsFunc (ZFSet.prod I L) C
      (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A) := by
  classical
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro p hp
  obtain ⟨i, hi, x, hxL, rfl⟩ := ZFSet.mem_prod.1 hp
  rcases mem_taggedExtension.1 (current ▸ hxL) with old | ⟨n, hn, rfl⟩
  · obtain ⟨S, mapEntry⟩ := maps.total hi
    obtain ⟨y, entry, unique⟩ := (valid i S mapEntry).2 x old
    have hy := (ZFSet.pair_mem_prod.1 ((valid i S mapEntry).1 entry)).2
    refine ⟨y, (liftedCompressionGraph_old_iff maps mapEntry old).2 ⟨hxL, extension hy, entry⟩, ?_⟩
    intro z hz
    exact unique z ((liftedCompressionGraph_old_iff maps mapEntry old).1 hz).2.2
  · obtain ⟨j, hj, q, hq, rfl⟩ := ZFSet.mem_prod.1 (freshShape hn)
    obtain ⟨a, source, _⟩ := sources.2 i hi
    have ha := (ZFSet.pair_mem_prod.1 (sources.1 source)).2
    obtain ⟨F, filter⟩ := filters.total hj
    have sourceFunc : FunctionGraphOn I Sources := ⟨D, sources⟩
    by_cases positive : a ∈ F
    · obtain ⟨g, representative, _⟩ := reps.2 i hi
      have hg := (ZFSet.pair_mem_prod.1 (reps.1 representative)).2
      obtain ⟨y, entry, unique⟩ := action.2
        (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) (ZFSet.pair_mem_prod.2 ⟨hg, hxL⟩)
      have hy := (ZFSet.pair_mem_prod.1 (action.1 entry)).2
      refine ⟨y, (liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).2
        ⟨hxL, extension hy, Or.inl ⟨positive, g, hg, representative, entry⟩⟩, ?_⟩
      intro z hz
      rcases ((liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).1 hz).2.2
          with ⟨_, g', _, representative', entry'⟩ | ⟨negative, _⟩
      · have equal : g' = g := (show FunctionGraphOn I Reps from ⟨G, reps⟩).unique representative' representative
        exact unique z (equal ▸ entry')
      · exact False.elim (negative positive)
    · let y := ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q)
      have hy : y ∈ C := negativeTargets i hi j hj q hq a F hn source filter positive
      refine ⟨y, (liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).2
        ⟨hxL, hy, Or.inr ⟨positive, rfl⟩⟩, ?_⟩
      intro z hz
      rcases ((liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).1 hz).2.2
          with ⟨positive', _⟩ | ⟨_, equal⟩
      · exact False.elim (positive positive')
      · exact equal

theorem indexedRelationSection_function {I L C R i : ZFSet.{u}}
    (function : ZFSet.IsFunc (ZFSet.prod I L) C R) (hi : i ∈ I) :
    ZFSet.IsFunc L C (indexedRelationSection L C R i) := by
  refine ⟨indexedRelationSection_subset L C R i, ?_⟩
  intro x hx
  obtain ⟨y, entry, unique⟩ := function.2 (ZFSet.pair i x) (ZFSet.pair_mem_prod.2 ⟨hi, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  refine ⟨y, (pair_mem_indexedRelationSection L C R i x y).2 ⟨hx, hy, entry⟩, ?_⟩
  intro z hz
  exact unique z ((pair_mem_indexedRelationSection L C R i x z).1 hz).2.2

theorem liftedCompressionSection_function
    {I J D L C N B Maps Sources Fs Reps G A i : ZFSet.{u}}
    (current : L = taggedExtension D N) (freshShape : N ⊆ ZFSet.prod J B)
    (extension : L ⊆ C) (maps : FunctionGraphOn I Maps)
    (valid : ∀ j S, ZFSet.pair j S ∈ Maps → ZFSet.IsFunc D L S)
    (sources : ZFSet.IsFunc I D Sources) (filters : FunctionGraphOn J Fs)
    (reps : ZFSet.IsFunc I G Reps) (action : ZFSet.IsFunc (ZFSet.prod G L) L A)
    (negativeTargets : ∀ j ∈ I, ∀ k ∈ J, ∀ q ∈ B, ∀ a F,
      ZFSet.pair k q ∈ N → ZFSet.pair j a ∈ Sources → ZFSet.pair k F ∈ Fs →
        a ∉ F → ZFSet.pair L (ZFSet.pair (ZFSet.pair j k) q) ∈ C)
    (hi : i ∈ I) :
    ZFSet.IsFunc L C (indexedRelationSection L C
      (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A) i) :=
  indexedRelationSection_function
    (liftedCompressionGraph_function current freshShape extension maps valid sources filters reps action negativeTargets) hi

end PartitionPilot.Forcing

end OAI
