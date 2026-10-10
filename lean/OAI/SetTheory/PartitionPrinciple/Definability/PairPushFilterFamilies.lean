import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFilterCopies

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def pushFilterCode (L rL S F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ f ∈ F, ∃ z ∈ L,
    ZFSet.pair f z ∈ S ∧ ZFSet.pair z y ∈ rL) L

theorem mem_pushFilterCode (L rL S F y : ZFSet.{u}) :
    y ∈ pushFilterCode L rL S F ↔ y ∈ L ∧ ∃ f ∈ F, ∃ z ∈ L,
      ZFSet.pair f z ∈ S ∧ ZFSet.pair z y ∈ rL := ZFSet.mem_sep

theorem pushFilterCode_subset (L rL S F : ZFSet.{u}) : pushFilterCode L rL S F ⊆ L :=
  fun _ hy => ((mem_pushFilterCode L rL S F _).1 hy).1

theorem MeetEmbeddingCode.order_iff {P L rP rL μP μL S x y x' y' : ZFSet.{u}}
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (source : MeetOrderCode P rP μP) (target : MeetOrderCode L rL μL)
    (first : ZFSet.pair x x' ∈ S) (second : ZFSet.pair y y' ∈ S) :
    ZFSet.pair x' y' ∈ rL ↔ ZFSet.pair x y ∈ rP := by
  refine ⟨?_, fun lower => embedding.monotone x y x' y' lower first second⟩
  intro lower
  have sx := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 first)
  have sy := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 second)
  obtain ⟨z, meetXY, _⟩ := source.operation.2 (ZFSet.pair x y)
    (ZFSet.pair_mem_prod.2 ⟨sx.1, sy.1⟩)
  have hz := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
  obtain ⟨z', image, _⟩ := embedding.injection.function.2 z hz
  have hz' := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).2
  have imageMeet := embedding.map_meet x y z x' y' z' meetXY first second image
  have equalImage : z' = x' := target.order.antisymm z' hz' x' sx.2
    (target.lower_left x' y' z' imageMeet)
    (target.greatest x' y' z' x' sx.2 imageMeet (target.order.refl x' sx.2) lower)
  have equal : z = x := embedding.injection.injective z x x' (equalImage ▸ image) first
  exact equal ▸ source.lower_right x y z meetXY

theorem meetFilter_pushFilter {P L rP rL μP μL S F : ZFSet.{u}}
    (source : MeetOrderCode P rP μP) (target : MeetOrderCode L rL μL)
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (filter : MeetFilterCode P rP μP F) :
    MeetFilterCode L rL μL (pushFilterCode L rL S F) where
  subset := pushFilterCode_subset L rL S F
  nonempty := by
    obtain ⟨f, hf⟩ := filter.nonempty
    obtain ⟨z, image, _⟩ := embedding.injection.function.2 f (filter.subset hf)
    have hz := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).2
    exact ⟨z, (mem_pushFilterCode L rL S F z).2
      ⟨hz, f, hf, z, hz, image, target.order.refl z hz⟩⟩
  upward := by
    intro x hx y hy lower
    obtain ⟨hxL, f, hf, z, hz, image, below⟩ := (mem_pushFilterCode L rL S F x).1 hx
    exact (mem_pushFilterCode L rL S F y).2
      ⟨hy, f, hf, z, hz, image, target.order.trans z hz x hxL y hy below lower⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨hxL, f, hf, f', hf', first, belowX⟩ := (mem_pushFilterCode L rL S F x).1 hx
    obtain ⟨hyL, g, hg, g', hg', second, belowY⟩ := (mem_pushFilterCode L rL S F y).1 hy
    have hz := (ZFSet.pair_mem_prod.1 (target.operation.1 meetXY)).2
    obtain ⟨h, meetFG, _⟩ := source.operation.2 (ZFSet.pair f g)
      (ZFSet.pair_mem_prod.2 ⟨filter.subset hf, filter.subset hg⟩)
    have hhF := filter.closed_meet f hf g hg h meetFG
    obtain ⟨h', image, _⟩ := embedding.injection.function.2 h (filter.subset hhF)
    have hh' := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).2
    have imageMeet := embedding.map_meet f g h f' g' h' meetFG first second image
    have left := target.order.trans h' hh' f' hf' x hxL
      (target.lower_left f' g' h' imageMeet) belowX
    have right := target.order.trans h' hh' g' hg' y hyL
      (target.lower_right f' g' h' imageMeet) belowY
    exact (mem_pushFilterCode L rL S F z).2
      ⟨hz, h, hhF, h', hh', image, target.greatest x y z h' hh' meetXY left right⟩

theorem pushFilter_trace {P L rP rL μP μL S F x y : ZFSet.{u}}
    (source : MeetOrderCode P rP μP) (target : MeetOrderCode L rL μL)
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (filter : MeetFilterCode P rP μP F) (entry : ZFSet.pair x y ∈ S) :
    y ∈ pushFilterCode L rL S F ↔ x ∈ F := by
  have shape := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)
  constructor
  · intro positive
    obtain ⟨_, f, hf, z, _, image, below⟩ := (mem_pushFilterCode L rL S F y).1 positive
    exact filter.upward f hf x shape.1 ((embedding.order_iff source target image entry).1 below)
  · intro positive
    exact (mem_pushFilterCode L rL S F y).2
      ⟨shape.2, x, positive, y, shape.2, entry, target.order.refl y shape.2⟩

theorem pushFilter_lower_bound {P L rP rL μP μL S F e e' y : ZFSet.{u}}
    (target : MeetOrderCode L rL μL) (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (lower : ∀ f ∈ F, ZFSet.pair e f ∈ rP) (entry : ZFSet.pair e e' ∈ S)
    (positive : y ∈ pushFilterCode L rL S F) : ZFSet.pair e' y ∈ rL := by
  obtain ⟨hy, f, hf, z, hz, image, below⟩ := (mem_pushFilterCode L rL S F y).1 positive
  have he' := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2
  exact target.order.trans e' he' z hz y hy
    (embedding.monotone e f e' z (lower f hf) entry image) below

noncomputable def pairPushFilterFamily (K I J L rL Ss Fs B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ j ∈ J, ∃ S ∈ Ss.sUnion.sUnion,
    ∃ F ∈ Fs.sUnion.sUnion, ∃ V ∈ B,
    z = ZFSet.pair (ZFSet.pair i j) V ∧ ZFSet.pair i S ∈ Ss ∧ ZFSet.pair j F ∈ Fs ∧
      V = pushFilterCode L rL S F) (ZFSet.prod K B)

theorem pair_mem_pairPushFilterFamily (K I J L rL Ss Fs B i j V : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i j) V ∈ pairPushFilterFamily K I J L rL Ss Fs B ↔
      ZFSet.pair i j ∈ K ∧ V ∈ B ∧ i ∈ I ∧ j ∈ J ∧ ∃ S F,
        ZFSet.pair i S ∈ Ss ∧ ZFSet.pair j F ∈ Fs ∧ V = pushFilterCode L rL S F := by
  rw [pairPushFilterFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hk, hV⟩, i', hi, j', hj, S, _, F, _, V', _, equal, eS, eF, value⟩
    obtain ⟨pairEq, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 pairEq
    exact ⟨hk, hV, hi, hj, S, F, eS, eF, value⟩
  · rintro ⟨hk, hV, hi, hj, S, F, eS, eF, value⟩
    exact ⟨⟨hk, hV⟩, i, hi, j, hj, S, pair_second_mem_doubleUnion eS,
      F, pair_second_mem_doubleUnion eF, V, hV, rfl, eS, eF, value⟩

theorem pairPushFilterFamily_entry_iff {K I J L rL Ss Fs B i j S F V : ZFSet.{u}}
    (maps : FunctionGraphOn I Ss) (filters : FunctionGraphOn J Fs)
    (mapEntry : ZFSet.pair i S ∈ Ss) (filterEntry : ZFSet.pair j F ∈ Fs) :
    ZFSet.pair (ZFSet.pair i j) V ∈ pairPushFilterFamily K I J L rL Ss Fs B ↔
      ZFSet.pair i j ∈ K ∧ V ∈ B ∧ V = pushFilterCode L rL S F := by
  rw [pair_mem_pairPushFilterFamily]
  constructor
  · rintro ⟨hk, hV, _, _, S', F', eS, eF, value⟩
    exact ⟨hk, hV, maps.unique eS mapEntry ▸ filters.unique eF filterEntry ▸ value⟩
  · rintro ⟨hk, hV, value⟩
    exact ⟨hk, hV, maps.pair_source mapEntry, filters.pair_source filterEntry,
      S, F, mapEntry, filterEntry, value⟩

theorem pairPushFilterFamily_function {K I J L rL Ss Fs B : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J) (maps : FunctionGraphOn I Ss) (filters : FunctionGraphOn J Fs)
    (bounds : ∀ i ∈ I, ∀ j ∈ J, ∀ S F,
      ZFSet.pair i S ∈ Ss → ZFSet.pair j F ∈ Fs → pushFilterCode L rL S F ∈ B) :
    ZFSet.IsFunc K B (pairPushFilterFamily K I J L rL Ss Fs B) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  obtain ⟨S, eS⟩ := maps.total hi
  obtain ⟨F, eF⟩ := filters.total hj
  exact ⟨pushFilterCode L rL S F,
    (pairPushFilterFamily_entry_iff maps filters eS eF).2 ⟨hk, bounds i hi j hj S F eS eF, rfl⟩,
    fun V hV => ((pairPushFilterFamily_entry_iff maps filters eS eF).1 hV).2.2⟩

end PartitionPilot.Forcing

end OAI
