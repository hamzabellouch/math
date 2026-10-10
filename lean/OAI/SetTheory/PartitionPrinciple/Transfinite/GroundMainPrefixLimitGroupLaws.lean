import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedValueLifts
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitCoverageGraph

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

noncomputable def directLimitRelation (T U F L : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ T, ∃ x ∈ U, ∃ j ∈ T, ∃ y ∈ U,
    ∃ k ∈ T, ∃ w ∈ U, ∃ f ∈ ⋃₀ ⋃₀ F, ∃ g ∈ ⋃₀ ⋃₀ F,
      z = ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∧
      ZFSet.pair (ZFSet.pair k i) f ∈ F ∧ ZFSet.pair (ZFSet.pair k j) g ∈ F ∧
      ZFSet.pair x w ∈ f ∧ ZFSet.pair y w ∈ g) (ZFSet.prod L L)

theorem directLimitRelation_subset (T U F L : ZFSet.{u}) :
    directLimitRelation T U F L ⊆ ZFSet.prod L L := fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_directLimitRelation (T U F L i x j y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∈ directLimitRelation T U F L ↔
      ZFSet.pair i x ∈ L ∧ ZFSet.pair j y ∈ L ∧
      i ∈ T ∧ x ∈ U ∧ j ∈ T ∧ y ∈ U ∧
      ∃ k ∈ T, ∃ w ∈ U, ∃ f g,
        ZFSet.pair (ZFSet.pair k i) f ∈ F ∧ ZFSet.pair (ZFSet.pair k j) g ∈ F ∧
        ZFSet.pair x w ∈ f ∧ ZFSet.pair y w ∈ g := by
  rw [directLimitRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨shape, a, ha, b, hb, c, hc, d, hd, k, hk, w, hw, f, _, g, _, equal, first, second, left, right⟩
    obtain ⟨ab, cd⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ab
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 cd
    exact ⟨(ZFSet.pair_mem_prod.1 shape).1, (ZFSet.pair_mem_prod.1 shape).2,
      ha, hb, hc, hd, k, hk, w, hw, f, g, first, second, left, right⟩
  · rintro ⟨leftLabel, rightLabel, hi, hx, hj, hy, k, hk, w, hw, f, g, first, second, left, right⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨leftLabel, rightLabel⟩,
      i, hi, x, hx, j, hj, y, hy, k, hk, w, hw,
      f, pair_second_mem_doubleUnion first, g, pair_second_mem_doubleUnion second,
      rfl, first, second, left, right⟩

namespace BoundedFormula
open SetFormula

def directLimitRelationEntryFormula : BoundedFormula 5 :=
  exMem 1 (exMem 3 (exMem 3 (exMem 5 (exMem 5 (exMem 7 (exMem 9 (exMem 10
    (.conj (pairOfPairsFormula 8 7 6 5 4)
      (.conj (tripleMembershipFormula 3 7 1 12)
        (.conj (tripleMembershipFormula 3 5 0 12)
          (.conj (pairMembershipFormula 6 2 1) (pairMembershipFormula 4 2 0))))))))))))

theorem truth_directLimitRelationEntryFormula (env : Fin 5 → ZFSet.{u}) :
    Truth directLimitRelationEntryFormula env ↔
      ∃ i ∈ env 1, ∃ x ∈ env 2, ∃ j ∈ env 1, ∃ y ∈ env 2,
        ∃ k ∈ env 1, ∃ w ∈ env 2, ∃ f ∈ env 3, ∃ g ∈ env 3,
          env 0 = ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∧
          ZFSet.pair (ZFSet.pair k i) f ∈ env 4 ∧ ZFSet.pair (ZFSet.pair k j) g ∈ env 4 ∧
          ZFSet.pair x w ∈ f ∧ ZFSet.pair y w ∈ g := by
  simp only [directLimitRelationEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_tripleMembershipFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem directLimitRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U F L : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hF : F ∈ M.sets) (hL : L ∈ M.sets) : directLimitRelation T U F L ∈ M.sets := by
  have hB := M.union_mem unions (M.union_mem unions hF)
  let params := extend T (extend U (extend (⋃₀ ⋃₀ F) (extend F Fin.elim0)))
  have selected := M.bounded_separation_mem separation BoundedFormula.directLimitRelationEntryFormula
    params (Fin.cases hT (Fin.cases hU (Fin.cases hB (Fin.cases hF (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hL hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.directLimitRelationEntryFormula
      (extend z params)) (ZFSet.prod L L) = directLimitRelation T U F L := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, directLimitRelation, ZFSet.mem_sep,
      BoundedFormula.truth_directLimitRelationEntryFormula]
    rfl
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.CodedDirectPresentation
universe u v
variable {I : Type v} [Small.{u} I] [Preorder I] {system : CodedDirectSystem.{u} I}
variable {T U A F : ZFSet.{u}} (p : CodedDirectPresentation system T U A F)

theorem relation_iff (i : I) (x : ZFSet.{u}) (j : I) (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (p.key i) x) (ZFSet.pair (p.key j) y) ∈
        directLimitRelation T U F (indexedCarrierLabels T U A) ↔ system.Related i x j y := by
  rw [pair_mem_directLimitRelation]
  constructor
  · rintro ⟨_, _, _, _, _, _, k, hk, w, _, f, g, first, second, left, right⟩
    obtain ⟨k, rfl⟩ := p.exists_key hk
    obtain ⟨before, rfl⟩ := p.map_lookup first
    obtain ⟨after, rfl⟩ := p.map_lookup second
    exact ⟨k, before, after, w, left, right⟩
  · rintro ⟨k, first, second, w, left, right⟩
    have leftBounds := system.map_entry_bounds first left
    have rightBounds := system.map_entry_bounds second right
    exact ⟨(p.label_mem i x).2 leftBounds.1, (p.label_mem j y).2 rightBounds.1,
      p.key_mem i, p.carrier_bound i leftBounds.1, p.key_mem j, p.carrier_bound j rightBounds.1,
      p.key k, p.key_mem k, w, p.carrier_bound k leftBounds.2,
      system.map first, system.map second, p.map_entry first, p.map_entry second, left, right⟩

include p in
theorem relation_equivalence : EquivalenceRelationCode (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A)) := by
  refine ⟨directLimitRelation_subset _ _ _ _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, x, member, rfl⟩ := p.label_cases hx
    exact (p.relation_iff i x i x).2 (system.related_refl member)
  · intro x y related
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (directLimitRelation_subset _ _ _ _ related)
    obtain ⟨i, x, _, rfl⟩ := p.label_cases hx
    obtain ⟨j, y, _, rfl⟩ := p.label_cases hy
    exact (p.relation_iff j y i x).2 (system.related_symm ((p.relation_iff i x j y).1 related))
  · intro x y z first second
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (directLimitRelation_subset _ _ _ _ first)
    have hz := (ZFSet.pair_mem_prod.1 (directLimitRelation_subset _ _ _ _ second)).2
    obtain ⟨i, x, _, rfl⟩ := p.label_cases hx
    obtain ⟨j, y, _, rfl⟩ := p.label_cases hy
    obtain ⟨k, z, _, rfl⟩ := p.label_cases hz
    exact (p.relation_iff i x k z).2
      (system.related_trans ((p.relation_iff i x j y).1 first) ((p.relation_iff j y k z).1 second))

end PartitionPilot.Forcing.CodedDirectPresentation

namespace PartitionPilot.Forcing
universe u v

noncomputable def directLimitCarrier (T U A F : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A))

noncomputable def directLimitInclusion (T U A F k : ZFSet.{u}) : ZFSet.{u} :=
  indexedClassInclusion U (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A)) k

namespace CodedDirectPresentation
variable {I : Type v} [Small.{u} I] [Preorder I] {system : CodedDirectSystem.{u} I}
variable {T U A F : ZFSet.{u}} (p : CodedDirectPresentation system T U A F)

noncomputable def limitPoint (i : I) (x : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClass (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A)) (ZFSet.pair (p.key i) x)

theorem limitPoint_mem {i : I} {x : ZFSet.{u}} (member : x ∈ system.carrier i) :
    p.limitPoint i x ∈ directLimitCarrier T U A F :=
  equivalenceClass_mem ((p.label_mem i x).2 member)

theorem limitPoint_eq_iff_related {i j : I} {x y : ZFSet.{u}}
    (hx : x ∈ system.carrier i) (hy : y ∈ system.carrier j) :
    p.limitPoint i x = p.limitPoint j y ↔ system.Related i x j y :=
  (p.relation_equivalence.class_eq_iff ((p.label_mem i x).2 hx) ((p.label_mem j y).2 hy)).trans
    (p.relation_iff i x j y)

theorem limitPoint_same_iff {i : I} {x y : ZFSet.{u}}
    (hx : x ∈ system.carrier i) (hy : y ∈ system.carrier i) :
    p.limitPoint i x = p.limitPoint i y ↔ x = y :=
  (p.limitPoint_eq_iff_related hx hy).trans (system.related_same_iff_eq hx)

theorem limitPoint_transition {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    p.limitPoint i x = p.limitPoint j y :=
  (p.limitPoint_eq_iff_related (system.map_entry_bounds before entry).1
    (system.map_entry_bounds before entry).2).2 (system.related_of_entry before entry)

theorem limitPoint_later_iff {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (hx : x ∈ system.carrier i) (hy : y ∈ system.carrier j) :
    p.limitPoint i x = p.limitPoint j y ↔ ZFSet.pair x y ∈ system.map before :=
  (p.limitPoint_eq_iff_related hx hy).trans (system.related_iff_entry before)

theorem inclusion_entry (i : I) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ directLimitInclusion T U A F (p.key i) ↔
      x ∈ system.carrier i ∧ y = p.limitPoint i x :=
  pair_mem_indexedClassInclusion_of_entry p.carrier_function (p.carrier_entry i) (p.carrier_bound i)

theorem inclusion_injection (i : I) :
    InjectionCode (system.carrier i) (directLimitCarrier T U A F)
      (directLimitInclusion T U A F (p.key i)) := by
  refine ⟨indexedClassInclusion_function p.carrier_function (p.carrier_entry i) (p.carrier_bound i), ?_⟩
  intro x y z first second
  obtain ⟨hx, left⟩ := (p.inclusion_entry i x z).1 first
  obtain ⟨hy, right⟩ := (p.inclusion_entry i y z).1 second
  exact (p.limitPoint_same_iff hx hy).1 (left.symm.trans right)

theorem inclusion_comp {i j : I} (before : i ≤ j) :
    relationCompose (system.carrier i) (system.carrier j) (directLimitCarrier T U A F)
      (system.map before) (directLimitInclusion T U A F (p.key j)) =
      directLimitInclusion T U A F (p.key i) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, _, w, _, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨_, equal⟩ := (p.inclusion_entry j y w).1 yw
    exact (p.inclusion_entry i x w).2 ⟨hx, equal.trans (p.limitPoint_transition before xy).symm⟩
  · intro entry
    obtain ⟨x, _, w, _, rfl⟩ := ZFSet.mem_prod.1 ((p.inclusion_injection i).function.1 entry)
    obtain ⟨hx, rfl⟩ := (p.inclusion_entry i x w).1 entry
    obtain ⟨y, xy⟩ := system.map_entry_total before hx
    have hy := (system.map_entry_bounds before xy).2
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨hx, p.limitPoint_mem hx, y, hy, xy,
        (p.inclusion_entry j y (p.limitPoint i x)).2 ⟨hy, p.limitPoint_transition before xy⟩⟩

end CodedDirectPresentation

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem indexedCarrierLabels_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {T U : ZFSet.{u}} (A : ZFSet.{u})
    (indices : ZFSet.rank T < o) (points : ZFSet.rank U < o) :
    ZFSet.rank (indexedCarrierLabels T U A) < o :=
  (ZFSet.rank_mono (indexedCarrierLabels_subset T U A)).trans_lt
    (rank_product_lt limit indices points)

theorem directLimitRelation_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U F : ZFSet.{u}) {L : ZFSet.{u}} (labels : ZFSet.rank L < o) :
    ZFSet.rank (directLimitRelation T U F L) < o :=
  (ZFSet.rank_mono (directLimitRelation_subset T U F L)).trans_lt
    (rank_product_lt limit labels labels)

theorem equivalenceClasses_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {L : ZFSet.{u}} (E : ZFSet.{u}) (labels : ZFSet.rank L < o) :
    ZFSet.rank (equivalenceClasses L E) < o := by
  have bound := ZFSet.rank_mono
    (show equivalenceClasses L E ⊆ ZFSet.powerset L from fun _ hz => (ZFSet.mem_sep.1 hz).1)
  rw [ZFSet.rank_powerset] at bound
  exact bound.trans_lt (limit.succ_lt labels)

theorem equivalenceClassifier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {L : ZFSet.{u}} (E : ZFSet.{u}) (labels : ZFSet.rank L < o) :
    ZFSet.rank (equivalenceClassifier L E) < o :=
  (ZFSet.rank_mono
    (show equivalenceClassifier L E ⊆ ZFSet.prod L (equivalenceClasses L E)
      from fun _ hz => (ZFSet.mem_sep.1 hz).1)).trans_lt
    (rank_product_lt limit labels (equivalenceClasses_rank_lt limit E labels))

theorem indexedClassInclusion_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {U L : ZFSet.{u}} (E i : ZFSet.{u})
    (points : ZFSet.rank U < o) (labels : ZFSet.rank L < o) :
    ZFSet.rank (indexedClassInclusion U L E i) < o :=
  (ZFSet.rank_mono (indexedRelationSection_subset U (equivalenceClasses L E)
    (equivalenceClassifier L E) i)).trans_lt
    (rank_product_lt limit points (equivalenceClasses_rank_lt limit E labels))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedClassInclusions_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {T U L : ZFSet.{u}} (E : ZFSet.{u}) (indices : ZFSet.rank T < o)
    (points : ZFSet.rank U < o) (labels : ZFSet.rank L < o) :
    ZFSet.rank (M.indexedClassInclusions T U L E) < o :=
  (ZFSet.rank_mono
    (show M.indexedClassInclusions T U L E ⊆
        ZFSet.prod T (M.groundRelations U (equivalenceClasses L E))
      from fun _ hz => by
        unfold indexedClassInclusions indexedRelationSections at hz
        exact (ZFSet.mem_sep.1 hz).1)).trans_lt
    (rank_product_lt limit indices
      (M.groundRelations_rank_lt limit points (equivalenceClasses_rank_lt limit E labels)))

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.CodedDirectPresentation
universe u v
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {system : CodedDirectSystem.{u} I} {T U A F : ZFSet.{u}}
variable (p : CodedDirectPresentation system T U A F)

theorem limitPoint_coverage {z : ZFSet.{u}} (member : z ∈ directLimitCarrier T U A F) :
    ∃ i x, x ∈ system.carrier i ∧ z = p.limitPoint i x := by
  obtain ⟨label, labelMember, rfl⟩ := (mem_equivalenceClasses _ _ z).1 member
  obtain ⟨i, x, hx, rfl⟩ := p.label_cases labelMember
  exact ⟨i, x, hx, rfl⟩

theorem mixed_pair_coverage {other : CodedDirectSystem.{u} I} {T' U' A' F' : ZFSet.{u}}
    (q : CodedDirectPresentation other T' U' A' F') {z w : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T' U' A' F') :
    ∃ k x y, x ∈ system.carrier k ∧ y ∈ other.carrier k ∧
      z = p.limitPoint k x ∧ w = q.limitPoint k y := by
  obtain ⟨i, x, hx, rfl⟩ := p.limitPoint_coverage hz
  obtain ⟨j, y, hy, rfl⟩ := q.limitPoint_coverage hw
  obtain ⟨k, ik, jk⟩ := system.common_upper i j
  obtain ⟨x', xx'⟩ := system.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := other.map_entry_total jk hy
  exact ⟨k, x', y', (system.map_entry_bounds ik xx').2, (other.map_entry_bounds jk yy').2,
    p.limitPoint_transition ik xx', q.limitPoint_transition jk yy'⟩

theorem mixed_triple_coverage {other third : CodedDirectSystem.{u} I}
    {T' U' A' F' T'' U'' A'' F'' : ZFSet.{u}}
    (q : CodedDirectPresentation other T' U' A' F')
    (r : CodedDirectPresentation third T'' U'' A'' F'') {z w v : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T' U' A' F')
    (hv : v ∈ directLimitCarrier T'' U'' A'' F'') :
    ∃ k x y a, x ∈ system.carrier k ∧ y ∈ other.carrier k ∧ a ∈ third.carrier k ∧
      z = p.limitPoint k x ∧ w = q.limitPoint k y ∧ v = r.limitPoint k a := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := p.mixed_pair_coverage q hz hw
  obtain ⟨j, a, ha, rfl⟩ := r.limitPoint_coverage hv
  obtain ⟨k, ik, jk⟩ := system.common_upper i j
  obtain ⟨x', xx'⟩ := system.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := other.map_entry_total ik hy
  obtain ⟨a', aa'⟩ := third.map_entry_total jk ha
  exact ⟨k, x', y', a', (system.map_entry_bounds ik xx').2, (other.map_entry_bounds ik yy').2,
    (third.map_entry_bounds jk aa').2, p.limitPoint_transition ik xx',
    q.limitPoint_transition ik yy', r.limitPoint_transition jk aa'⟩

theorem pair_coverage {z w : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T U A F) :
    ∃ k x y, x ∈ system.carrier k ∧ y ∈ system.carrier k ∧
      z = p.limitPoint k x ∧ w = p.limitPoint k y :=
  p.mixed_pair_coverage p hz hw

theorem triple_coverage {z w v : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T U A F)
    (hv : v ∈ directLimitCarrier T U A F) :
    ∃ k x y a, x ∈ system.carrier k ∧ y ∈ system.carrier k ∧ a ∈ system.carrier k ∧
      z = p.limitPoint k x ∧ w = p.limitPoint k y ∧ v = p.limitPoint k a :=
  p.mixed_triple_coverage p p hz hw hv

end PartitionPilot.Forcing.CodedDirectPresentation

namespace PartitionPilot.Forcing.CodedDirectPresentation
universe u v
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {system : CodedDirectSystem.{u} I} {T U A F Q : ZFSet.{u}}
variable (p : CodedDirectPresentation system T U A F) (cone : system.InjectiveCone Q)

noncomputable def coneMap : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i x y, x ∈ system.carrier i ∧
    z = ZFSet.pair (p.limitPoint i x) y ∧ ZFSet.pair x y ∈ cone.map i)
    (ZFSet.prod (directLimitCarrier T U A F) Q)

theorem coneMap_subset : p.coneMap cone ⊆ ZFSet.prod (directLimitCarrier T U A F) Q :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem coneMap_entry (q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ p.coneMap cone ↔
      ∃ i x, x ∈ system.carrier i ∧ q = p.limitPoint i x ∧ ZFSet.pair x y ∈ cone.map i := by
  rw [coneMap, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, i, x, y', hx, equal, entry⟩
    obtain ⟨eq, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨i, x, hx, eq, entry⟩
  · rintro ⟨i, x, hx, rfl, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨p.limitPoint_mem hx, (cone.entry_bounds entry).2⟩,
      i, x, y, hx, rfl, entry⟩

theorem coneMap_at (i : I) {x : ZFSet.{u}} (hx : x ∈ system.carrier i) (y : ZFSet.{u}) :
    ZFSet.pair (p.limitPoint i x) y ∈ p.coneMap cone ↔ ZFSet.pair x y ∈ cone.map i := by
  rw [p.coneMap_entry cone]
  constructor
  · rintro ⟨j, z, hz, equal, zy⟩
    obtain ⟨v, xv⟩ := cone.entry_total hx
    have same := (cone.entry_eq_iff_related xv zy).2 ((p.limitPoint_eq_iff_related hx hz).1 equal)
    exact same ▸ xv
  · exact fun entry => ⟨i, x, hx, rfl, entry⟩

theorem coneMap_function : ZFSet.IsFunc (directLimitCarrier T U A F) Q (p.coneMap cone) := by
  refine ⟨p.coneMap_subset cone, ?_⟩
  intro q hq
  obtain ⟨i, x, hx, rfl⟩ := p.limitPoint_coverage hq
  obtain ⟨y, xy⟩ := cone.entry_total hx
  refine ⟨y, (p.coneMap_at cone i hx y).2 xy, ?_⟩
  intro z entry
  exact (show FunctionGraphOn (system.carrier i) (cone.map i) from
    ⟨Q, (cone.injection i).function⟩).unique ((p.coneMap_at cone i hx z).1 entry) xy

theorem coneMap_injection : InjectionCode (directLimitCarrier T U A F) Q (p.coneMap cone) := by
  refine ⟨p.coneMap_function cone, ?_⟩
  intro q r y first second
  obtain ⟨i, x, hx, rfl, xy⟩ := (p.coneMap_entry cone q y).1 first
  obtain ⟨j, z, hz, rfl, zy⟩ := (p.coneMap_entry cone r y).1 second
  exact (p.limitPoint_eq_iff_related hx hz).2 ((cone.entry_eq_iff_related xy zy).1 rfl)

theorem coneMap_triangle (i : I) :
    relationCompose (system.carrier i) (directLimitCarrier T U A F) Q
      (directLimitInclusion T U A F (p.key i)) (p.coneMap cone) = cone.map i := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, _, q, _, y, _, rfl, inclusion, image⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨hx, rfl⟩ := (p.inclusion_entry i x q).1 inclusion
    exact (p.coneMap_at cone i hx y).1 image
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((cone.injection i).function.1 entry)
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hx, hy, p.limitPoint i x,
      p.limitPoint_mem hx, (p.inclusion_entry i x _).2 ⟨hx, rfl⟩,
      (p.coneMap_at cone i hx y).2 entry⟩

theorem coneMap_range (y : ZFSet.{u}) :
    (∃ q ∈ directLimitCarrier T U A F, ZFSet.pair q y ∈ p.coneMap cone) ↔
      ∃ i x, x ∈ system.carrier i ∧ ZFSet.pair x y ∈ cone.map i := by
  constructor
  · rintro ⟨q, _, entry⟩
    obtain ⟨i, x, hx, _, xy⟩ := (p.coneMap_entry cone q y).1 entry
    exact ⟨i, x, hx, xy⟩
  · rintro ⟨i, x, hx, xy⟩
    exact ⟨p.limitPoint i x, p.limitPoint_mem hx, (p.coneMap_at cone i hx y).2 xy⟩

theorem coneMap_onto {B : ZFSet.{u}} (coverage : cone.Covers B) :
    ∀ y ∈ B, ∃ q ∈ directLimitCarrier T U A F, ZFSet.pair q y ∈ p.coneMap cone :=
  fun y hy => (p.coneMap_range cone y).2 (coverage y hy)

theorem coneMap_unique {g : ZFSet.{u}}
    (function : ZFSet.IsFunc (directLimitCarrier T U A F) Q g)
    (triangles : ∀ i, relationCompose (system.carrier i) (directLimitCarrier T U A F) Q
      (directLimitInclusion T U A F (p.key i)) g = cone.map i) : g = p.coneMap cone := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨q, hq, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 entry)
    obtain ⟨i, x, hx, rfl⟩ := p.limitPoint_coverage hq
    apply (p.coneMap_at cone i hx y).2
    rw [← triangles i]
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨hx, hy, p.limitPoint i x, p.limitPoint_mem hx,
        (p.inclusion_entry i x _).2 ⟨hx, rfl⟩, entry⟩
  · intro entry
    obtain ⟨q, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (p.coneMap_subset cone entry)
    obtain ⟨i, x, _, rfl, xy⟩ := (p.coneMap_entry cone q y).1 entry
    rw [← triangles i] at xy
    obtain ⟨_, _, q, _, inclusion, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xy
    obtain ⟨_, rfl⟩ := (p.inclusion_entry i x q).1 inclusion
    exact image

end PartitionPilot.Forcing.CodedDirectPresentation

namespace PartitionPilot.Forcing.CodedDirectPresentation
open SetFormula
universe u v
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {system : CodedDirectSystem.{u} I} {T U A F Q : ZFSet.{u}}
variable (p : CodedDirectPresentation system T U A F) (cone : system.InjectiveCone Q)

theorem coneMap_eq_indexedValueLift {G J : ZFSet.{u}}
    (legs : ∀ i g, ZFSet.pair (p.key i) g ∈ G ↔ g = cone.map i)
    (inclusions : ∀ i e, ZFSet.pair (p.key i) e ∈ J ↔
      e = directLimitInclusion T U A F (p.key i)) :
    p.coneMap cone = indexedValueLift T U (directLimitCarrier T U A F) Q G J := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨q, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (p.coneMap_subset cone entry)
    obtain ⟨i, x, hx, rfl, xy⟩ := (p.coneMap_entry cone q y).1 entry
    exact (pair_mem_indexedValueLift _ _ _ _ _ _ _ _).2
      ⟨p.limitPoint_mem hx, (cone.entry_bounds xy).2, p.key i, p.key_mem i,
        cone.map i, directLimitInclusion T U A F (p.key i), x, p.carrier_bound i hx,
        (legs i _).2 rfl, (inclusions i _).2 rfl,
        (p.inclusion_entry i x _).2 ⟨hx, rfl⟩, xy⟩
  · intro entry
    obtain ⟨q, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (indexedValueLift_subset _ _ _ _ _ _ entry)
    obtain ⟨_, _, k, hk, g, e, x, _, kg, ke, image, xy⟩ :=
      (pair_mem_indexedValueLift _ _ _ _ _ _ _ _).1 entry
    obtain ⟨i, rfl⟩ := p.exists_key hk
    obtain rfl := (legs i g).1 kg
    obtain rfl := (inclusions i e).1 ke
    obtain ⟨hx, rfl⟩ := (p.inclusion_entry i x q).1 image
    exact (p.coneMap_at cone i hx y).2 xy

theorem coneMap_ground (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hA : A ∈ M.sets) (hF : F ∈ M.sets) (hQ : Q ∈ M.sets) (hG : G ∈ M.sets)
    (family : FunctionGraphOn T G) (entries : ∀ i, ZFSet.pair (p.key i) (cone.map i) ∈ G) :
    p.coneMap cone ∈ M.sets := by
  let L := indexedCarrierLabels T U A
  let E := directLimitRelation T U F L
  let J := M.indexedClassInclusions T U L E
  have hL : L ∈ M.sets := M.indexedCarrierLabels_mem pairing unions powers separation hT hU hA
  have hE : E ∈ M.sets := M.directLimitRelation_mem pairing unions powers separation hT hU hF hL
  have hClasses : directLimitCarrier T U A F ∈ M.sets :=
    M.equivalenceClasses_mem powers separation hL hE
  have hJ : J ∈ M.sets := M.indexedClassInclusions_mem pairing unions powers separation hT hU hL hE
  have legs (i : I) (g : ZFSet.{u}) : ZFSet.pair (p.key i) g ∈ G ↔ g = cone.map i :=
    ⟨fun entry => family.unique entry (entries i), fun equal => equal.symm ▸ entries i⟩
  have inclusions (i : I) (e : ZFSet.{u}) : ZFSet.pair (p.key i) e ∈ J ↔
      e = directLimitInclusion T U A F (p.key i) := by
    exact (M.indexedClassInclusions_entries pairing unions powers separation hT hU hL hE
      (p.key i) e).trans (and_iff_right (p.key_mem i))
  rw [p.coneMap_eq_indexedValueLift cone legs inclusions]
  exact M.indexedValueLift_mem pairing unions powers separation hT hU hClasses hQ hG hJ

theorem coneMap_injection_into {B : ZFSet.{u}}
    (bound : ∀ i x y, ZFSet.pair x y ∈ cone.map i → y ∈ B) :
    InjectionCode (directLimitCarrier T U A F) B (p.coneMap cone) := by
  refine ⟨⟨?_, (p.coneMap_function cone).2⟩, (p.coneMap_injection cone).injective⟩
  intro z entry
  obtain ⟨q, hq, y, _, rfl⟩ := ZFSet.mem_prod.1 (p.coneMap_subset cone entry)
  obtain ⟨i, x, _, _, xy⟩ := (p.coneMap_entry cone q y).1 entry
  exact ZFSet.pair_mem_prod.2 ⟨hq, bound i x y xy⟩

theorem coneMap_bijection_onto {B : ZFSet.{u}}
    (bound : ∀ i x y, ZFSet.pair x y ∈ cone.map i → y ∈ B) (coverage : cone.Covers B) :
    InjectionCode (directLimitCarrier T U A F) B (p.coneMap cone) ∧
      ∀ y ∈ B, ∃ q ∈ directLimitCarrier T U A F, ZFSet.pair q y ∈ p.coneMap cone :=
  ⟨p.coneMap_injection_into cone bound, p.coneMap_onto cone coverage⟩

end PartitionPilot.Forcing.CodedDirectPresentation

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def limitPointLabels : ZFSet.{u} :=
  indexedCarrierLabels run.indices run.carrierUnion run.carrierFamily

noncomputable def limitPointRelation : ZFSet.{u} :=
  directLimitRelation run.indices run.carrierUnion run.pointMapFamily run.limitPointLabels

noncomputable def limitPoints : ZFSet.{u} :=
  directLimitCarrier run.indices run.carrierUnion run.carrierFamily run.pointMapFamily

noncomputable def limitPointMap (i : I) : ZFSet.{u} :=
  directLimitInclusion run.indices run.carrierUnion run.carrierFamily run.pointMapFamily (run.key i)

noncomputable def limitPointInclusions : ZFSet.{u} :=
  M.indexedClassInclusions run.indices run.carrierUnion run.limitPointLabels run.limitPointRelation

theorem limitPointLabels_ground : run.limitPointLabels ∈ M.sets :=
  M.indexedCarrierLabels_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.carrierFamily_ground

theorem limitPointRelation_ground : run.limitPointRelation ∈ M.sets :=
  M.directLimitRelation_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.pointMapFamily_ground run.limitPointLabels_ground

theorem limitPoints_ground : run.limitPoints ∈ M.sets :=
  M.equivalenceClasses_mem powers separation run.limitPointLabels_ground run.limitPointRelation_ground

theorem limitPointMap_ground (i : I) : run.limitPointMap i ∈ M.sets :=
  M.indexedClassInclusion_mem pairing unions powers separation run.carrierUnion_ground
    run.limitPointLabels_ground run.limitPointRelation_ground
    (M.transitive run.indices_ground (ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitPointInclusions_ground : run.limitPointInclusions ∈ M.sets :=
  M.indexedClassInclusions_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPointLabels_ground run.limitPointRelation_ground

theorem limitPointMap_injection (i : I) :
    InjectionCode (run.diagram.stage i).stage.carrier run.limitPoints (run.limitPointMap i) :=
  run.pointPresentation.inclusion_injection i

theorem limitPointInclusions_function : FunctionGraphOn run.indices run.limitPointInclusions :=
  ⟨_, M.indexedClassInclusions_function pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPointLabels_ground run.limitPointRelation_ground⟩

theorem limitPointInclusions_entry (i : I) (f : ZFSet.{u}) :
    ZFSet.pair (run.key i) f ∈ run.limitPointInclusions ↔ f = run.limitPointMap i := by
  exact (M.indexedClassInclusions_entries pairing unions powers separation (T := run.indices)
    run.indices_ground run.carrierUnion_ground run.limitPointLabels_ground run.limitPointRelation_ground
    (run.key i) f).trans (and_iff_right (show run.key i ∈ run.indices from ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitPointMap_comp {i j : I} (before : i ≤ j) :
    relationCompose (run.diagram.stage i).stage.carrier (run.diagram.stage j).stage.carrier
      run.limitPoints (run.diagram.transition before).map.points
      (run.limitPointMap j) = run.limitPointMap i :=
  run.pointPresentation.inclusion_comp before

noncomputable def limitActorLabels : ZFSet.{u} :=
  indexedCarrierLabels run.indices run.actorUnion run.actorFamily

noncomputable def limitActorRelation : ZFSet.{u} :=
  directLimitRelation run.indices run.actorUnion run.actorMapFamily run.limitActorLabels

noncomputable def limitActors : ZFSet.{u} :=
  directLimitCarrier run.indices run.actorUnion run.actorFamily run.actorMapFamily

noncomputable def limitActorMap (i : I) : ZFSet.{u} :=
  directLimitInclusion run.indices run.actorUnion run.actorFamily run.actorMapFamily (run.key i)

noncomputable def limitActorInclusions : ZFSet.{u} :=
  M.indexedClassInclusions run.indices run.actorUnion run.limitActorLabels run.limitActorRelation

theorem limitActorLabels_ground : run.limitActorLabels ∈ M.sets :=
  M.indexedCarrierLabels_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorFamily_ground

theorem limitActorRelation_ground : run.limitActorRelation ∈ M.sets :=
  M.directLimitRelation_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorMapFamily_ground run.limitActorLabels_ground

theorem limitActors_ground : run.limitActors ∈ M.sets :=
  M.equivalenceClasses_mem powers separation run.limitActorLabels_ground run.limitActorRelation_ground

theorem limitActorMap_ground (i : I) : run.limitActorMap i ∈ M.sets :=
  M.indexedClassInclusion_mem pairing unions powers separation run.actorUnion_ground
    run.limitActorLabels_ground run.limitActorRelation_ground
    (M.transitive run.indices_ground (ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitActorInclusions_ground : run.limitActorInclusions ∈ M.sets :=
  M.indexedClassInclusions_mem pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.limitActorLabels_ground run.limitActorRelation_ground

theorem limitActorMap_injection (i : I) :
    InjectionCode (run.diagram.stage i).stage.actors run.limitActors (run.limitActorMap i) :=
  run.actorPresentation.inclusion_injection i

theorem limitActorInclusions_function : FunctionGraphOn run.indices run.limitActorInclusions :=
  ⟨_, M.indexedClassInclusions_function pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.limitActorLabels_ground run.limitActorRelation_ground⟩

theorem limitActorInclusions_entry (i : I) (f : ZFSet.{u}) :
    ZFSet.pair (run.key i) f ∈ run.limitActorInclusions ↔ f = run.limitActorMap i := by
  exact (M.indexedClassInclusions_entries pairing unions powers separation (T := run.indices)
    run.indices_ground run.actorUnion_ground run.limitActorLabels_ground run.limitActorRelation_ground
    (run.key i) f).trans (and_iff_right (show run.key i ∈ run.indices from ZFSet.mem_range.2 ⟨i, rfl⟩))

theorem limitActorMap_comp {i j : I} (before : i ≤ j) :
    relationCompose (run.diagram.stage i).stage.actors (run.diagram.stage j).stage.actors
      run.limitActors (run.diagram.transition before).map.actors
      (run.limitActorMap j) = run.limitActorMap i :=
  run.actorPresentation.inclusion_comp before

def LimitMul (g h k : ZFSet.{u}) : Prop :=
  ∃ i a b c, a ∈ (run.diagram.stage i).stage.actors ∧ b ∈ (run.diagram.stage i).stage.actors ∧
    c ∈ (run.diagram.stage i).stage.actors ∧ g = run.actorPresentation.limitPoint i a ∧
    h = run.actorPresentation.limitPoint i b ∧ k = run.actorPresentation.limitPoint i c ∧
    ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication

def LimitInv (g h : ZFSet.{u}) : Prop :=
  ∃ i a b, a ∈ (run.diagram.stage i).stage.actors ∧ b ∈ (run.diagram.stage i).stage.actors ∧
    g = run.actorPresentation.limitPoint i a ∧ h = run.actorPresentation.limitPoint i b ∧
    ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse

theorem limitMul_bounds {g h k : ZFSet.{u}} (mul : run.LimitMul g h k) :
    g ∈ run.limitActors ∧ h ∈ run.limitActors ∧ k ∈ run.limitActors := by
  obtain ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, _⟩ := mul
  exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb,
    run.actorPresentation.limitPoint_mem hc⟩

theorem limitInv_bounds {g h : ZFSet.{u}} (inv : run.LimitInv g h) :
    g ∈ run.limitActors ∧ h ∈ run.limitActors := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl, _⟩ := inv
  exact ⟨run.actorPresentation.limitPoint_mem ha, run.actorPresentation.limitPoint_mem hb⟩

theorem limitMul_total {g h : ZFSet.{u}} (hg : g ∈ run.limitActors) (hh : h ∈ run.limitActors) :
    ∃ k ∈ run.limitActors, run.LimitMul g h k := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl⟩ := run.actorPresentation.pair_coverage hg hh
  obtain ⟨c, entry, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
    (ZFSet.pair a b) (ZFSet.pair_mem_prod.2 ⟨ha, hb⟩)
  have hc := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 entry)).2
  exact ⟨run.actorPresentation.limitPoint i c, run.actorPresentation.limitPoint_mem hc,
    i, a, b, c, ha, hb, hc, rfl, rfl, rfl, entry⟩

theorem limitInv_total {g : ZFSet.{u}} (hg : g ∈ run.limitActors) :
    ∃ h ∈ run.limitActors, run.LimitInv g h := by
  obtain ⟨i, a, ha, rfl⟩ := run.actorPresentation.limitPoint_coverage hg
  obtain ⟨b, entry, _⟩ := (run.diagram.stage i).stage.group_code.inv_function.2 a ha
  have hb := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.inv_function.1 entry)).2
  exact ⟨run.actorPresentation.limitPoint i b, run.actorPresentation.limitPoint_mem hb,
    i, a, b, ha, hb, rfl, rfl, entry⟩

theorem limitMul_unique {g h k l : ZFSet.{u}}
    (first : run.LimitMul g h k) (second : run.LimitMul g h l) : k = l := by
  obtain ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, product⟩ := first
  obtain ⟨j, d, e, f, hd, he, hf, equalA, equalB, rfl, product'⟩ := second
  obtain ⟨m, im, jm⟩ := run.common_upper i j
  obtain ⟨a', aa'⟩ := run.actorSystem.map_entry_total im ha
  obtain ⟨b', bb'⟩ := run.actorSystem.map_entry_total im hb
  obtain ⟨c', cc'⟩ := run.actorSystem.map_entry_total im hc
  obtain ⟨d', dd'⟩ := run.actorSystem.map_entry_total jm hd
  obtain ⟨e', ee'⟩ := run.actorSystem.map_entry_total jm he
  obtain ⟨f', ff'⟩ := run.actorSystem.map_entry_total jm hf
  have sameA := (run.actorSystem.related_iff_common_images im jm aa' dd').1
    ((run.actorPresentation.limitPoint_eq_iff_related ha hd).1 equalA)
  have sameB := (run.actorSystem.related_iff_common_images im jm bb' ee').1
    ((run.actorPresentation.limitPoint_eq_iff_related hb he).1 equalB)
  subst d'
  subst e'
  have left := (run.diagram.transition im).map.group_embedding.mul a b c a' b' c' product aa' bb' cc'
  have right := (run.diagram.transition jm).map.group_embedding.mul d e f a' b' f' product' dd' ee' ff'
  have sameC : c' = f' :=
    (show FunctionGraphOn (ZFSet.prod (run.diagram.stage m).stage.actors (run.diagram.stage m).stage.actors)
      (run.diagram.stage m).stage.multiplication from
      ⟨_, (run.diagram.stage m).stage.group_code.mul_function⟩).unique left right
  apply (run.actorPresentation.limitPoint_eq_iff_related hc hf).2
  exact ⟨m, im, jm, c', cc', sameC.symm ▸ ff'⟩

theorem limitInv_unique {g h k : ZFSet.{u}}
    (first : run.LimitInv g h) (second : run.LimitInv g k) : h = k := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl, inverse⟩ := first
  obtain ⟨j, c, d, hc, hd, equal, rfl, inverse'⟩ := second
  obtain ⟨m, im, jm⟩ := run.common_upper i j
  obtain ⟨a', aa'⟩ := run.actorSystem.map_entry_total im ha
  obtain ⟨b', bb'⟩ := run.actorSystem.map_entry_total im hb
  obtain ⟨c', cc'⟩ := run.actorSystem.map_entry_total jm hc
  obtain ⟨d', dd'⟩ := run.actorSystem.map_entry_total jm hd
  have sameA := (run.actorSystem.related_iff_common_images im jm aa' cc').1
    ((run.actorPresentation.limitPoint_eq_iff_related ha hc).1 equal)
  subst c'
  have left := (run.diagram.transition im).map.group_embedding.map_inv
    (run.diagram.stage i).stage.group_code (run.diagram.stage m).stage.group_code inverse aa' bb'
  have right := (run.diagram.transition jm).map.group_embedding.map_inv
    (run.diagram.stage j).stage.group_code (run.diagram.stage m).stage.group_code inverse' cc' dd'
  have sameB : b' = d' :=
    (show FunctionGraphOn (run.diagram.stage m).stage.actors (run.diagram.stage m).stage.inverse from
      ⟨_, (run.diagram.stage m).stage.group_code.inv_function⟩).unique left right
  apply (run.actorPresentation.limitPoint_eq_iff_related hb hd).2
  exact ⟨m, im, jm, b', bb', sameB.symm ▸ dd'⟩

theorem limitMul_at (i : I) {a b c : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors)
    (hc : c ∈ (run.diagram.stage i).stage.actors) :
    run.LimitMul (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b)
      (run.actorPresentation.limitPoint i c) ↔
      ZFSet.pair (ZFSet.pair a b) c ∈ (run.diagram.stage i).stage.multiplication := by
  constructor
  · intro product
    obtain ⟨d, entry, _⟩ := (run.diagram.stage i).stage.group_code.mul_function.2
      (ZFSet.pair a b) (ZFSet.pair_mem_prod.2 ⟨ha, hb⟩)
    have hd := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.mul_function.1 entry)).2
    have canonical : run.LimitMul (run.actorPresentation.limitPoint i a)
        (run.actorPresentation.limitPoint i b) (run.actorPresentation.limitPoint i d) :=
      ⟨i, a, b, d, ha, hb, hd, rfl, rfl, rfl, entry⟩
    have equal := (run.actorPresentation.limitPoint_same_iff hc hd).1 (run.limitMul_unique product canonical)
    subst d
    exact entry
  · intro entry
    exact ⟨i, a, b, c, ha, hb, hc, rfl, rfl, rfl, entry⟩

theorem limitInv_at (i : I) {a b : ZFSet.{u}}
    (ha : a ∈ (run.diagram.stage i).stage.actors) (hb : b ∈ (run.diagram.stage i).stage.actors) :
    run.LimitInv (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i b) ↔
      ZFSet.pair a b ∈ (run.diagram.stage i).stage.inverse := by
  constructor
  · intro inverse
    obtain ⟨c, entry, _⟩ := (run.diagram.stage i).stage.group_code.inv_function.2 a ha
    have hc := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.group_code.inv_function.1 entry)).2
    have canonical : run.LimitInv (run.actorPresentation.limitPoint i a) (run.actorPresentation.limitPoint i c) :=
      ⟨i, a, c, ha, hc, rfl, rfl, entry⟩
    have equal := (run.actorPresentation.limitPoint_same_iff hb hc).1 (run.limitInv_unique inverse canonical)
    subst c
    exact entry
  · intro entry
    exact ⟨i, a, b, ha, hb, rfl, rfl, entry⟩

noncomputable def limitIdentity (i : I) : ZFSet.{u} :=
  run.actorPresentation.limitPoint i (run.diagram.stage i).stage.identity

theorem limitIdentity_mem (i : I) : run.limitIdentity i ∈ run.limitActors :=
  run.actorPresentation.limitPoint_mem (run.diagram.stage i).stage.group_code.identity_mem

theorem limitIdentity_eq (i j : I) : run.limitIdentity i = run.limitIdentity j := by
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  apply (run.actorPresentation.limitPoint_eq_iff_related
    (run.diagram.stage i).stage.group_code.identity_mem (run.diagram.stage j).stage.group_code.identity_mem).2
  exact ⟨k, ik, jk, (run.diagram.stage k).stage.identity,
    (run.diagram.transition ik).map.group_embedding.one, (run.diagram.transition jk).map.group_embedding.one⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
