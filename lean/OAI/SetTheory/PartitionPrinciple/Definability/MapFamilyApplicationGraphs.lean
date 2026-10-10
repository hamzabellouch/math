import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

noncomputable def indexedRelationSection (B C R i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ B, ∃ y ∈ C,
    z = ZFSet.pair q y ∧ ZFSet.pair (ZFSet.pair i q) y ∈ R) (ZFSet.prod B C)

theorem indexedRelationSection_subset (B C R i : ZFSet.{u}) :
    indexedRelationSection B C R i ⊆ ZFSet.prod B C :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedRelationSection (B C R i z : ZFSet.{u}) :
    z ∈ indexedRelationSection B C R i ↔ ∃ q ∈ B, ∃ y ∈ C,
      z = ZFSet.pair q y ∧ ZFSet.pair (ZFSet.pair i q) y ∈ R := by
  constructor
  · intro hz
    exact (ZFSet.mem_sep.1 hz).2
  · rintro ⟨q, hq, y, hy, rfl, entry⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hq, hy⟩, q, hq, y, hy, rfl, entry⟩

theorem pair_mem_indexedRelationSection (B C R i q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ indexedRelationSection B C R i ↔
      q ∈ B ∧ y ∈ C ∧ ZFSet.pair (ZFSet.pair i q) y ∈ R := by
  rw [mem_indexedRelationSection]
  constructor
  · rintro ⟨q', hq, y', hy, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hq, hy, entry⟩
  · rintro ⟨hq, hy, entry⟩
    exact ⟨q, hq, y, hy, rfl, entry⟩






namespace BoundedFormula

open SetFormula

def indexedRelationSectionEntryFormula {n} (z i b c r : Fin n) : BoundedFormula n :=
  exMem b (exMem c.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tripleMembershipFormula i.succ.succ 1 0 r.succ.succ)))

theorem truth_indexedRelationSectionEntryFormula {n} (z i b c r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedRelationSectionEntryFormula z i b c r) env ↔
      env z ∈ indexedRelationSection (env b) (env c) (env r) (env i) := by
  simp only [indexedRelationSectionEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_tripleMembershipFormula, mem_indexedRelationSection]
  rfl

def indexedRelationSectionFormula {n} (f i b c r : Fin n) : BoundedFormula n :=
  .conj (.allMem f (indexedRelationSectionEntryFormula 0 i.succ b.succ c.succ r.succ))
    (.allMem b (.allMem c.succ
      (imp (tripleMembershipFormula i.succ.succ 1 0 r.succ.succ)
        (pairMembershipFormula 1 0 f.succ.succ))))

theorem truth_indexedRelationSectionFormula {n} (f i b c r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedRelationSectionFormula f i b c r) env ↔
      env f = indexedRelationSection (env b) (env c) (env r) (env i) := by
  simp only [indexedRelationSectionFormula, Truth, truth_indexedRelationSectionEntryFormula,
    truth_imp, truth_tripleMembershipFormula, truth_pairMembershipFormula]
  constructor
  · rintro ⟨subset, complete⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    intro hz
    obtain ⟨q, hq, y, hy, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ z).1 hz
    exact complete q hq y hy entry
  · intro equal
    refine ⟨fun _ hz => equal ▸ hz, ?_⟩
    intro q hq y hy entry
    change ZFSet.pair q y ∈ env f
    rw [equal]
    exact (pair_mem_indexedRelationSection _ _ _ _ q y).2 ⟨hq, hy, entry⟩

def indexedRelationFamilyEntryFormula {n} (z domain bound b c r : Fin n) : BoundedFormula n :=
  exMem domain (exMem bound.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (indexedRelationSectionFormula 0 1 b.succ.succ c.succ.succ r.succ.succ)))

theorem truth_indexedRelationFamilyEntryFormula {n} (z domain bound b c r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedRelationFamilyEntryFormula z domain bound b c r) env ↔
      ∃ i ∈ env domain, ∃ f ∈ env bound, env z = ZFSet.pair i f ∧
        f = indexedRelationSection (env b) (env c) (env r) i := by
  simp only [indexedRelationFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_indexedRelationSectionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem indexedRelationSection_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {B C R i : ZFSet.{u}} (hB : B ∈ M.sets) (hC : C ∈ M.sets)
    (hR : R ∈ M.sets) (hi : i ∈ M.sets) : indexedRelationSection B C R i ∈ M.sets := by
  let params := extend i (extend B (extend C (extend R Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedRelationSectionEntryFormula 0 1 2 3 4) params
    (Fin.cases hi (Fin.cases hB (Fin.cases hC (Fin.cases hR (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hB hC)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedRelationSectionEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod B C) = indexedRelationSection B C R i := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedRelationSectionEntryFormula]
    exact ⟨And.right, fun hz => ⟨indexedRelationSection_subset B C R i hz, hz⟩⟩
  exact equal ▸ selected

noncomputable def indexedRelationSections (I B C R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ M.groundRelations B C,
    z = ZFSet.pair i f ∧ f = indexedRelationSection B C R i)
    (ZFSet.prod I (M.groundRelations B C))

theorem pair_mem_indexedRelationSections (I B C R i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.indexedRelationSections I B C R ↔
      i ∈ I ∧ f ∈ M.groundRelations B C ∧ f = indexedRelationSection B C R i := by
  rw [indexedRelationSections, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hf⟩, j, _, g, _, equal, sectionEq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hf, sectionEq⟩
  · rintro ⟨hi, hf, sectionEq⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, sectionEq⟩

theorem indexedRelationSections_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B C R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hR : R ∈ M.sets) : M.indexedRelationSections I B C R ∈ M.sets := by
  have bound := M.groundRelations_mem pairing unions powers separation hB hC
  let params := extend I (extend (M.groundRelations B C) (extend B (extend C (extend R Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedRelationFamilyEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases bound (Fin.cases hB (Fin.cases hC
      (Fin.cases hR (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation hI bound)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedRelationFamilyEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod I (M.groundRelations B C)) = M.indexedRelationSections I B C R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedRelationSections, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedRelationFamilyEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem indexedRelationSections_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B C R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hR : R ∈ M.sets) :
    ZFSet.IsFunc I (M.groundRelations B C) (M.indexedRelationSections I B C R) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  have sectionBound := (M.mem_groundRelations B C (indexedRelationSection B C R i)).2
    ⟨M.indexedRelationSection_mem pairing unions powers separation hB hC hR (M.transitive hI hi),
      indexedRelationSection_subset B C R i⟩
  exact ⟨indexedRelationSection B C R i,
    (M.pair_mem_indexedRelationSections I B C R i _).2 ⟨hi, sectionBound, rfl⟩,
    fun f hf => ((M.pair_mem_indexedRelationSections I B C R i f).1 hf).2.2⟩

theorem indexedRelationSections_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B C R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hR : R ∈ M.sets) :
    M.indexedRelationSections I B C R ∈ M.sets ∧
      ZFSet.IsFunc I (M.groundRelations B C) (M.indexedRelationSections I B C R) ∧
      ∀ i f, ZFSet.pair i f ∈ M.indexedRelationSections I B C R ↔
        i ∈ I ∧ f = indexedRelationSection B C R i := by
  have func := M.indexedRelationSections_function pairing unions powers separation hI hB hC hR
  refine ⟨M.indexedRelationSections_mem pairing unions powers separation hI hB hC hR, func, ?_⟩
  intro i f
  constructor
  · intro entry
    have parts := (M.pair_mem_indexedRelationSections I B C R i f).1 entry
    exact ⟨parts.1, parts.2.2⟩
  · rintro ⟨hi, rfl⟩
    obtain ⟨g, entry, _⟩ := func.2 i hi
    have equal := ((M.pair_mem_indexedRelationSections I B C R i g).1 entry).2.2
    exact equal ▸ entry

end TransitiveGround

end



open SetFormula
universe u

noncomputable def indexedCarrierLabels (T U A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ T, ∃ X ∈ ZFSet.sUnion (ZFSet.sUnion A), ∃ x ∈ X,
    z = ZFSet.pair i x ∧ ZFSet.pair i X ∈ A) (ZFSet.prod T U)

theorem indexedCarrierLabels_subset (T U A : ZFSet.{u}) :
    indexedCarrierLabels T U A ⊆ ZFSet.prod T U :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedCarrierLabels (T U A z : ZFSet.{u}) :
    z ∈ indexedCarrierLabels T U A ↔
      ∃ i ∈ T, ∃ X ∈ ZFSet.sUnion (ZFSet.sUnion A), ∃ x ∈ X,
        x ∈ U ∧ z = ZFSet.pair i x ∧ ZFSet.pair i X ∈ A := by
  constructor
  · intro hz
    obtain ⟨bound, i, hi, X, hX, x, hx, rfl, entry⟩ := ZFSet.mem_sep.1 hz
    exact ⟨i, hi, X, hX, x, hx, (ZFSet.pair_mem_prod.1 bound).2, rfl, entry⟩
  · rintro ⟨i, hi, X, hX, x, hx, hu, rfl, entry⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hu⟩, i, hi, X, hX, x, hx, rfl, entry⟩

theorem pair_mem_indexedCarrierLabels (T U A i x : ZFSet.{u}) :
    ZFSet.pair i x ∈ indexedCarrierLabels T U A ↔
      i ∈ T ∧ x ∈ U ∧ ∃ X, ZFSet.pair i X ∈ A ∧ x ∈ X := by
  rw [mem_indexedCarrierLabels]
  constructor
  · rintro ⟨j, hj, X, _, y, hy, hu, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hu, X, entry, hy⟩
  · rintro ⟨hi, hu, X, entry, hx⟩
    exact ⟨i, hi, X, pair_second_mem_doubleUnion entry, x, hx, hu, rfl, entry⟩

theorem pair_mem_indexedCarrierLabels_of_entry {T U A i X x : ZFSet.{u}}
    (family : FunctionGraphOn T A) (entry : ZFSet.pair i X ∈ A) (bound : X ⊆ U) :
    ZFSet.pair i x ∈ indexedCarrierLabels T U A ↔ x ∈ X := by
  rw [pair_mem_indexedCarrierLabels]
  constructor
  · rintro ⟨_, _, Y, other, hx⟩
    exact (family.unique other entry) ▸ hx
  · intro hx
    exact ⟨family.pair_source entry, bound hx, X, entry, hx⟩

namespace BoundedFormula

def indexedCarrierLabelFormula {n} (z T U A V : Fin n) : BoundedFormula n :=
  exMem T (exMem V.succ (exMem 0
    (.conj (.mem 0 U.succ.succ.succ)
      (.conj (orderedPairFormula z.succ.succ.succ 2 0)
        (pairMembershipFormula 2 1 A.succ.succ.succ)))))

theorem truth_indexedCarrierLabelFormula {n} (z T U A V : Fin n)
    (env : Fin n → ZFSet.{u}) (bound : env V = ZFSet.sUnion (ZFSet.sUnion (env A))) :
    Truth (indexedCarrierLabelFormula z T U A V) env ↔
      env z ∈ indexedCarrierLabels (env T) (env U) (env A) := by
  simp only [indexedCarrierLabelFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∃ i ∈ env T, ∃ X ∈ env V, ∃ x ∈ X,
    x ∈ env U ∧ env z = ZFSet.pair i x ∧ ZFSet.pair i X ∈ env A) ↔ _
  rw [bound, mem_indexedCarrierLabels]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedCarrierLabels_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U A : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets) :
    indexedCarrierLabels T U A ∈ M.sets := by
  have hV := M.union_mem unions (M.union_mem unions hA)
  let params := extend T (extend U (extend A (extend (ZFSet.sUnion (ZFSet.sUnion A)) Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedCarrierLabelFormula 0 1 2 3 4) params
    (Fin.cases hT (Fin.cases hU (Fin.cases hA (Fin.cases hV (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hT hU)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedCarrierLabelFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod T U) = indexedCarrierLabels T U A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedCarrierLabelFormula 0 1 2 3 4 _ rfl]
    exact ⟨And.right, fun hz => ⟨indexedCarrierLabels_subset T U A hz, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround





noncomputable def mapFamilyApplicationGraph (I P Q family : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ x ∈ P, ∃ y ∈ Q, ∃ f ∈ ZFSet.sUnion (ZFSet.sUnion family),
    z = ZFSet.pair (ZFSet.pair i x) y ∧ ZFSet.pair i f ∈ family ∧ ZFSet.pair x y ∈ f)
    (ZFSet.prod (ZFSet.prod I P) Q)

theorem pair_mem_mapFamilyApplicationGraph (I P Q family i x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) y ∈ mapFamilyApplicationGraph I P Q family ↔
      i ∈ I ∧ x ∈ P ∧ y ∈ Q ∧ ∃ f, ZFSet.pair i f ∈ family ∧ ZFSet.pair x y ∈ f := by
  rw [mapFamilyApplicationGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, a, ha, b, hb, f, _, equal, indexed, entry⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    exact ⟨hj, ha, hb, f, indexed, entry⟩
  · rintro ⟨hi, hx, hy, f, indexed, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩,
      i, hi, x, hx, y, hy, f, pair_second_mem_doubleUnion indexed, rfl, indexed, entry⟩

namespace BoundedFormula

def mapFamilyApplicationEntryFormula {n} (z I P Q B family : Fin n) : BoundedFormula n :=
  exMem I (exMem P.succ (exMem Q.succ.succ (exMem B.succ.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ.succ 3 2 1)
      (.conj (pairMembershipFormula 3 0 family.succ.succ.succ.succ)
        (pairMembershipFormula 2 1 0))))))

theorem truth_mapFamilyApplicationEntryFormula {n} (z I P Q B family : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mapFamilyApplicationEntryFormula z I P Q B family) env ↔
      ∃ i ∈ env I, ∃ x ∈ env P, ∃ y ∈ env Q, ∃ f ∈ env B,
        env z = ZFSet.pair (ZFSet.pair i x) y ∧
          ZFSet.pair i f ∈ env family ∧ ZFSet.pair x y ∈ f := by
  simp only [mapFamilyApplicationEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mapFamilyApplicationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Q family : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQ : Q ∈ M.sets) (hFamily : family ∈ M.sets) :
    mapFamilyApplicationGraph I P Q family ∈ M.sets := by
  have hB := M.union_mem unions (M.union_mem unions hFamily)
  let params := extend I (extend P (extend Q (extend (ZFSet.sUnion (ZFSet.sUnion family)) (extend family Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQ (Fin.cases hB (Fin.cases hFamily
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hI hP) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod I P) Q) = mapFamilyApplicationGraph I P Q family := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mapFamilyApplicationGraph, ZFSet.mem_sep,
      BoundedFormula.truth_mapFamilyApplicationEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround


end PartitionPilot.Forcing

end OAI
