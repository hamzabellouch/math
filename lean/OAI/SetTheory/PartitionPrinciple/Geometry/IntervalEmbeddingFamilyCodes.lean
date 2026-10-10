import OAI.SetTheory.PartitionPrinciple.Definability.IndexedAttachmentCodes
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundIntervalRecursion

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

def leastInjectionMember (A f d : ZFSet.{u}) : Prop :=
  d ∈ A ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair d n ∈ f ∧
    ∀ x ∈ A, ∀ m ∈ n, ZFSet.pair x m ∉ f

theorem leastInjectionMember_unique {A f d b : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f)
    (hd : leastInjectionMember A f d) (hb : leastInjectionMember A f b) : d = b := by
  obtain ⟨dA, n, hn, dn, leastD⟩ := hd
  obtain ⟨bA, m, hm, bm, leastB⟩ := hb
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastB d dA (natSetCode k) ((natSetCode_mem_iff k l).2 smaller) dn)
  · subst l
    exact injection.injective d b (natSetCode k) dn bm
  · exact False.elim (leastD b bA (natSetCode l) ((natSetCode_mem_iff l k).2 larger) bm)

theorem leastInjectionMember_exists_unique {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    ∃! d, leastInjectionMember A f d := by
  classical
  let valid : Nat → Prop := fun n => ∃ d ∈ A, ZFSet.pair d (natSetCode n) ∈ f
  have existsValid : ∃ n, valid n := by
    obtain ⟨d, hd⟩ := nonempty
    obtain ⟨n, entry, _⟩ := injection.function.2 d hd
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1
      (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    exact ⟨k, d, hd, entry⟩
  obtain ⟨d, hd, entry⟩ := Nat.find_spec existsValid
  have selected : leastInjectionMember A f d := by
    refine ⟨hd, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro x hx m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨x, hx, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨d, selected, fun b hb => leastInjectionMember_unique injection hb selected⟩

noncomputable def canonicalEnumerationDefault (A f : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ d, leastInjectionMember A f d then Classical.choose h else ∅

theorem canonicalEnumerationDefault_least {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    leastInjectionMember A f (canonicalEnumerationDefault A f) := by
  classical
  have existsDefault := (leastInjectionMember_exists_unique injection nonempty).exists
  simpa only [canonicalEnumerationDefault, dite_eq_left existsDefault] using Classical.choose_spec existsDefault

theorem canonicalEnumerationDefault_eq {A f d : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (hd : leastInjectionMember A f d) :
    canonicalEnumerationDefault A f = d :=
  leastInjectionMember_unique injection (canonicalEnumerationDefault_least injection ⟨d, hd.1⟩) hd

noncomputable def canonicalEnumeration (A f : ZFSet.{u}) : ZFSet.{u} :=
  defaultInverse A ZFSet.omega f (canonicalEnumerationDefault A f)

theorem canonicalEnumeration_eq_of_least {A f d : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (hd : leastInjectionMember A f d) :
    canonicalEnumeration A f = defaultInverse A ZFSet.omega f d := by
  rw [canonicalEnumeration, canonicalEnumerationDefault_eq injection hd]

theorem canonicalEnumeration_isFunc {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    ZFSet.IsFunc ZFSet.omega A (canonicalEnumeration A f) :=
  defaultInverse_isFunc injection (canonicalEnumerationDefault_least injection nonempty).1

theorem canonicalEnumeration_onto {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) :
    ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ canonicalEnumeration A f :=
  defaultInverse_onto injection (canonicalEnumerationDefault A f)

theorem canonicalEnumeration_unique {A f d e : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (hd : leastInjectionMember A f d)
    (he : e = defaultInverse A ZFSet.omega f d) : e = canonicalEnumeration A f :=
  he.trans (canonicalEnumeration_eq_of_least injection hd).symm

namespace BoundedFormula

def leastInjectionMemberFormula {n} (d a f omega : Fin n) : BoundedFormula n :=
  .conj (.mem d a) (exMem omega
    (.conj (pairMembershipFormula d.succ 0 f.succ)
      (.allMem a.succ (.allMem 1 (.neg (pairMembershipFormula 1 0 f.succ.succ.succ))))))

theorem truth_leastInjectionMemberFormula {n} (d a f omega : Fin n)
    (env : Fin n → ZFSet.{u}) (hOmega : env omega = ZFSet.omega) :
    Truth (leastInjectionMemberFormula d a f omega) env ↔
      leastInjectionMember (env a) (env f) (env d) := by
  simp only [leastInjectionMemberFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  change (env d ∈ env a ∧ ∃ n ∈ env omega, ZFSet.pair (env d) n ∈ env f ∧
    ∀ x ∈ env a, ∀ m ∈ n, ZFSet.pair x m ∉ env f) ↔ _
  rw [hOmega]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem canonicalEnumerationDefault_mem {A f : ZFSet.{u}} (hA : A ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumerationDefault A f ∈ M.sets :=
  M.transitive hA (canonicalEnumerationDefault_least injection nonempty).1

theorem canonicalEnumeration_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumeration A f ∈ M.sets :=
  M.defaultInverse_mem pairing unions powers separation hA hOmega hf
    (M.canonicalEnumerationDefault_mem hA injection nonempty)

theorem canonicalEnumeration_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumerationDefault A f ∈ M.sets ∧
      leastInjectionMember A f (canonicalEnumerationDefault A f) ∧
      canonicalEnumeration A f ∈ M.sets ∧
      ZFSet.IsFunc ZFSet.omega A (canonicalEnumeration A f) ∧
      (∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ canonicalEnumeration A f) ∧
      ∀ d e, leastInjectionMember A f d → e = defaultInverse A ZFSet.omega f d →
        d = canonicalEnumerationDefault A f ∧ e = canonicalEnumeration A f :=
  ⟨M.canonicalEnumerationDefault_mem hA injection nonempty,
    canonicalEnumerationDefault_least injection nonempty,
    M.canonicalEnumeration_mem pairing unions powers separation hA hf hOmega injection nonempty,
    canonicalEnumeration_isFunc injection nonempty, canonicalEnumeration_onto injection,
    fun _ _ hd he => ⟨(canonicalEnumerationDefault_eq injection hd).symm,
      canonicalEnumeration_unique injection hd he⟩⟩

end TransitiveGround






noncomputable def intervalSequenceGraph (A D e t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ a ∈ A, ∃ q ∈ D,
    z = ZFSet.pair a q ∧ ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t)
    (ZFSet.prod A D)

theorem intervalSequenceGraph_subset (A D e t : ZFSet.{u}) :
    intervalSequenceGraph A D e t ⊆ ZFSet.prod A D :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_intervalSequenceGraph (A D e t z : ZFSet.{u}) :
    z ∈ intervalSequenceGraph A D e t ↔
      ∃ n ∈ ZFSet.omega, ∃ a ∈ A, ∃ q ∈ D,
        z = ZFSet.pair a q ∧ ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨n, hn, a, ha, q, hq, rfl, en, tn⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ha, hq⟩, n, hn, a, ha, q, hq, rfl, en, tn⟩

theorem pair_mem_intervalSequenceGraph (A D e t a q : ZFSet.{u}) :
    ZFSet.pair a q ∈ intervalSequenceGraph A D e t ↔
      a ∈ A ∧ q ∈ D ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t := by
  rw [mem_intervalSequenceGraph]
  constructor
  · rintro ⟨n, hn, b, hb, z, hz, equal, en, tn⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hb, hz, n, hn, en, tn⟩
  · rintro ⟨ha, hq, n, hn, en, tn⟩
    exact ⟨n, hn, a, ha, q, hq, rfl, en, tn⟩

theorem intervalSequenceGraph_isFunc {A D rA rD e lo hi t : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    ZFSet.IsFunc A D (intervalSequenceGraph A D e t) := by
  refine ⟨intervalSequenceGraph_subset A D e t, ?_⟩
  intro a ha
  obtain ⟨n, hn, en⟩ := onto a ha
  obtain ⟨q, tn, _⟩ := code.function.2 n hn
  have hq := (ZFSet.pair_mem_prod.1 (code.function.1 tn)).2
  refine ⟨q, (pair_mem_intervalSequenceGraph A D e t a q).2 ⟨ha, hq, n, hn, en, tn⟩, ?_⟩
  intro z hz
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t a z).1 hz
  exact (code.agree m n a a z q em en tm tn).1 rfl

theorem intervalSequenceGraph_injection {A D rA rD e lo hi t : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    InjectionCode A D (intervalSequenceGraph A D e t) := by
  refine ⟨intervalSequenceGraph_isFunc code onto, ?_⟩
  intro a b q ha hb
  obtain ⟨_, _, n, _, en, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 ha
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t b q).1 hb
  exact (code.agree n m a b q q en em tn tm).2 rfl

theorem intervalSequenceGraph_order_iff {A D rA rD e lo hi t a b q z : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (ha : ZFSet.pair a q ∈ intervalSequenceGraph A D e t)
    (hb : ZFSet.pair b z ∈ intervalSequenceGraph A D e t) :
    ZFSet.pair q z ∈ rD ↔ ZFSet.pair a b ∈ rA := by
  obtain ⟨_, _, n, _, en, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 ha
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t b z).1 hb
  exact (code.order n m a b q z en em tn tm).symm

theorem intervalSequenceGraph_inside {A D rA rD e lo hi t a q : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (entry : ZFSet.pair a q ∈ intervalSequenceGraph A D e t) :
    ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD := by
  obtain ⟨_, _, n, _, _, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 entry
  exact code.inside n q tn

theorem intervalSequenceGraph_sequence_entry {A D rA rD e lo hi t n a q : ZFSet.{u}}
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (en : ZFSet.pair n a ∈ e) (tn : ZFSet.pair n q ∈ t) :
    ZFSet.pair a q ∈ intervalSequenceGraph A D e t := by
  have eshape := ZFSet.pair_mem_prod.1 (enumeration.1 en)
  have tshape := ZFSet.pair_mem_prod.1 (code.function.1 tn)
  exact (pair_mem_intervalSequenceGraph A D e t a q).2 ⟨eshape.2, tshape.2, n, eshape.1, en, tn⟩






namespace BoundedFormula

open SetFormula

def intervalSequenceEntryFormula {n} (z a d e t omega : Fin n) : BoundedFormula n :=
  exMem omega (exMem a.succ (exMem d.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 1 0)
      (.conj (pairMembershipFormula 2 1 e.succ.succ.succ)
        (pairMembershipFormula 2 0 t.succ.succ.succ)))))

theorem truth_intervalSequenceEntryFormula {n} (z a d e t omega : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalSequenceEntryFormula z a d e t omega) env ↔
      ∃ i ∈ env omega, ∃ x ∈ env a, ∃ q ∈ env d,
        env z = ZFSet.pair x q ∧ ZFSet.pair i x ∈ env e ∧ ZFSet.pair i q ∈ env t := by
  simp only [intervalSequenceEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem intervalSequenceGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A D e t : ZFSet.{u}} (hA : A ∈ M.sets) (hD : D ∈ M.sets)
    (he : e ∈ M.sets) (ht : t ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets) :
    intervalSequenceGraph A D e t ∈ M.sets := by
  let params := extend A (extend D (extend e (extend t (extend ZFSet.omega Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalSequenceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hA (Fin.cases hD (Fin.cases he (Fin.cases ht
      (Fin.cases hOmega (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalSequenceEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod A D) = intervalSequenceGraph A D e t := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, intervalSequenceGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_intervalSequenceEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem intervalSequenceDescent_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A D rA rD e lo hi t : ZFSet.{u}} (hA : A ∈ M.sets) (hD : D ∈ M.sets)
    (he : e ∈ M.sets) (ht : t ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    intervalSequenceGraph A D e t ∈ M.sets ∧
      InjectionCode A D (intervalSequenceGraph A D e t) ∧
      (∀ a q, ZFSet.pair a q ∈ intervalSequenceGraph A D e t →
        ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD) ∧
      (∀ a b q z, ZFSet.pair a q ∈ intervalSequenceGraph A D e t →
        ZFSet.pair b z ∈ intervalSequenceGraph A D e t →
        (ZFSet.pair q z ∈ rD ↔ ZFSet.pair a b ∈ rA)) :=
  ⟨M.intervalSequenceGraph_mem pairing unions powers separation hA hD he ht hOmega,
    intervalSequenceGraph_injection code onto,
    fun _ _ entry => intervalSequenceGraph_inside code entry,
    fun _ _ _ _ left right => intervalSequenceGraph_order_iff code left right⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula SetRealization Compression.RecursiveMaps.RationalHeights
universe u

structure IntervalEmbeddingCode (A D rA rD lo hi f : ZFSet.{u}) : Prop where
  injection : InjectionCode A D f
  order : ∀ a b q z, ZFSet.pair a q ∈ f → ZFSet.pair b z ∈ f →
    (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD)
  inside : ∀ a q, ZFSet.pair a q ∈ f → ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD

theorem intervalEmbeddingCode_empty (D rA rD lo hi : ZFSet.{u}) :
    IntervalEmbeddingCode ∅ D rA rD lo hi ∅ := by
  refine ⟨⟨⟨ZFSet.empty_subset _, fun a ha => False.elim (ZFSet.notMem_empty a ha)⟩, ?_⟩, ?_, ?_⟩
  · intro a b q entry _
    exact False.elim (ZFSet.notMem_empty _ entry)
  · intro a b q z entry _
    exact False.elim (ZFSet.notMem_empty _ entry)
  · intro a q entry
    exact False.elim (ZFSet.notMem_empty _ entry)

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem exists_intervalEmbedding_of_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD e lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (he : e ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA rD lo hi f := by
  obtain ⟨t, ht, sequence, _, _⟩ := M.exists_ground_intervalSequence
    pairing unions separation collection infinite hA hD hrA hrD he hc
    source target injection enumeration loD hiD gap
  obtain ⟨member, inj, inside, order⟩ := M.intervalSequenceDescent_spec
    pairing unions powers separation hA hD he ht (M.omega_mem separation infinite) sequence onto
  exact ⟨intervalSequenceGraph A D e t, member, inj,
    fun a b q z first second => (order a b q z first second).symm, inside⟩

theorem exists_intervalEmbedding
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (small : M.groundEmbeddable A ZFSet.omega)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA rD lo hi f := by
  by_cases nonempty : A.Nonempty
  · obtain ⟨sourceCode, hSourceCode, sourceInjection⟩ := small
    have he := M.canonicalEnumeration_mem pairing unions powers separation
      hA hSourceCode (M.omega_mem separation infinite) sourceInjection nonempty
    have enumeration := canonicalEnumeration_isFunc sourceInjection nonempty
    have onto := canonicalEnumeration_onto sourceInjection
    exact M.exists_intervalEmbedding_of_enumeration pairing unions powers separation collection infinite
      hA hD hrA hrD he hc source target injection enumeration onto loD hiD gap
  · have empty : A = ∅ := by
      apply ZFSet.ext
      intro a
      exact ⟨fun ha => False.elim (nonempty ⟨a, ha⟩), fun ha => False.elim (ZFSet.notMem_empty a ha)⟩
    exact ⟨∅, M.empty_mem ⟨D, hD⟩, empty ▸ intervalEmbeddingCode_empty D rA rD lo hi⟩

theorem exists_groundRationalIntervals
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    ∃ D ∈ M.sets, ∃ r ∈ M.sets, ∃ c ∈ M.sets,
      InjectionCode D ZFSet.omega c ∧ DenseOrderCode D r ∧ (∃ x, x ∈ D) ∧
      (∀ x ∈ D, (∃ y ∈ D, ZFSet.pair y x ∈ r) ∧ (∃ y ∈ D, ZFSet.pair x y ∈ r)) ∧
      (∃ s : Presentation (ULift.{u} Rational), s.carrier = D ∧
        ∀ a b, ZFSet.pair (s.encode a) (s.encode b) ∈ r ↔ Rational.lt a.down b.down) ∧
      ∀ A ∈ M.sets, ∀ rA ∈ M.sets, StrictLinearOrderCode A rA →
        M.groundEmbeddable A ZFSet.omega → ∀ lo ∈ D, ∀ hi ∈ D,
          ZFSet.pair lo hi ∈ r → ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA r lo hi f := by
  obtain ⟨D, hD, r, hr, c, hc, injection, target, nonempty, endpoints, s, carrier, order⟩ :=
    M.exists_groundRationals pairing unions powers separation infinite
  refine ⟨D, hD, r, hr, c, hc, injection, target, nonempty, endpoints, ⟨s, carrier, order⟩, ?_⟩
  intro A hA rA hrA source small lo hlo hi hhi gap
  exact M.exists_intervalEmbedding pairing unions powers separation collection infinite
    hA hD hrA hr hc source target injection small hlo hhi gap

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

structure IntervalEmbeddingFamilyInputs (I As rs los his D rD : ZFSet.{u}) : Prop where
  sources : FunctionGraphOn I As
  orders : FunctionGraphOn I rs
  lows : FunctionGraphOn I los
  highs : FunctionGraphOn I his
  source_order : ∀ i, StrictLinearOrderCode (sources.value i) (orders.value i)
  lower_mem : ∀ i, lows.value i ∈ D
  upper_mem : ∀ i, highs.value i ∈ D
  gap : ∀ i, ZFSet.pair (lows.value i) (highs.value i) ∈ rD

def intervalEmbeddingCandidate (As rs los his D rD i f : ZFSet.{u}) : Prop :=
  ∃ A ∈ ⋃₀ ⋃₀ As, ∃ rA ∈ ⋃₀ ⋃₀ rs, ∃ lo ∈ D, ∃ hi ∈ D,
    ZFSet.pair i A ∈ As ∧ ZFSet.pair i rA ∈ rs ∧
    ZFSet.pair i lo ∈ los ∧ ZFSet.pair i hi ∈ his ∧
    IntervalEmbeddingCode A D rA rD lo hi f

noncomputable def intervalEmbeddingRelation (I W As rs los his D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ W, z = ZFSet.pair i f ∧
    intervalEmbeddingCandidate As rs los his D rD i f) (ZFSet.prod I W)

theorem pair_mem_intervalEmbeddingRelation (I W As rs los his D rD i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ intervalEmbeddingRelation I W As rs los his D rD ↔
      i ∈ I ∧ f ∈ W ∧ intervalEmbeddingCandidate As rs los his D rD i f := by
  rw [intervalEmbeddingRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hf⟩, j, _, g, _, equal, valid⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hf, valid⟩
  · rintro ⟨hi, hf, valid⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, valid⟩

namespace IntervalEmbeddingFamilyInputs

variable {I As rs los his D rD : ZFSet.{u}}
    (d : IntervalEmbeddingFamilyInputs I As rs los his D rD)

theorem candidate_iff (i : {i : ZFSet.{u} // i ∈ I}) (f : ZFSet.{u}) :
    intervalEmbeddingCandidate As rs los his D rD i.val f ↔
      IntervalEmbeddingCode (d.sources.value i) D (d.orders.value i) rD
        (d.lows.value i) (d.highs.value i) f := by
  constructor
  · rintro ⟨A, _, rA, _, lo, _, hi, _, entryA, entryR, entryLo, entryHi, code⟩
    have eA := d.sources.value_eq_of_entry i entryA
    have eR := d.orders.value_eq_of_entry i entryR
    have eLo := d.lows.value_eq_of_entry i entryLo
    have eHi := d.highs.value_eq_of_entry i entryHi
    rw [eA, eR, eLo, eHi]
    exact code
  · intro code
    exact ⟨d.sources.value i, d.sources.value_mem_doubleUnion i,
      d.orders.value i, d.orders.value_mem_doubleUnion i,
      d.lows.value i, d.lower_mem i, d.highs.value i, d.upper_mem i,
      d.sources.value_entry i, d.orders.value_entry i,
      d.lows.value_entry i, d.highs.value_entry i, code⟩

theorem embedding_subset_bound (i : {i : ZFSet.{u} // i ∈ I}) {f : ZFSet.{u}}
    (code : IntervalEmbeddingCode (d.sources.value i) D (d.orders.value i) rD
      (d.lows.value i) (d.highs.value i) f) :
    f ⊆ ZFSet.prod (familyPointBound As) D := by
  intro z hz
  obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 (code.injection.function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨mem_familyPointBound_of_entry (d.sources.value_entry i) ha, hq⟩

end IntervalEmbeddingFamilyInputs

end PartitionPilot.Forcing

end OAI
