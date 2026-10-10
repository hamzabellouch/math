import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIntervalSelection

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

structure IntervalSequenceCode (N A D rA rD e lo hi t : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc N D t
  inside : ∀ i q, ZFSet.pair i q ∈ t → ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD
  agree : ∀ i j a b q z, ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
    ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t → (a = b ↔ q = z)
  order : ∀ i j a b q z, ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
    ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t →
      (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD)

def intervalNextCandidate (N A D rA rD e lo hi p y : ZFSet.{u}) : Prop :=
  y ∈ D ∧ ZFSet.pair lo y ∈ rD ∧ ZFSet.pair y hi ∈ rD ∧
    ∀ i ∈ N, ∀ a ∈ A, ∀ b ∈ A, ∀ z ∈ D,
      ZFSet.pair i a ∈ e → ZFSet.pair N b ∈ e → ZFSet.pair i z ∈ p →
        ((a = b ↔ z = y) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair z y ∈ rD) ∧
          (ZFSet.pair b a ∈ rA ↔ ZFSet.pair y z ∈ rD))

theorem pair_mem_intervalSequenceInsert (N p y i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ insert (ZFSet.pair N y) p ↔
      (i = N ∧ q = y) ∨ ZFSet.pair i q ∈ p := by
  rw [ZFSet.mem_insert_iff, ZFSet.pair_inj]

namespace IntervalSequenceCode

theorem empty (A D rA rD e lo hi : ZFSet.{u}) : IntervalSequenceCode ∅ A D rA rD e lo hi ∅ := by
  refine ⟨⟨ZFSet.empty_subset _, fun i hi => False.elim (ZFSet.notMem_empty i hi)⟩, ?_, ?_, ?_⟩
  · intro i q h
    exact False.elim (ZFSet.notMem_empty _ h)
  · intro i j a b q z _ _ h _
    exact False.elim (ZFSet.notMem_empty _ h)
  · intro i j a b q z _ _ h _
    exact False.elim (ZFSet.notMem_empty _ h)

theorem restrict {N A D rA rD e lo hi t B : ZFSet.{u}}
    (code : IntervalSequenceCode N A D rA rD e lo hi t) (subset : B ⊆ N) :
    IntervalSequenceCode B A D rA rD e lo hi (graphRestriction B t) := by
  have function : FunctionGraphOn N t := ⟨D, code.function⟩
  refine ⟨⟨?_, (function.restrict subset).to_isFunc.2⟩, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, q, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hi, (ZFSet.pair_mem_prod.1 (code.function.1 entry)).2⟩
  · intro i q entry
    exact code.inside i q (pair_mem_graphRestriction.1 entry).1
  · intro i j a b q z ea eb qi zj
    exact code.agree i j a b q z ea eb
      (pair_mem_graphRestriction.1 qi).1 (pair_mem_graphRestriction.1 zj).1
  · intro i j a b q z ea eb qi zj
    exact code.order i j a b q z ea eb
      (pair_mem_graphRestriction.1 qi).1 (pair_mem_graphRestriction.1 zj).1

theorem insert {N A D rA rD e lo hi p y : ZFSet.{u}}
    (code : IntervalSequenceCode N A D rA rD e lo hi p)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (candidate : intervalNextCandidate N A D rA rD e lo hi p y) :
    IntervalSequenceCode (Insert.insert N N) A D rA rD e lo hi (Insert.insert (ZFSet.pair N y) p) := by
  have function : FunctionGraphOn N p := ⟨D, code.function⟩
  have enumFunction : FunctionGraphOn ZFSet.omega e := ⟨A, enumeration⟩
  have cross (i a b q : ZFSet.{u}) (ea : ZFSet.pair i a ∈ e) (eb : ZFSet.pair N b ∈ e)
      (qi : ZFSet.pair i q ∈ p) :
      (a = b ↔ q = y) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q y ∈ rD) ∧
        (ZFSet.pair b a ∈ rA ↔ ZFSet.pair y q ∈ rD) :=
    candidate.2.2.2 i (ZFSet.pair_mem_prod.1 (code.function.1 qi)).1
      a (ZFSet.pair_mem_prod.1 (enumeration.1 ea)).2
      b (ZFSet.pair_mem_prod.1 (enumeration.1 eb)).2
      q (ZFSet.pair_mem_prod.1 (code.function.1 qi)).2 ea eb qi
  refine ⟨⟨?_, (function.successor y).to_isFunc.2⟩, ?_, ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _, candidate.1⟩
    · obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ hi, hq⟩
  · intro i q entry
    rcases (pair_mem_intervalSequenceInsert N p y i q).1 entry with ⟨rfl, rfl⟩ | entry
    · exact ⟨candidate.2.1, candidate.2.2.1⟩
    · exact code.inside i q entry
  · intro i j a b q z ea eb qi zj
    rcases (pair_mem_intervalSequenceInsert N p y i q).1 qi with ⟨hi, hq⟩ | qi
    · subst i
      subst q
      rcases (pair_mem_intervalSequenceInsert N p y j z).1 zj with ⟨hj, hz⟩ | zj
      · subst j
        subst z
        have equal := enumFunction.unique ea eb
        exact ⟨fun _ => rfl, fun _ => equal⟩
      · have relation := (cross j b a z eb ea zj).1
        exact ⟨fun h => (relation.1 h.symm).symm, fun h => (relation.2 h.symm).symm⟩
    · rcases (pair_mem_intervalSequenceInsert N p y j z).1 zj with ⟨hj, hz⟩ | zj
      · subst j
        subst z
        exact (cross i a b q ea eb qi).1
      · exact code.agree i j a b q z ea eb qi zj
  · intro i j a b q z ea eb qi zj
    rcases (pair_mem_intervalSequenceInsert N p y i q).1 qi with ⟨hi, hq⟩ | qi
    · subst i
      subst q
      rcases (pair_mem_intervalSequenceInsert N p y j z).1 zj with ⟨hj, hz⟩ | zj
      · subst j
        subst z
        have equal := enumFunction.unique ea eb
        subst b
        exact iff_of_false (source.irrefl a (ZFSet.pair_mem_prod.1 (enumeration.1 ea)).2)
          (target.irrefl y candidate.1)
      · exact (cross j b a z eb ea zj).2.2
    · rcases (pair_mem_intervalSequenceInsert N p y j z).1 zj with ⟨hj, hz⟩ | zj
      · subst j
        subst z
        exact (cross i a b q ea eb qi).2.1
      · exact code.order i j a b q z ea eb qi zj

end IntervalSequenceCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

def leastIntervalNextCandidate (N A D rA rD e lo hi p c y : ZFSet.{u}) : Prop :=
  intervalNextCandidate N A D rA rD e lo hi p y ∧
    ∃ n ∈ ZFSet.omega, ZFSet.pair y n ∈ c ∧
      ∀ z ∈ D, intervalNextCandidate N A D rA rD e lo hi p z →
        ∀ m ∈ n, ZFSet.pair z m ∉ c

theorem leastIntervalNextCandidate_unique {N A D rA rD e lo hi p c x y : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (hx : leastIntervalNextCandidate N A D rA rD e lo hi p c x)
    (hy : leastIntervalNextCandidate N A D rA rD e lo hi p c y) : x = y := by
  obtain ⟨xValid, n, hn, xn, leastX⟩ := hx
  obtain ⟨yValid, m, hm, ym, leastY⟩ := hy
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastY x xValid.1 xValid (natSetCode k)
      ((natSetCode_mem_iff k l).2 smaller) xn)
  · subst l
    exact injection.injective x y (natSetCode k) xn ym
  · exact False.elim (leastX y yValid.1 yValid (natSetCode l)
      ((natSetCode_mem_iff l k).2 larger) ym)

theorem leastIntervalNextCandidate_exists_unique {N A D rA rD e lo hi p c : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (candidate : ∃ y, intervalNextCandidate N A D rA rD e lo hi p y) :
    ∃! y, leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
  classical
  let valid : Nat → Prop := fun n => ∃ y, intervalNextCandidate N A D rA rD e lo hi p y ∧
    ZFSet.pair y (natSetCode n) ∈ c
  have existsValid : ∃ n, valid n := by
    obtain ⟨y, hy⟩ := candidate
    obtain ⟨a, entry, _⟩ := injection.function.2 y hy.1
    have aNat := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 aNat
    exact ⟨n, y, hy, entry⟩
  obtain ⟨y, hy, entry⟩ := Nat.find_spec existsValid
  have selected : leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
    refine ⟨hy, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro z _ hz m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨z, hz, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨y, selected, fun z hz => leastIntervalNextCandidate_unique injection hz selected⟩

namespace BoundedFormula

open SetFormula

def iffFormula {n} (φ ψ : BoundedFormula n) : BoundedFormula n :=
  .conj (imp φ ψ) (imp ψ φ)

theorem truth_iffFormula {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (iffFormula φ ψ) env ↔ (Truth φ env ↔ Truth ψ env) := by
  simp only [iffFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

def intervalNextCandidateFormula {n} (N A D rA rD e lo hi p y : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  .conj (.mem y D) (.conj (pairMembershipFormula lo y rD)
    (.conj (pairMembershipFormula y hi rD)
      (.allMem N (.allMem A.succ (.allMem A.succ.succ (.allMem D.succ.succ.succ
        (imp (pairMembershipFormula 3 2 (lift e))
          (imp (pairMembershipFormula (lift N) 1 (lift e))
            (imp (pairMembershipFormula 3 0 (lift p))
              (.conj (iffFormula (.equal 2 1) (.equal 0 (lift y)))
                (.conj (iffFormula (pairMembershipFormula 2 1 (lift rA))
                    (pairMembershipFormula 0 (lift y) (lift rD)))
                  (iffFormula (pairMembershipFormula 1 2 (lift rA))
                    (pairMembershipFormula (lift y) 0 (lift rD))))))))))))))

theorem truth_intervalNextCandidateFormula {n} (N A D rA rD e lo hi p y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalNextCandidateFormula N A D rA rD e lo hi p y) env ↔
      intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env y) := by
  simp only [intervalNextCandidateFormula, Truth, truth_pairMembershipFormula,
    truth_imp, truth_iffFormula]
  rfl

def leastIntervalNextCandidateFormula {n} (N A D rA rD e lo hi p c y omega : Fin n) : BoundedFormula n :=
  .conj (intervalNextCandidateFormula N A D rA rD e lo hi p y)
    (exMem omega (.conj (pairMembershipFormula y.succ 0 c.succ)
      (.allMem D.succ (imp
        (intervalNextCandidateFormula N.succ.succ A.succ.succ D.succ.succ rA.succ.succ
          rD.succ.succ e.succ.succ lo.succ.succ hi.succ.succ p.succ.succ 0)
        (.allMem 1 (.neg (pairMembershipFormula 1 0 c.succ.succ.succ)))))))

theorem truth_leastIntervalNextCandidateFormula {n} (N A D rA rD e lo hi p c y omega : Fin n)
    (env : Fin n → ZFSet.{u}) (hOmega : env omega = ZFSet.omega) :
    Truth (leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega) env ↔
      leastIntervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env c) (env y) := by
  simp only [leastIntervalNextCandidateFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_intervalNextCandidateFormula]
  change (intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
      (env lo) (env hi) (env p) (env y) ∧
    ∃ k ∈ env omega, ZFSet.pair (env y) k ∈ env c ∧
      ∀ z ∈ env D, intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) z → ∀ m ∈ k, ZFSet.pair z m ∉ env c) ↔ _
  rw [hOmega]
  rfl

theorem realize_leastIntervalNextCandidateFormula (M : TransitiveGround.{u}) {n}
    (N A D rA rD e lo hi p c y omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (hOmega : env omega = ZFSet.omega) :
    Realize M.sets (leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega).toFormula env ↔
      leastIntervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env c) (env y) :=
  (realize_toFormula M _ env members).trans
    (truth_leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega env hOmega)

end BoundedFormula

namespace SetFormula

def intervalSequenceStepFormula : SetFormula 12 :=
  (BoundedFormula.leastIntervalNextCandidateFormula 0 3 4 5 6 7 8 9 1 10 2 11).toFormula

end SetFormula

namespace TransitiveGround

open SetFormula

theorem realize_intervalSequenceStepFormula (M : TransitiveGround.{u})
    (env : Fin 12 → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (hOmega : env 11 = ZFSet.omega) :
    Realize M.sets intervalSequenceStepFormula env ↔
      leastIntervalNextCandidate (env 0) (env 3) (env 4) (env 5) (env 6) (env 7)
        (env 8) (env 9) (env 1) (env 10) (env 2) :=
  BoundedFormula.realize_leastIntervalNextCandidateFormula M 0 3 4 5 6 7 8 9 1 10 2 11
    env members hOmega

theorem exists_unique_ground_intervalNext (M : TransitiveGround.{u})
    {N A D rA rD e lo hi p c : ZFSet.{u}} (hD : D ∈ M.sets)
    (injection : InjectionCode D ZFSet.omega c)
    (candidate : ∃ y, intervalNextCandidate N A D rA rD e lo hi p y) :
    ∃! y, y ∈ M.sets ∧ leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
  obtain ⟨y, selected, unique⟩ := leastIntervalNextCandidate_exists_unique injection candidate
  exact ⟨y, ⟨M.transitive hD selected.1.1, selected⟩, fun z hz => unique z hz.2⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
