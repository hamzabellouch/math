import OAI.SetTheory.PartitionPrinciple.Forcing.CodedDenseOrders

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

def leastIntervalCandidate (D r c lower upper lo hi x : ZFSet.{u}) : Prop :=
  intervalCandidate D r lower upper lo hi x ∧
    ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ c ∧
      ∀ y ∈ D, intervalCandidate D r lower upper lo hi y →
        ∀ m ∈ n, ZFSet.pair y m ∉ c

theorem leastIntervalCandidate_unique {D r c lower upper lo hi x y : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (hx : leastIntervalCandidate D r c lower upper lo hi x)
    (hy : leastIntervalCandidate D r c lower upper lo hi y) : x = y := by
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

theorem leastIntervalCandidate_exists_unique {D r c lower upper lo hi : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (candidate : ∃ x, intervalCandidate D r lower upper lo hi x) :
    ∃! x, leastIntervalCandidate D r c lower upper lo hi x := by
  classical
  let valid : Nat → Prop := fun n => ∃ x, intervalCandidate D r lower upper lo hi x ∧
    ZFSet.pair x (natSetCode n) ∈ c
  have existsValid : ∃ n, valid n := by
    obtain ⟨x, hx⟩ := candidate
    obtain ⟨a, entry, _⟩ := injection.function.2 x hx.1
    have aNat := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 aNat
    exact ⟨n, x, hx, entry⟩
  obtain ⟨x, hx, entry⟩ := Nat.find_spec existsValid
  have selected : leastIntervalCandidate D r c lower upper lo hi x := by
    refine ⟨hx, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro y _ hy m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨y, hy, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨x, selected, fun y hy => leastIntervalCandidate_unique injection hy selected⟩

theorem DenseOrderCode.least_interval_exists_unique {D r c lower upper lo hi : ZFSet.{u}}
    (code : DenseOrderCode D r) (injection : InjectionCode D ZFSet.omega c)
    (loD : lo ∈ D) (hiD : hi ∈ D) (lowerD : lower ⊆ D) (upperD : upper ⊆ D)
    (finiteLower : lower.toSet.Finite) (finiteUpper : upper.toSet.Finite)
    (gap : ZFSet.pair lo hi ∈ r)
    (lowerHi : ∀ x ∈ lower, ZFSet.pair x hi ∈ r)
    (loUpper : ∀ y ∈ upper, ZFSet.pair lo y ∈ r)
    (separated : ∀ x ∈ lower, ∀ y ∈ upper, ZFSet.pair x y ∈ r) :
    ∃! x, leastIntervalCandidate D r c lower upper lo hi x :=
  leastIntervalCandidate_exists_unique injection
    (code.finite_interval_candidate loD hiD lowerD upperD finiteLower finiteUpper gap lowerHi loUpper separated)

namespace BoundedFormula

open SetFormula

def intervalCandidateFormula {n} (x d r lower upper lo hi : Fin n) : BoundedFormula n :=
  .conj (.mem x d) (.conj (pairMembershipFormula lo x r)
    (.conj (pairMembershipFormula x hi r)
      (.conj (.allMem lower (pairMembershipFormula 0 x.succ r.succ))
        (.allMem upper (pairMembershipFormula x.succ 0 r.succ)))))

theorem truth_intervalCandidateFormula {n} (x d r lower upper lo hi : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalCandidateFormula x d r lower upper lo hi) env ↔
      intervalCandidate (env d) (env r) (env lower) (env upper) (env lo) (env hi) (env x) := by
  simp only [intervalCandidateFormula, Truth, truth_pairMembershipFormula, intervalCandidate]
  rfl

def leastIntervalCandidateFormula {n} (x d r c lower upper lo hi omega : Fin n) : BoundedFormula n :=
  .conj (intervalCandidateFormula x d r lower upper lo hi)
    (exMem omega (.conj (pairMembershipFormula x.succ 0 c.succ)
      (.allMem d.succ (imp
        (intervalCandidateFormula 0 d.succ.succ r.succ.succ lower.succ.succ
          upper.succ.succ lo.succ.succ hi.succ.succ)
        (.allMem 1 (.neg (pairMembershipFormula 1 0 c.succ.succ.succ)))))))

theorem truth_leastIntervalCandidateFormula {n} (x d r c lower upper lo hi omega : Fin n)
    (env : Fin n → ZFSet.{u}) (hOmega : env omega = ZFSet.omega) :
    Truth (leastIntervalCandidateFormula x d r c lower upper lo hi omega) env ↔
      leastIntervalCandidate (env d) (env r) (env c) (env lower) (env upper) (env lo) (env hi) (env x) := by
  simp only [leastIntervalCandidateFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_intervalCandidateFormula]
  change (intervalCandidate (env d) (env r) (env lower) (env upper) (env lo) (env hi) (env x) ∧
    ∃ n ∈ env omega, ZFSet.pair (env x) n ∈ env c ∧
      ∀ y ∈ env d, intervalCandidate (env d) (env r) (env lower) (env upper) (env lo) (env hi) y →
        ∀ m ∈ n, ZFSet.pair y m ∉ env c) ↔ _
  rw [hOmega]
  rfl

theorem realize_leastIntervalCandidateFormula (M : TransitiveGround.{u}) {n}
    (x d r c lower upper lo hi omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (hOmega : env omega = ZFSet.omega) :
    Realize M.sets (leastIntervalCandidateFormula x d r c lower upper lo hi omega).toFormula env ↔
      leastIntervalCandidate (env d) (env r) (env c) (env lower) (env upper) (env lo) (env hi) (env x) :=
  (realize_toFormula M _ env members).trans
    (truth_leastIntervalCandidateFormula x d r c lower upper lo hi omega env hOmega)

end BoundedFormula

namespace TransitiveGround

theorem exists_unique_ground_intervalSelection (M : TransitiveGround.{u})
    {D r c lower upper lo hi : ZFSet.{u}} (hD : D ∈ M.sets)
    (code : DenseOrderCode D r) (injection : InjectionCode D ZFSet.omega c)
    (loD : lo ∈ D) (hiD : hi ∈ D) (lowerD : lower ⊆ D) (upperD : upper ⊆ D)
    (finiteLower : lower.toSet.Finite) (finiteUpper : upper.toSet.Finite)
    (gap : ZFSet.pair lo hi ∈ r)
    (lowerHi : ∀ x ∈ lower, ZFSet.pair x hi ∈ r)
    (loUpper : ∀ y ∈ upper, ZFSet.pair lo y ∈ r)
    (separated : ∀ x ∈ lower, ∀ y ∈ upper, ZFSet.pair x y ∈ r) :
    ∃! x, x ∈ M.sets ∧ leastIntervalCandidate D r c lower upper lo hi x := by
  obtain ⟨x, selected, unique⟩ := code.least_interval_exists_unique injection loD hiD lowerD upperD
    finiteLower finiteUpper gap lowerHi loUpper separated
  exact ⟨x, ⟨M.transitive hD selected.1.1, selected⟩, fun y hy => unique y hy.2⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
