import OAI.SetTheory.PartitionPrinciple.Definability.RationalCodeLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteWordLaws

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

def gridStep (p : Nat × Nat) : Nat × Nat :=
  if p.1 < p.2 then
    if p.1 + 1 < p.2 then (p.1 + 1, p.2) else (p.2, 0)
  else if p.2 < p.1 then (p.1, p.2 + 1) else (0, p.1 + 1)

theorem gridStep_pair (a b : Nat) :
    Nat.pair (gridStep (a, b)).1 (gridStep (a, b)).2 = Nat.pair a b + 1 := by
  by_cases h : a < b
  · by_cases next : a + 1 < b
    · simp [gridStep, h, next, Nat.pair, Nat.add_assoc]
    · have eq : b = a + 1 := by omega
      simp [gridStep, Nat.pair, eq, Nat.add_assoc]
  · by_cases next : b < a
    · have hnext : ¬ a < b + 1 := by omega
      simp [gridStep, h, next, Nat.pair, hnext, Nat.add_assoc]
    · have eq : b = a := by omega
      subst b
      simp [gridStep, Nat.pair, Nat.mul_add, Nat.add_mul, Nat.add_assoc]

theorem gridStep_eq_iff (a b c d : Nat) : gridStep (a, b) = (c, d) ↔
    (c = a + 1 ∧ c < b ∧ d = b) ∨ (b = a + 1 ∧ c = b ∧ d = 0) ∨
    (b < a ∧ c = a ∧ d = b + 1) ∨ (a = b ∧ c = 0 ∧ d = a + 1) := by
  simp only [gridStep]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

def liftedGridStep (p : ULift.{u} Nat × ULift.{u} Nat) : ULift.{u} Nat × ULift.{u} Nat :=
  (⟨(gridStep (p.1.down, p.2.down)).1⟩, ⟨(gridStep (p.1.down, p.2.down)).2⟩)

theorem gridIteration_pair (n : Nat) :
    Nat.pair (natIterate liftedGridStep ((⟨0⟩, ⟨0⟩) : ULift.{u} Nat × ULift.{u} Nat) n).1.down
      (natIterate liftedGridStep ((⟨0⟩, ⟨0⟩) : ULift.{u} Nat × ULift.{u} Nat) n).2.down = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.pair (gridStep _).1 (gridStep _).2 = n + 1
    exact (gridStep_pair _ _).trans (congrArg (fun k => k + 1) ih)

def omegaGridEquiv : ULift.{u} Nat ≃ (ULift.{u} Nat × ULift.{u} Nat) where
  toFun n := (⟨(Nat.unpair n.down).1⟩, ⟨(Nat.unpair n.down).2⟩)
  invFun p := ⟨Nat.pair p.1.down p.2.down⟩
  left_inv n := ULift.ext _ _ (Nat.pair_unpair n.down)
  right_inv p := by
    apply Prod.ext
    · apply ULift.ext
      exact congrArg Prod.fst (Nat.unpair_pair p.1.down p.2.down)
    · apply ULift.ext
      exact congrArg Prod.snd (Nat.unpair_pair p.1.down p.2.down)

theorem gridIteration_eq (n : ULift.{u} Nat) :
    natIterate liftedGridStep (⟨0⟩, ⟨0⟩) n.down = omegaGridEquiv n := by
  apply omegaGridEquiv.symm.injective
  apply ULift.ext
  exact (gridIteration_pair n.down).trans (Nat.pair_unpair n.down).symm

end



section

open Compression.RecursiveMaps.RationalHeights
universe u

def positiveMagnitude (code magnitude add : ZFSet.{u}) : Prop :=
  ZFSet.pair (ZFSet.pair magnitude magnitude) code ∈ add

def negativeMagnitude (code magnitude W add one : ZFSet.{u}) : Prop :=
  ∃ k ∈ W, ∃ d ∈ W,
    ZFSet.pair (ZFSet.pair k one) magnitude ∈ add ∧
    ZFSet.pair (ZFSet.pair k k) d ∈ add ∧
    ZFSet.pair (ZFSet.pair d one) code ∈ add

def fractionComparison (strict : Bool) (a ad b bd W add mul one : ZFSet.{u}) : Prop :=
  ∃ m ∈ W, ∃ n ∈ W, ∃ x ∈ W, ∃ y ∈ W,
    ZFSet.pair (ZFSet.pair m bd) x ∈ mul ∧
    ZFSet.pair (ZFSet.pair n ad) y ∈ mul ∧
    ((positiveMagnitude a m add ∧ positiveMagnitude b n add ∧
        (if strict then x ∈ y else x = y)) ∨
      (negativeMagnitude a m W add one ∧ negativeMagnitude b n W add one ∧
        (if strict then y ∈ x else x = y)) ∨
      (if strict then negativeMagnitude a m W add one ∧ positiveMagnitude b n add else False))

theorem exists_mem_omega_code (p : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, p x) ↔ ∃ n : Nat, p (natSetCode n) := by
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    exact ⟨n, hp⟩
  · rintro ⟨n, hp⟩
    exact ⟨_, natSetCode_mem_omega n, hp⟩

theorem positiveMagnitude_ofNat (n m : Nat) :
    positiveMagnitude (natSetCode (Fraction.intCode (Int.ofNat n)))
      (natSetCode m) natAddGraph.{u} ↔ m = n := by
  rw [positiveMagnitude, pair_mem_natAddGraph]
  simp only [Fraction.intCode]
  omega

theorem positiveMagnitude_negSucc (n m : Nat) :
    ¬ positiveMagnitude (natSetCode (Fraction.intCode (Int.negSucc n)))
      (natSetCode m) natAddGraph.{u} := by
  rw [positiveMagnitude, pair_mem_natAddGraph]
  simp only [Fraction.intCode]
  omega

theorem negativeMagnitude_ofNat (n m : Nat) :
    ¬ negativeMagnitude (natSetCode (Fraction.intCode (Int.ofNat n)))
      (natSetCode m) ZFSet.omega natAddGraph.{u} (natSetCode 1) := by
  simp only [negativeMagnitude, exists_mem_omega_code, pair_mem_natAddGraph, Fraction.intCode]
  omega

theorem negativeMagnitude_negSucc (n m : Nat) :
    negativeMagnitude (natSetCode (Fraction.intCode (Int.negSucc n)))
      (natSetCode m) ZFSet.omega natAddGraph.{u} (natSetCode 1) ↔ m = n + 1 := by
  simp only [negativeMagnitude, exists_mem_omega_code, pair_mem_natAddGraph, Fraction.intCode]
  constructor
  · rintro ⟨k, d, hm, hd, hn⟩
    omega
  · intro hm
    exact ⟨n, n + n, hm, rfl, by omega⟩

theorem fractionComparison_code (strict : Bool) (a b : Fraction) :
    fractionComparison strict (natSetCode (Fraction.intCode a.num)) (natSetCode a.den)
      (natSetCode (Fraction.intCode b.num)) (natSetCode b.den)
      ZFSet.omega natAddGraph.{u} natMulGraph (natSetCode 1) ↔
        (if strict then Fraction.Lt a b else Fraction.Equiv a b) := by
  rcases a with ⟨an, ad, ha⟩
  rcases b with ⟨bn, bd, hb⟩
  cases an <;> cases bn <;> cases strict <;>
    simp only [fractionComparison, exists_mem_omega_code, pair_mem_natMulGraph,
      positiveMagnitude_ofNat, positiveMagnitude_negSucc, negativeMagnitude_ofNat,
      negativeMagnitude_negSucc, Bool.false_eq_true, ite_false, ite_true,
      natSetCode_injective.eq_iff, natSetCode_mem_iff]
  all_goals rename_i an bn
  all_goals have pa := Nat.mul_pos (Nat.succ_pos an) hb
  all_goals have pb := Nat.mul_pos (Nat.succ_pos bn) ha
  all_goals simp only [Fraction.Equiv, Fraction.Lt]
  all_goals try simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, ← Int.natCast_succ, Int.neg_mul, ← Int.natCast_mul]
  all_goals simp only [false_and, and_false, false_or, or_false, exists_eq_left, exists_eq_right,
    and_self, exists_and_left]
  all_goals try simp only [Nat.succ_eq_add_one] at *
  all_goals try simp only [exists_false, exists_eq, false_iff, true_iff]
  all_goals omega

namespace BoundedFormula

open SetFormula

def positiveMagnitudeFormula {n} (code magnitude add : Fin n) : BoundedFormula n :=
  tripleMembershipFormula magnitude magnitude code add

def negativeMagnitudeFormula {n} (code magnitude W add one : Fin n) : BoundedFormula n :=
  exMem W (exMem W.succ
    (.conj (tripleMembershipFormula 1 one.succ.succ magnitude.succ.succ add.succ.succ)
      (.conj (tripleMembershipFormula 1 1 0 add.succ.succ)
        (tripleMembershipFormula 0 one.succ.succ code.succ.succ add.succ.succ))))

theorem truth_positiveMagnitudeFormula {n} (code magnitude add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (positiveMagnitudeFormula code magnitude add) env ↔
      positiveMagnitude (env code) (env magnitude) (env add) :=
  truth_tripleMembershipFormula magnitude magnitude code add env

theorem truth_negativeMagnitudeFormula {n} (code magnitude W add one : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (negativeMagnitudeFormula code magnitude W add one) env ↔
      negativeMagnitude (env code) (env magnitude) (env W) (env add) (env one) := by
  simp only [negativeMagnitudeFormula, truth_exMem, Truth, truth_tripleMembershipFormula]
  rfl

def fractionComparisonFormula {n} (strict : Bool) (a ad b bd W add mul one : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  exMem W (exMem W.succ (exMem W.succ.succ (exMem W.succ.succ.succ
    (.conj (tripleMembershipFormula 3 (lift bd) 1 (lift mul))
      (.conj (tripleMembershipFormula 2 (lift ad) 0 (lift mul))
        (disj
          (.conj (positiveMagnitudeFormula (lift a) 3 (lift add))
            (.conj (positiveMagnitudeFormula (lift b) 2 (lift add))
              (if strict then .mem 1 0 else .equal 1 0)))
          (disj
            (.conj (negativeMagnitudeFormula (lift a) 3 (lift W) (lift add) (lift one))
              (.conj (negativeMagnitudeFormula (lift b) 2 (lift W) (lift add) (lift one))
                (if strict then .mem 0 1 else .equal 1 0)))
            (if strict then
              .conj (negativeMagnitudeFormula (lift a) 3 (lift W) (lift add) (lift one))
                (positiveMagnitudeFormula (lift b) 2 (lift add))
              else .neg (.equal 0 0)))))))))

theorem truth_fractionComparisonFormula {n} (strict : Bool) (a ad b bd W add mul one : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fractionComparisonFormula strict a ad b bd W add mul one) env ↔
      fractionComparison strict (env a) (env ad) (env b) (env bd)
        (env W) (env add) (env mul) (env one) := by
  cases strict <;>
    simp only [fractionComparisonFormula, truth_exMem, Truth, truth_tripleMembershipFormula,
      truth_positiveMagnitudeFormula, truth_negativeMagnitudeFormula, truth_disj,
      Bool.false_eq_true, ite_false, ite_true, not_true_eq_false]
  all_goals rfl

end BoundedFormula

end



section

open SetRealization
universe u

def GridStepCode (a b c d : ZFSet.{u}) : Prop :=
  (c = insert a a ∧ c ∈ b ∧ d = b) ∨ (b = insert a a ∧ c = b ∧ d = ∅) ∨
  (b ∈ a ∧ c = a ∧ d = insert b b) ∨ (a = b ∧ c = ∅ ∧ d = insert a a)

theorem gridStepCode_nat (a b c d : Nat) :
    GridStepCode (natSetCode a : ZFSet.{u}) (natSetCode b) (natSetCode c) (natSetCode d) ↔
      gridStep (a, b) = (c, d) := by
  have successor (m n : Nat) : (natSetCode m : ZFSet.{u}) = insert (natSetCode n) (natSetCode n) ↔
      m = n + 1 := by
    rw [← natSetCode_succ]
    exact natSetCode_injective.eq_iff
  have zero (m : Nat) : (natSetCode m : ZFSet.{u}) = ∅ ↔ m = 0 := by
    rw [← natSetCode_zero]
    exact natSetCode_injective.eq_iff
  rw [GridStepCode, gridStep_eq_iff]
  simp only [successor, zero, natSetCode_injective.eq_iff, natSetCode_mem_iff]

namespace BoundedFormula

open SetFormula

def gridStepFormula {n} (a b c d : Fin n) : BoundedFormula n :=
  disj (.conj (successorFormula c a) (.conj (.mem c b) (.equal d b)))
    (disj (.conj (successorFormula b a) (.conj (.equal c b) (emptyFormula d)))
      (disj (.conj (.mem b a) (.conj (.equal c a) (successorFormula d b)))
        (.conj (.equal a b) (.conj (emptyFormula c) (successorFormula d a)))))

theorem truth_gridStepFormula {n} (a b c d : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (gridStepFormula a b c d) env ↔ GridStepCode (env a) (env b) (env c) (env d) := by
  simp only [gridStepFormula, truth_disj, Truth, truth_successorFormula, truth_emptyFormula]
  rfl

def gridTransitionFormula {n} (x y w : Fin n) : BoundedFormula n :=
  exMem w (exMem w.succ (exMem w.succ.succ (exMem w.succ.succ.succ
    (.conj (orderedPairFormula x.succ.succ.succ.succ 3 2)
      (.conj (orderedPairFormula y.succ.succ.succ.succ 1 0) (gridStepFormula 3 2 1 0))))))

theorem truth_gridTransitionFormula {n} (x y w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (gridTransitionFormula x y w) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w,
        env x = ZFSet.pair a b ∧ env y = ZFSet.pair c d ∧ GridStepCode a b c d := by
  simp only [gridTransitionFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_gridStepFormula]
  rfl

def gridEntryFormula {n} (z w s : Fin n) : BoundedFormula n :=
  exMem s (exMem s.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (gridTransitionFormula 1 0 w.succ.succ)))

theorem truth_gridEntryFormula {n} (z w s : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (gridEntryFormula z w s) env ↔
      ∃ x ∈ env s, ∃ y ∈ env s, env z = ZFSet.pair x y ∧
        ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w,
          x = ZFSet.pair a b ∧ y = ZFSet.pair c d ∧ GridStepCode a b c d := by
  simp only [gridEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_gridTransitionFormula]
  rfl

theorem gridEntry_correct (z : ZFSet.{u}) :
    Truth (gridEntryFormula 0 1 2) (extend z (extend ZFSet.omega
      (extend (ZFSet.prod ZFSet.omega ZFSet.omega) Fin.elim0))) ↔
      z ∈ (natPresentation.product natPresentation).graph
        (natPresentation.product natPresentation) liftedGridStep := by
  rw [truth_gridEntryFormula]
  change (∃ x ∈ ZFSet.prod ZFSet.omega ZFSet.omega, ∃ y ∈ ZFSet.prod ZFSet.omega ZFSet.omega,
    z = ZFSet.pair x y ∧ ∃ a ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ c ∈ ZFSet.omega, ∃ d ∈ ZFSet.omega,
      x = ZFSet.pair a b ∧ y = ZFSet.pair c d ∧ GridStepCode a b c d) ↔ _
  constructor
  · rintro ⟨x, _, y, _, rfl, a, ha, b, hb, c, hc, d, hd, rfl, rfl, code⟩
    obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
    obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode b).1 hb
    obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode c).1 hc
    obtain ⟨d, rfl⟩ := (mem_omega_iff_natSetCode d).1 hd
    have step := (gridStepCode_nat a b c d).1 code
    apply ((natPresentation.product natPresentation).pair_mem_graph
      (natPresentation.product natPresentation) liftedGridStep (⟨a⟩, ⟨b⟩) (⟨c⟩, ⟨d⟩)).2
    exact Prod.ext (ULift.ext _ _ (congrArg Prod.fst step)) (ULift.ext _ _ (congrArg Prod.snd step))
  · intro hz
    obtain ⟨p, eq⟩ := ((natPresentation.product natPresentation).mem_graph
      (natPresentation.product natPresentation) liftedGridStep z).1 hz
    let q := liftedGridStep p
    exact ⟨(natPresentation.product natPresentation).encode p,
      (natPresentation.product natPresentation).encode_mem p,
      (natPresentation.product natPresentation).encode q,
      (natPresentation.product natPresentation).encode_mem q, eq.symm,
      natSetCode p.1.down, natSetCode_mem_omega _, natSetCode p.2.down, natSetCode_mem_omega _,
      natSetCode q.1.down, natSetCode_mem_omega _, natSetCode q.2.down, natSetCode_mem_omega _,
      rfl, rfl, (gridStepCode_nat _ _ _ _).2 rfl⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem gridStep_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    (natPresentation.product natPresentation).graph
      (natPresentation.product natPresentation) liftedGridStep ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hs := M.prod_mem pairing unions powers separation hw hw
  have bound := M.prod_mem pairing unions powers separation hs hs
  let params := extend ZFSet.omega (extend (ZFSet.prod ZFSet.omega ZFSet.omega) Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.gridEntryFormula 0 1 2)
    params (Fin.cases hw (Fin.cases hs (fun i => Fin.elim0 i))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.gridEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod (ZFSet.prod ZFSet.omega ZFSet.omega)
        (ZFSet.prod ZFSet.omega ZFSet.omega)) =
      (natPresentation.product natPresentation).graph (natPresentation.product natPresentation) liftedGridStep := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.gridEntry_correct]
    exact ⟨And.right, fun h => ⟨((natPresentation.product natPresentation).graph_isFunc
      (natPresentation.product natPresentation) liftedGridStep).1 h, h⟩⟩
  exact eq ▸ selected

theorem omega_grid_equiv_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have graph := M.natural_recursion_graph_mem pairing unions powers separation infinite
    (natPresentation.product natPresentation) liftedGridStep (⟨0⟩, ⟨0⟩)
    (M.prod_mem pairing unions powers separation hw hw)
    (M.gridStep_graph_mem pairing unions powers separation infinite)
  have eq : (fun n : ULift.{u} Nat => natIterate liftedGridStep (⟨0⟩, ⟨0⟩) n.down) = omegaGridEquiv :=
    funext gridIteration_eq
  rw [eq] at graph
  exact graph

theorem omega_product_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    M.groundEmbeddable (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega := by
  have hw := M.omega_mem separation infinite
  have inverse := M.inverse_function_graph_mem natPresentation (natPresentation.product natPresentation)
    pairing unions powers separation omegaGridEquiv hw (M.prod_mem pairing unions powers separation hw hw)
    (M.omega_grid_equiv_graph_mem pairing unions powers separation infinite)
  exact ⟨(natPresentation.product natPresentation).graph natPresentation omegaGridEquiv.symm,
    inverse, (natPresentation.product natPresentation).graph_injection natPresentation
      omegaGridEquiv.symm omegaGridEquiv.symm.injective⟩

end TransitiveGround

end



section

open Compression.RecursiveMaps.RationalHeights
universe u

namespace BoundedFormula

open SetFormula

def fractionGraphFormula (strict : Bool) : BoundedFormula 6 :=
  exMem 1 (exMem 2 (.conj (orderedPairFormula 2 1 0)
    (exMem 4 (exMem 5 (exMem 6 (exMem 7
      (.conj (orderedPairFormula 5 3 2)
        (.conj (orderedPairFormula 4 1 0)
          (fractionComparisonFormula strict 3 2 1 0 8 9 10 11)))))))))

theorem truth_fractionGraphFormula (strict : Bool) (env : Fin 6 → ZFSet.{u}) :
    Truth (fractionGraphFormula strict) env ↔
      ∃ x ∈ env 1, ∃ y ∈ env 1, env 0 = ZFSet.pair x y ∧
        ∃ a ∈ env 2, ∃ ad ∈ env 2, ∃ b ∈ env 2, ∃ bd ∈ env 2,
          x = ZFSet.pair a ad ∧ y = ZFSet.pair b bd ∧
          fractionComparison strict a ad b bd (env 2) (env 3) (env 4) (env 5) := by
  simp only [fractionGraphFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fractionComparisonFormula]
  rfl

theorem fractionGraphFormula_iff (strict : Bool) (z : ZFSet.{u}) :
    Truth (fractionGraphFormula strict)
      (extend z (extend fractionCarrier (extend ZFSet.omega (extend natAddGraph
        (extend natMulGraph (extend (natSetCode 1) Fin.elim0)))))) ↔
      ∃ a b : Fraction, z = ZFSet.pair (fractionEncode a) (fractionEncode b) ∧
        (if strict then Fraction.Lt a b else Fraction.Equiv a b) := by
  rw [truth_fractionGraphFormula]
  change (∃ x ∈ fractionCarrier, ∃ y ∈ fractionCarrier, z = ZFSet.pair x y ∧
    ∃ a ∈ ZFSet.omega, ∃ ad ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ bd ∈ ZFSet.omega,
      x = ZFSet.pair a ad ∧ y = ZFSet.pair b bd ∧
      fractionComparison strict a ad b bd ZFSet.omega natAddGraph natMulGraph (natSetCode 1)) ↔ _
  constructor
  · rintro ⟨x, hx, y, hy, equal, n, _, d, _, k, _, e, _, ex, ey, compare⟩
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 hx
    obtain ⟨b, rfl⟩ := (mem_fractionCarrier y).1 hy
    have pa := ZFSet.pair_inj.1 ex
    have pb := ZFSet.pair_inj.1 ey
    exact ⟨a, b, equal, (fractionComparison_code strict a b).1
      (pa.1.symm ▸ pa.2.symm ▸ pb.1.symm ▸ pb.2.symm ▸ compare)⟩
  · rintro ⟨a, b, equal, compare⟩
    exact ⟨fractionEncode a, fractionEncode_mem a, fractionEncode b, fractionEncode_mem b,
      equal, natSetCode (Fraction.intCode a.num), natSetCode_mem_omega _,
      natSetCode a.den, natSetCode_mem_omega _, natSetCode (Fraction.intCode b.num),
      natSetCode_mem_omega _, natSetCode b.den, natSetCode_mem_omega _, rfl, rfl,
      (fractionComparison_code strict a b).2 compare⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem fractionCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : fractionCarrier ∈ M.sets := by
  have hW := M.omega_mem separation infinite
  have h0 := M.natSetCode_mem separation infinite 0
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.neg (BoundedFormula.equal 0 1)) (extend (natSetCode 0) Fin.elim0)
    (Fin.cases h0 (fun j => Fin.elim0 j)) hW
  exact M.prod_mem pairing unions powers separation hW selected

theorem fractionComparisonGraph_mem (strict : Bool)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    (if strict then fractionLtGraph else fractionEquivGraph) ∈ M.sets := by
  have hF := M.fractionCarrier_mem pairing unions powers separation infinite
  have hW := M.omega_mem separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  have hMul := M.natMulGraph_mem pairing unions powers separation infinite
  have hOne := M.natSetCode_mem separation infinite 1
  let params := extend fractionCarrier (extend ZFSet.omega
    (extend natAddGraph (extend natMulGraph (extend (natSetCode 1) Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.fractionGraphFormula strict)
    params (Fin.cases hF (Fin.cases hW (Fin.cases hAdd
      (Fin.cases hMul (Fin.cases hOne (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation hF hF)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.fractionGraphFormula strict) (extend z params))
      (ZFSet.prod fractionCarrier fractionCarrier) =
        (if strict then fractionLtGraph else fractionEquivGraph) := by
    cases strict <;> apply ZFSet.ext <;> intro z
    all_goals simp only [Bool.false_eq_true, ite_false, ite_true, fractionLtGraph,
      fractionEquivGraph, ZFSet.mem_sep]
    all_goals exact and_congr Iff.rfl (BoundedFormula.fractionGraphFormula_iff _ z)
  exact equal ▸ selected

theorem fractionEquivGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : fractionEquivGraph ∈ M.sets :=
  M.fractionComparisonGraph_mem false pairing unions powers separation infinite

theorem fractionLtGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : fractionLtGraph ∈ M.sets :=
  M.fractionComparisonGraph_mem true pairing unions powers separation infinite

end TransitiveGround

end



namespace TransitiveGround

open SetFormula SetRealization Compression.RecursiveMaps.RationalHeights
universe u
variable (M : TransitiveGround.{u})

theorem fractionCarrier_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    M.groundEmbeddable fractionCarrier ZFSet.omega := by
  have subset : fractionCarrier.{u} ⊆ ZFSet.prod ZFSet.omega ZFSet.omega := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.mem_sep.1 hy).1⟩
  exact M.groundEmbeddable_restrict separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.omega_mem separation infinite) subset
    (M.omega_product_countable pairing unions powers separation infinite)

theorem rationalCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {c : ZFSet.{u}} (hc : c ∈ M.sets) : rationalCarrier c ∈ M.sets :=
  M.canonicalRepresentatives_mem separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.fractionEquivGraph_mem pairing unions powers separation infinite) hc
    (M.omega_mem separation infinite)

theorem rationalLtGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {c : ZFSet.{u}} (hc : c ∈ M.sets) : rationalLtGraph c ∈ M.sets :=
  M.injection_restriction_mem separation
    (M.rationalCarrier_mem pairing unions powers separation infinite hc)
    (M.rationalCarrier_mem pairing unions powers separation infinite hc)
    (M.fractionLtGraph_mem pairing unions powers separation infinite)

theorem exists_groundRationals
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    ∃ D ∈ M.sets, ∃ r ∈ M.sets, ∃ f ∈ M.sets,
      InjectionCode D ZFSet.omega f ∧ DenseOrderCode D r ∧
      (∃ x, x ∈ D) ∧
      (∀ x ∈ D, (∃ y ∈ D, ZFSet.pair y x ∈ r) ∧ (∃ y ∈ D, ZFSet.pair x y ∈ r)) ∧
      ∃ s : Presentation (ULift.{u} Rational), s.carrier = D ∧
        ∀ a b, ZFSet.pair (s.encode a) (s.encode b) ∈ r ↔ Rational.lt a.down b.down := by
  obtain ⟨c, hc, code⟩ := M.fractionCarrier_countable pairing unions powers separation infinite
  have carrier := M.rationalCarrier_mem pairing unions powers separation infinite hc
  have relation := M.rationalLtGraph_mem pairing unions powers separation infinite hc
  have injection := M.canonicalRepresentativesInjection_mem separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.fractionEquivGraph_mem pairing unions powers separation infinite) hc
    (M.omega_mem separation infinite)
  exact ⟨rationalCarrier c, carrier, rationalLtGraph c, relation,
    canonicalRepresentativesInjection fractionCarrier fractionEquivGraph c, injection,
    canonicalRepresentativesInjection_code code, rational_denseOrderCode code,
    rationalCarrier_nonempty code, rational_no_endpoints code,
    rationalPresentation code, rfl, fun a b => pair_mem_rationalLtGraph code a.down b.down⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
