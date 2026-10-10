import OAI.SetTheory.PartitionPrinciple.Definability.IntervalSequenceFormulas

namespace OAI

section

namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

theorem intervalComparisons_of_preserved {A D rA rD a b z y : ZFSet.{u}}
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (ha : a ∈ A) (hb : b ∈ A) (hz : z ∈ D) (hy : y ∈ D)
    (same : a = b → z = y)
    (forward : ZFSet.pair a b ∈ rA → ZFSet.pair z y ∈ rD)
    (backward : ZFSet.pair b a ∈ rA → ZFSet.pair y z ∈ rD) :
    (a = b ↔ z = y) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair z y ∈ rD) ∧
      (ZFSet.pair b a ∈ rA ↔ ZFSet.pair y z ∈ rD) := by
  refine ⟨⟨same, ?_⟩, ⟨forward, ?_⟩, ⟨backward, ?_⟩⟩
  · intro equal
    rcases source.compare a ha b hb with less | equalSource | more
    · have rel := forward less
      rw [equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact equalSource
    · have rel := backward more
      rw [equal] at rel
      exact False.elim (target.irrefl y hy rel)
  · intro rel
    rcases source.compare a ha b hb with less | equal | more
    · exact less
    · rw [same equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact False.elim (target.irrefl z hz (target.trans z y z rel (backward more)))
  · intro rel
    rcases source.compare a ha b hb with less | equal | more
    · exact False.elim (target.irrefl y hy (target.trans y z y rel (forward less)))
    · rw [same equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact more

theorem finite_intervalNextCandidate_exists
    {A D rA rD e lo hi p : ZFSet.{u}} (n : Nat)
    (code : IntervalSequenceCode (natSetCode n) A D rA rD e lo hi p)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ y, intervalNextCandidate (natSetCode n) A D rA rD e lo hi p y := by
  classical
  let enumerate : Nat → {a : ZFSet.{u} // a ∈ A} := fun k =>
    ⟨Classical.choose (enumeration.2 (natSetCode k) (natSetCode_mem_omega k)),
      (ZFSet.pair_mem_prod.1 (enumeration.1
        (Classical.choose_spec (enumeration.2 (natSetCode k) (natSetCode_mem_omega k))).1)).2⟩
  have enumerateEntry (k : Nat) : ZFSet.pair (natSetCode k) (enumerate k).val ∈ e :=
    (Classical.choose_spec (enumeration.2 (natSetCode k) (natSetCode_mem_omega k))).1
  let value : Nat → {q : ZFSet.{u} // q ∈ D} := fun k =>
    if hk : k < n then
      ⟨Classical.choose (code.function.2 (natSetCode k) ((natSetCode_mem_iff k n).2 hk)),
        (ZFSet.pair_mem_prod.1 (code.function.1
          (Classical.choose_spec (code.function.2 (natSetCode k)
            ((natSetCode_mem_iff k n).2 hk))).1)).2⟩
    else ⟨lo, loD⟩
  have valueEntry (k : Nat) (hk : k < n) :
      ZFSet.pair (natSetCode k) (value k).val ∈ p := by
    dsimp only [value]
    rw [dite_eq_left hk]
    exact (Classical.choose_spec (code.function.2 (natSetCode k)
      ((natSetCode_mem_iff k n).2 hk))).1
  let initial : CountableInterpolation.Partial source.toLinearHeightOrder target.toDenseHeightOrder
      enumerate ⟨lo, loD⟩ ⟨hi, hiD⟩ n := {
    value := value
    lower := fun k hk => (code.inside _ _ (valueEntry k hk)).1
    upper := fun k hk => (code.inside _ _ (valueEntry k hk)).2
    strict := fun i j hi hj less => (code.order _ _ _ _ _ _
      (enumerateEntry i) (enumerateEntry j) (valueEntry i hi) (valueEntry j hj)).1 less
    equal := fun i j hi hj equal => Subtype.ext ((code.agree _ _ _ _ _ _
      (enumerateEntry i) (enumerateEntry j) (valueEntry i hi) (valueEntry j hj)).1
        (congrArg Subtype.val equal)) }
  obtain ⟨y, lower, upper, forward, backward, same⟩ := CountableInterpolation.next_exists initial gap
  refine ⟨y.val, y.property, lower, upper, ?_⟩
  intro i hi a _ b _ z _ ea eb iz
  obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i n).1 hi
  have enumFunction : FunctionGraphOn ZFSet.omega e := ⟨A, enumeration⟩
  have valueFunction : FunctionGraphOn (natSetCode n) p := ⟨D, code.function⟩
  have first : (enumerate k).val = a := enumFunction.unique (enumerateEntry k) ea
  have second : (enumerate n).val = b := enumFunction.unique (enumerateEntry n) eb
  have previous : (value k).val = z := valueFunction.unique (valueEntry k hk) iz
  have comparisons := intervalComparisons_of_preserved source target.toStrictLinearOrderCode
    (enumerate k).property (enumerate n).property (value k).property y.property
    (fun equal => congrArg Subtype.val (same k hk (Subtype.ext equal)))
    (forward k hk) (backward k hk)
  change ((enumerate k).val = (enumerate n).val ↔ (value k).val = y.val) ∧
    (ZFSet.pair (enumerate k).val (enumerate n).val ∈ rA ↔ ZFSet.pair (value k).val y.val ∈ rD) ∧
    (ZFSet.pair (enumerate n).val (enumerate k).val ∈ rA ↔ ZFSet.pair y.val (value k).val ∈ rD)
    at comparisons
  rw [first, second, previous] at comparisons
  exact comparisons

end PartitionPilot.Forcing

end

end OAI
