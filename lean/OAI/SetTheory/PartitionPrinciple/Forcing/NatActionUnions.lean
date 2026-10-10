import OAI.SetTheory.PartitionPrinciple.Definability.SeparationFulfillmentCodes

namespace OAI

section

namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem posetAction {P r a : Nat → ZFSet.{u}} {G m e L R A : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R) (action : NatUnionCode a A)
    (codes : ∀ n, PosetActionCode G (P n) m e (r n) (a n))
    (relationMono : ∀ n j, n ≤ j → r n ⊆ r j)
    (actionMono : ∀ n j, n ≤ j → a n ⊆ a j) : PosetActionCode G L m e R A := by
  refine ⟨(carrier.prod_left G).isFunc carrier action (fun n => (codes n).function) actionMono,
    ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨n, hn⟩ := (carrier p).1 hp
    exact action.subset n ((codes n).one p hn)
  · intro g hg h hh k hk p _ q _ v _ product first second
    obtain ⟨i, hi⟩ := (action _).1 first
    obtain ⟨j, hj⟩ := (action _).1 second
    let n := max i j
    have firstN := actionMono i n (le_max_left i j) hi
    have secondN := actionMono j n (le_max_right i j) hj
    have firstShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 firstN)
    have secondShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 secondN)
    exact action.subset n ((codes n).mul g hg h hh k hk
      p (ZFSet.pair_mem_prod.1 firstShape.1).2 q firstShape.2 v secondShape.2 product firstN secondN)
  · intro g hg p _ q _ v _ w _ first second lower
    obtain ⟨i, hi⟩ := (action _).1 first
    obtain ⟨j, hj⟩ := (action _).1 second
    obtain ⟨k, hk⟩ := (relation _).1 lower
    let n := max k (max i j)
    have kn : k ≤ n := le_max_left k (max i j)
    have inN : i ≤ n := (le_max_left i j).trans (le_max_right k (max i j))
    have jn : j ≤ n := (le_max_right i j).trans (le_max_right k (max i j))
    have firstN := actionMono i n inN hi
    have secondN := actionMono j n jn hj
    have firstShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 firstN)
    have secondShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 secondN)
    exact relation.subset n ((codes n).monotone g hg
      p (ZFSet.pair_mem_prod.1 firstShape.1).2
      q (ZFSet.pair_mem_prod.1 secondShape.1).2 v firstShape.2 w secondShape.2
      firstN secondN (relationMono k n kn hk))

theorem action_entry_iff {P r a : Nat → ZFSet.{u}} {G m e L R A : ZFSet.{u}}
    (action : NatUnionCode a A) (unionCode : PosetActionCode G L m e R A)
    (codes : ∀ n, PosetActionCode G (P n) m e (r n) (a n))
    (n : Nat) {g x y : ZFSet.{u}} (hx : x ∈ P n) :
    ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ a n := by
  by_cases hg : g ∈ G
  · exact action.function_entry_iff unionCode.function (fun n => (codes n).function) n
      (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
  · constructor
    · intro entry
      exact (hg (ZFSet.pair_mem_prod.1
        (ZFSet.pair_mem_prod.1 (unionCode.function.1 entry)).1).1).elim
    · intro entry
      exact (hg (ZFSet.pair_mem_prod.1
        (ZFSet.pair_mem_prod.1 ((codes n).function.1 entry)).1).1).elim

end PartitionPilot.Forcing.NatUnionCode

end

end OAI
