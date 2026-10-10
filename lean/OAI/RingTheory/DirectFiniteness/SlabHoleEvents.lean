import OAI.RingTheory.DirectFiniteness.EventLoad

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

lemma diff_mem_coset {j : R × Q} (C : AffineCoset (F.U j)) {x y : A}
    (hx : x ∈ C.val) (hy : y ∈ C.val) : y-x ∈ F.U j := by
  have he := (AffineCoset.eq_of_mem _ hy).trans (AffineCoset.eq_of_mem _ hx).symm
  exact (AffineCoset.of_eq_iff _ _ _).mp he

abbrev LocalHolePair (v : SlabVariable F) :=
  {xy : ↥(O ∩ v.2.val) × ↥(O ∩ v.2.val) // xy.1 ≠ xy.2}

lemma localHolePair_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (v : SlabVariable F) : Fintype.card (F.LocalHolePair O v) ≤ 100^2 := by
  apply le_trans (Fintype.card_subtype_le _)
  simp only [Fintype.card_prod,Fintype.card_coe]
  simpa only [pow_two] using Nat.mul_self_le_mul_self (F.holes_in_coset_card S O hO v.1 v.2)

def localHolePairVector (v : SlabVariable F) (p : F.LocalHolePair O v) : Q × E :=
  (F.diff_mem_coset v.2 (Finset.mem_inter.mp p.val.1.property).2
    (Finset.mem_inter.mp p.val.2.property).2).choose

lemma localHolePairVector_eq (v : SlabVariable F) (p : F.LocalHolePair O v) :
    F.u v.1 (F.localHolePairVector O v p) = p.val.2.val-p.val.1.val :=
  (F.diff_mem_coset v.2 (Finset.mem_inter.mp p.val.1.property).2
    (Finset.mem_inter.mp p.val.2.property).2).choose_spec

lemma localHolePairVector_nonzero
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (v : SlabVariable F) (p : F.LocalHolePair O v) : (F.localHolePairVector O v p).2 ≠ 0 := by
  apply F.different_holes_nonzero_component S O hO v.1
    (Finset.mem_inter.mp p.val.1.property).1 (Finset.mem_inter.mp p.val.2.property).1
    (fun h => p.property (Subtype.ext h.symm))
  exact F.localHolePairVector_eq O v p

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
