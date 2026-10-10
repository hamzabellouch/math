import OAI.RingTheory.DirectFiniteness.LexicographicOrder

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription

local instance two_neZero : NeZero (2 : ℕ) := inferInstance

local instance polynomialResidueOrder : LinearOrder (ZMod 2) := @residueOrder 2 two_neZero
local instance polynomialVectorOrder (d : ℕ) : LinearOrder (Fin (d+1) → ZMod 2) := vectorOrder

def irreducibleCoeffs (d : ℕ) (c : Fin (d+1) → ZMod 2) : Prop :=
  (ofFn (d+1) c).Monic ∧ (ofFn (d+1) c).natDegree=d ∧ Irreducible (ofFn (d+1) c)

lemma irreducibleCoeffs_exists (d : ℕ) (hd : 0 < d) : ∃ c, irreducibleCoeffs d c := by
  let K := GaloisField 2 d
  let b := Field.powerBasisOfFiniteOfSeparable (ZMod 2) K
  have hb : b.dim=d := b.finrank.symm.trans (GaloisField.finrank 2 (Nat.ne_of_gt hd))
  have hi := b.isIntegral_gen
  have hdeg : (minpoly (ZMod 2) b.gen).natDegree=d := b.natDegree_minpoly.trans hb
  refine ⟨toFn (d+1) (minpoly (ZMod 2) b.gen),?_⟩
  unfold irreducibleCoeffs
  rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : (minpoly (ZMod 2) b.gen).natDegree < d+1)]
  exact ⟨minpoly.monic hi,hdeg,minpoly.irreducible hi⟩

def firstCoeffs (d : ℕ) (hd : 0 < d) : Fin (d+1) → ZMod 2 :=
  first (irreducibleCoeffs d) (irreducibleCoeffs_exists d hd)

def firstPolynomial (d : ℕ) (hd : 0 < d) : (ZMod 2)[X] := ofFn (d+1) (firstCoeffs d hd)

lemma firstPolynomial_monic (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).Monic :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).1
lemma firstPolynomial_degree (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).natDegree=d :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.1
lemma firstPolynomial_irreducible (d : ℕ) (hd : 0 < d) : Irreducible (firstPolynomial d hd) :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.2
lemma firstCoeffs_le (d : ℕ) (hd : 0 < d) (c : Fin (d+1) → ZMod 2)
    (hc : irreducibleCoeffs d c) : toLex (firstCoeffs d hd) ≤ toLex c :=
  first_le _ (irreducibleCoeffs_exists d hd) c hc

/-- Exactly F₂[Z]/(g), with g the lexicographically first monic irreducible
polynomial of the prescribed degree. -/
abbrev CoefficientField (d : ℕ) (hd : 0 < d) := AdjoinRoot (firstPolynomial d hd)

instance firstPolynomial_fact (d : ℕ) (hd : 0 < d) : Fact (Irreducible (firstPolynomial d hd)) :=
  ⟨firstPolynomial_irreducible d hd⟩

instance coefficientField_finite (d : ℕ) (hd : 0 < d) : Finite (CoefficientField d hd) := by
  let : Module.Finite (ZMod 2) (CoefficientField d hd) :=
    (AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finite
  exact Module.finite_of_finite (ZMod 2)

instance coefficientField_fintype (d : ℕ) (hd : 0 < d) : Fintype (CoefficientField d hd) :=
  Fintype.ofFinite _

lemma coefficientField_finrank (d : ℕ) (hd : 0 < d) :
    finrank (ZMod 2) (CoefficientField d hd)=d := by
  rw [(AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim,firstPolynomial_degree]

lemma coefficientField_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CoefficientField d hd)=2^d := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,coefficientField_finrank]

@[instance_reducible] def coefficientFieldOrder (d : ℕ) (hd : 0 < d) :
    LinearOrder (CoefficientField d hd) :=
  letI : LinearOrder (Fin (firstPolynomial d hd).natDegree → ZMod 2) := vectorOrder
  LinearOrder.lift' (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun
    (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun.injective

end KaplanskyCounterexample.Prescription
end

end OAI
