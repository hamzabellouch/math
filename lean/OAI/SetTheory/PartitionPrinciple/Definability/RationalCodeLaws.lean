import OAI.SetTheory.PartitionPrinciple.Forcing.CodedDenseOrders

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.RationalHeights
universe u

theorem fractionEquivalence_code : EquivalenceRelationCode fractionCarrier.{u} fractionEquivGraph := by
  refine ⟨fractionEquivGraph_subset, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 hx
    exact (pair_mem_fractionEquivGraph a a).2 rfl
  · intro x y hxy
    have shape := ZFSet.pair_mem_prod.1 (fractionEquivGraph_subset hxy)
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 shape.1
    obtain ⟨b, rfl⟩ := (mem_fractionCarrier y).1 shape.2
    exact (pair_mem_fractionEquivGraph b a).2 ((pair_mem_fractionEquivGraph a b).1 hxy).symm
  · intro x y z hxy hyz
    have shape := ZFSet.pair_mem_prod.1 (fractionEquivGraph_subset hxy)
    have zmem := (ZFSet.pair_mem_prod.1 (fractionEquivGraph_subset hyz)).2
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 shape.1
    obtain ⟨b, rfl⟩ := (mem_fractionCarrier y).1 shape.2
    obtain ⟨d, rfl⟩ := (mem_fractionCarrier z).1 zmem
    exact (pair_mem_fractionEquivGraph a d).2 (Fraction.equiv_trans
      ((pair_mem_fractionEquivGraph a b).1 hxy) ((pair_mem_fractionEquivGraph b d).1 hyz))

noncomputable def rationalCarrier (c : ZFSet.{u}) : ZFSet.{u} :=
  canonicalRepresentatives fractionCarrier fractionEquivGraph c

theorem rationalCarrier_subset (c : ZFSet.{u}) : rationalCarrier c ⊆ fractionCarrier :=
  canonicalRepresentatives_subset _ _ _

noncomputable def rationalEncode {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r : Rational) : ZFSet.{u} :=
  Classical.choose (canonical_exists_unique fractionEquivalence_code hc
    (fractionEncode_mem (Rational.representative r)))

theorem rationalEncode_spec {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r : Rational) :
    rationalEncode hc r ∈ rationalCarrier c ∧
      ZFSet.pair (fractionEncode (Rational.representative r)) (rationalEncode hc r) ∈ fractionEquivGraph :=
  (Classical.choose_spec (canonical_exists_unique fractionEquivalence_code hc
    (fractionEncode_mem (Rational.representative r)))).1

theorem rationalEncode_class {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r : Rational) :
    ∃ a : Fraction, fractionEncode a = rationalEncode hc r ∧ Rational.mk a = r := by
  have spec := rationalEncode_spec hc r
  obtain ⟨a, ha⟩ := (mem_fractionCarrier _).1 (rationalCarrier_subset c spec.1)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at spec
  have eq := (Rational.mk_eq_iff _ _).2 ((pair_mem_fractionEquivGraph _ _).1 spec.2)
  exact eq.symm.trans (Rational.representative_eq r)

theorem rationalEncode_injective {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) : Function.Injective (rationalEncode hc) := by
  intro r s eq
  obtain ⟨a, ha, ar⟩ := rationalEncode_class hc r
  obtain ⟨b, hb, bs⟩ := rationalEncode_class hc s
  have ab := fractionEncode_injective (ha.trans (eq.trans hb.symm))
  exact ar.symm.trans ((congrArg Rational.mk ab).trans bs)

theorem rationalEncode_of_canonical {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (a : Fraction)
    (ha : fractionEncode a ∈ rationalCarrier c) :
    rationalEncode hc (Rational.mk a) = fractionEncode a := by
  have unique := (Classical.choose_spec (canonical_exists_unique fractionEquivalence_code hc
    (fractionEncode_mem (Rational.representative (Rational.mk a))))).2
  exact (unique (fractionEncode a) ⟨ha,
    (pair_mem_fractionEquivGraph _ _).2 (Rational.representative_equiv a)⟩).symm

noncomputable def rationalPresentation {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) : Presentation (ULift.{u} Rational) where
  carrier := rationalCarrier c
  encode r := rationalEncode hc r.down
  injective := fun _ _ eq => ULift.ext _ _ (rationalEncode_injective hc eq)
  mem_carrier x := by
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (mem_fractionCarrier _).1 (rationalCarrier_subset c hx)
      exact ⟨⟨Rational.mk a⟩, rationalEncode_of_canonical hc a hx⟩
    · rintro ⟨r, rfl⟩
      exact (rationalEncode_spec hc r.down).1

noncomputable def rationalLtGraph (c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod (rationalCarrier c) (rationalCarrier c)) fractionLtGraph

theorem rationalLtGraph_subset (c : ZFSet.{u}) :
    rationalLtGraph c ⊆ ZFSet.prod (rationalCarrier c) (rationalCarrier c) :=
  fun _ h => (ZFSet.mem_sep.1 h).2

theorem pair_mem_rationalLtGraph {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r s : Rational) :
    ZFSet.pair (rationalEncode hc r) (rationalEncode hc s) ∈ rationalLtGraph c ↔ Rational.lt r s := by
  have first := (rationalEncode_spec hc r).1
  have second := (rationalEncode_spec hc s).1
  rw [rationalLtGraph, ZFSet.mem_sep]
  have lookup : ZFSet.pair (rationalEncode hc r) (rationalEncode hc s) ∈ fractionLtGraph ↔
      Rational.lt r s := by
    obtain ⟨a, ha, ar⟩ := rationalEncode_class hc r
    obtain ⟨b, hb, bs⟩ := rationalEncode_class hc s
    rw [← ha, ← hb, pair_mem_fractionLtGraph, ← ar, ← bs]
    exact Iff.rfl
  exact ⟨fun h => lookup.1 h.1,
    fun h => ⟨lookup.2 h, ZFSet.pair_mem_prod.2 ⟨first, second⟩⟩⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open Compression.RecursiveMaps.RationalHeights
universe u

theorem rational_denseOrderCode {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) :
    DenseOrderCode (rationalCarrier c) (rationalLtGraph c) := by
  refine ⟨⟨rationalLtGraph_subset c, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 hx
    exact fun h => Rational.irrefl a.down ((pair_mem_rationalLtGraph hc _ _).1 h)
  · intro x y z xy yz
    have shape := ZFSet.pair_mem_prod.1 (rationalLtGraph_subset c xy)
    have hz := (ZFSet.pair_mem_prod.1 (rationalLtGraph_subset c yz)).2
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 shape.1
    obtain ⟨b, rfl⟩ := ((rationalPresentation hc).mem_carrier y).1 shape.2
    obtain ⟨d, rfl⟩ := ((rationalPresentation hc).mem_carrier z).1 hz
    exact (pair_mem_rationalLtGraph hc _ _).2 (Rational.trans
      ((pair_mem_rationalLtGraph hc _ _).1 xy) ((pair_mem_rationalLtGraph hc _ _).1 yz))
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := ((rationalPresentation hc).mem_carrier y).1 hy
    rcases Rational.compare a.down b.down with less | same | more
    · exact Or.inl ((pair_mem_rationalLtGraph hc _ _).2 less)
    · exact Or.inr (Or.inl (congrArg (rationalEncode hc) same))
    · exact Or.inr (Or.inr ((pair_mem_rationalLtGraph hc _ _).2 more))
  · intro x y xy
    have shape := ZFSet.pair_mem_prod.1 (rationalLtGraph_subset c xy)
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 shape.1
    obtain ⟨b, rfl⟩ := ((rationalPresentation hc).mem_carrier y).1 shape.2
    obtain ⟨d, ad, db⟩ := Rational.between _ _ ((pair_mem_rationalLtGraph hc _ _).1 xy)
    exact ⟨rationalEncode hc d, (rationalEncode_spec hc d).1,
      (pair_mem_rationalLtGraph hc _ _).2 ad, (pair_mem_rationalLtGraph hc _ _).2 db⟩

theorem rationalCarrier_nonempty {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) : ∃ x, x ∈ rationalCarrier c :=
  ⟨rationalEncode hc (Rational.mk ⟨0, 1, by decide⟩), (rationalEncode_spec hc _).1⟩

theorem rational_no_endpoints {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) :
    ∀ x ∈ rationalCarrier c,
      (∃ y ∈ rationalCarrier c, ZFSet.pair y x ∈ rationalLtGraph c) ∧
      (∃ y ∈ rationalCarrier c, ZFSet.pair x y ∈ rationalLtGraph c) := by
  intro x hx
  obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 hx
  obtain ⟨b, ba⟩ := Rational.unbounded_below a.down
  obtain ⟨d, ad⟩ := Rational.unbounded_above a.down
  exact ⟨⟨rationalEncode hc b, (rationalEncode_spec hc b).1,
      (pair_mem_rationalLtGraph hc _ _).2 ba⟩,
    ⟨rationalEncode hc d, (rationalEncode_spec hc d).1,
      (pair_mem_rationalLtGraph hc _ _).2 ad⟩⟩

end PartitionPilot.Forcing

end OAI
