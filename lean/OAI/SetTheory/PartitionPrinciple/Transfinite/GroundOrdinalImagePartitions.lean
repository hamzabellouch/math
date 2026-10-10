import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def ordinalFirstRelation (delta Y R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ delta, ∃ y ∈ Y,
    z = ZFSet.pair i y ∧ ∀ k ∈ i, ZFSet.pair k y ∉ R) R

theorem pair_mem_ordinalFirstRelation (delta Y R i y : ZFSet.{u}) :
    ZFSet.pair i y ∈ ordinalFirstRelation delta Y R ↔
      ZFSet.pair i y ∈ R ∧ i ∈ delta ∧ y ∈ Y ∧ ∀ k ∈ i, ZFSet.pair k y ∉ R := by
  rw [ordinalFirstRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨entry, j, hj, z, hz, equal, least⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨entry, hj, hz, least⟩
  · rintro ⟨entry, hi, hy, least⟩
    exact ⟨entry, i, hi, y, hy, rfl, least⟩

namespace BoundedFormula
private def firstRelationEntryFormula {n} (z delta Y R : Fin n) : BoundedFormula n :=
  exMem delta (exMem Y.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.allMem 1 (.neg (pairMembershipFormula 0 1 R.succ.succ.succ)))))

private theorem firstRelationEntry_meaning {n} (z delta Y R : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (firstRelationEntryFormula z delta Y R) env ↔
      ∃ i ∈ env delta, ∃ y ∈ env Y, env z = ZFSet.pair i y ∧
        ∀ k ∈ i, ZFSet.pair k y ∉ env R := by
  simp only [firstRelationEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (N : TransitiveGround.{u})

theorem ordinalFirstRelation_mem (separation : SeparationSchema N.sets)
    {delta Y R : ZFSet.{u}} (hDelta : delta ∈ N.sets) (hY : Y ∈ N.sets) (hR : R ∈ N.sets) :
    ordinalFirstRelation delta Y R ∈ N.sets := by
  let params := extend delta (extend Y (extend R Fin.elim0))
  have ground := N.bounded_separation_mem separation
    (BoundedFormula.firstRelationEntryFormula 0 1 2 3) params
    (Fin.cases hDelta (Fin.cases hY (Fin.cases hR (fun j => Fin.elim0 j)))) hR
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.firstRelationEntryFormula 0 1 2 3) (extend z params)) R =
      ordinalFirstRelation delta Y R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ordinalFirstRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.firstRelationEntry_meaning _ _ _ _ _)
  exact equal ▸ ground

theorem ordinal_image_partitions
    (zf : ZFRealization N.sets) {delta X Y R f : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (ordinal : ordinalSetProperty delta)
    (hX : X ∈ N.sets) (hY : Y ∈ N.sets) (hR : R ∈ N.sets) (hf : f ∈ N.sets)
    (relation : R ⊆ ZFSet.prod delta X) (function : ZFSet.IsFunc X Y f)
    (onto : ∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f)
    (coverX : ∀ x ∈ X, ∃ i ∈ delta, ZFSet.pair i x ∈ R) :
    ∃ p ∈ N.sets, ∃ q ∈ N.sets,
      FunctionGraphOn delta p ∧ FunctionGraphOn delta q ∧
      (∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X) ∧
      (∀ y ∈ Y, ∃ i ∈ delta, ∃ U, ZFSet.pair i U ∈ p ∧ y ∈ U) ∧
      (∀ i k U V y, ZFSet.pair i U ∈ p → ZFSet.pair k V ∈ p → y ∈ U → y ∈ V → i = k) ∧
      (∀ i k U V x, ZFSet.pair i U ∈ q → ZFSet.pair k V ∈ q → x ∈ U → x ∈ V → i = k) ∧
      ∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
        (∀ y, y ∈ U ↔ y ∈ Y ∧
          (∃ x ∈ X, ZFSet.pair i x ∈ R ∧ ZFSet.pair x y ∈ f) ∧
          ∀ k ∈ i, ¬ ∃ x ∈ X, ZFSet.pair k x ∈ R ∧ ZFSet.pair x y ∈ f) ∧
        (∀ x, x ∈ V ↔ ZFSet.pair i x ∈ R ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f) ∧
        graphRestriction V f ∈ N.sets ∧ ZFSet.IsFunc V U (graphRestriction V f) ∧
        ∀ y ∈ U, ∃ x ∈ V, ZFSet.pair x y ∈ graphRestriction V f := by
  have pairing := zf.1.2.2.2.1
  have unions := zf.1.2.2.2.2.1
  have powers := zf.1.2.2.2.2.2.1
  have separation : SeparationSchema N.sets := zf.2.1
  let image := relationCompose delta X Y R f
  have hImage : image ∈ N.sets := N.relationCompose_mem pairing unions powers separation hDelta hX hY hR hf
  have imageEntries (i y : ZFSet.{u}) : ZFSet.pair i y ∈ image ↔
      i ∈ delta ∧ y ∈ Y ∧ ∃ x ∈ X, ZFSet.pair i x ∈ R ∧ ZFSet.pair x y ∈ f :=
    pair_mem_relationCompose _ _ _ _ _ _ _
  let first := ordinalFirstRelation delta Y image
  have hFirst : first ∈ N.sets := N.ordinalFirstRelation_mem separation hDelta hY hImage
  have firstUnique (i k y : ZFSet.{u}) (iy : ZFSet.pair i y ∈ first)
      (ky : ZFSet.pair k y ∈ first) : i = k := by
    have a := (pair_mem_ordinalFirstRelation delta Y image i y).1 iy
    have b := (pair_mem_ordinalFirstRelation delta Y image k y).1 ky
    rcases ordinalSetProperty_mem_compare ordinal a.2.1 b.2.1 with less | equal | greater
    · exact (b.2.2.2 i less a.1).elim
    · exact equal
    · exact (a.2.2.2 k greater b.1).elim
  let preimage := relationCompose delta Y X first (relationConverse X Y f)
  have hPreimage : preimage ∈ N.sets := N.relationCompose_mem pairing unions powers separation hDelta hY hX
    hFirst (N.relationConverse_mem pairing unions powers separation hX hY hf)
  let selected := ZFSet.sep (fun z => z ∈ preimage) R
  have hSelected : selected ∈ N.sets := by
    exact N.bounded_separation_mem separation (.mem 0 1) (extend preimage Fin.elim0)
      (Fin.cases hPreimage (fun j => Fin.elim0 j)) hR
  let p := N.relationFiberFamily delta Y first
  let q := N.relationFiberFamily delta X selected
  have hp := N.relationFiberFamily_mem pairing unions powers separation hDelta hY hFirst
  have hq := N.relationFiberFamily_mem pairing unions powers separation hDelta hX hSelected
  have pFunction : FunctionGraphOn delta p :=
    ⟨N.groundPower Y, N.relationFiberFamily_function separation hDelta hY hFirst⟩
  have qFunction : FunctionGraphOn delta q :=
    ⟨N.groundPower X, N.relationFiberFamily_function separation hDelta hX hSelected⟩
  have pEntries (i U : ZFSet.{u}) (entry : ZFSet.pair i U ∈ p) (y : ZFSet.{u}) :
      y ∈ U ↔ y ∈ Y ∧ ZFSet.pair i y ∈ first := by
    have equal := ((N.pair_mem_relationFiberFamily delta Y first i U).1 entry).2.2
    rw [equal, mem_relationFiber]
  have qEntries (i V : ZFSet.{u}) (entry : ZFSet.pair i V ∈ q) (x : ZFSet.{u}) :
      x ∈ V ↔ x ∈ X ∧ ZFSet.pair i x ∈ selected := by
    have equal := ((N.pair_mem_relationFiberFamily delta X selected i V).1 entry).2.2
    rw [equal, mem_relationFiber]
  have sourceEntries (i U V : ZFSet.{u}) (ip : ZFSet.pair i U ∈ p) (iq : ZFSet.pair i V ∈ q)
      (x : ZFSet.{u}) : x ∈ V ↔ ZFSet.pair i x ∈ R ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f := by
    rw [qEntries i V iq x]
    constructor
    · rintro ⟨hx, entry⟩
      obtain ⟨ix, back⟩ := ZFSet.mem_sep.1 entry
      obtain ⟨_, _, y, hy, firstEntry, converse⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 back
      exact ⟨ix, y, (pEntries i U ip y).2 ⟨hy, firstEntry⟩,
        ((pair_mem_relationConverse X Y f x y).1 converse).2.2⟩
    · rintro ⟨ix, y, hy, xy⟩
      have shape := ZFSet.pair_mem_prod.1 (relation ix)
      have firstEntry := (pEntries i U ip y).1 hy
      exact ⟨shape.2, ZFSet.mem_sep.2 ⟨ix,
        (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨shape.1, shape.2, y, firstEntry.1, firstEntry.2,
          (pair_mem_relationConverse X Y f x y).2 ⟨shape.2, firstEntry.1, xy⟩⟩⟩⟩
  refine ⟨p, hp, q, hq, pFunction, qFunction, ?_, ?_, ?_, ?_, ?_⟩
  · intro i U V ip iq
    exact ⟨fun y hy => ((pEntries i U ip y).1 hy).1,
      fun x hx => ((qEntries i V iq x).1 hx).1⟩
  · intro y hy
    obtain ⟨x, hx, xy⟩ := onto y hy
    obtain ⟨j, hj, jx⟩ := coverX x hx
    let indices : Set ZFSet.{u} := {i | i ∈ delta ∧ ZFSet.pair i y ∈ image}
    have inhabited : indices.Nonempty := ⟨j, hj, (imageEntries j y).2 ⟨hj, hy, x, hx, jx, xy⟩⟩
    obtain ⟨i, hi, least⟩ := ZFSet.mem_wf.has_min indices inhabited
    obtain ⟨U, ip⟩ := pFunction.total hi.1
    refine ⟨i, hi.1, U, ip, (pEntries i U ip y).2 ⟨hy, ?_⟩⟩
    exact (pair_mem_ordinalFirstRelation delta Y image i y).2
      ⟨hi.2, hi.1, hy, fun k ki entry => least k ⟨ordinal.1 i hi.1 k ki, entry⟩ ki⟩
  · intro i k U V y ip kp hy hy'
    exact firstUnique i k y ((pEntries i U ip y).1 hy).2 ((pEntries k V kp y).1 hy').2
  · intro i k U V x iq kq hx hx'
    obtain ⟨A, ip⟩ := pFunction.total (qFunction.pair_source iq)
    obtain ⟨B, kp⟩ := pFunction.total (qFunction.pair_source kq)
    obtain ⟨_, y, hy, xy⟩ := (sourceEntries i A U ip iq x).1 hx
    obtain ⟨_, z, hz, xz⟩ := (sourceEntries k B V kp kq x).1 hx'
    obtain ⟨v, _, unique⟩ := function.2 x ((qEntries i U iq x).1 hx).1
    have equal : z = y := (unique z xz).trans (unique y xy).symm
    subst z
    exact firstUnique i k y ((pEntries i A ip y).1 hy).2 ((pEntries k B kp y).1 hz).2
  · intro i U V ip iq
    have hi := pFunction.pair_source ip
    have hV : V ∈ N.sets := N.transitive (N.union_mem unions (N.union_mem unions hq))
      (pair_second_mem_doubleUnion iq)
    have maps (x y : ZFSet.{u}) (hx : x ∈ V) (xy : ZFSet.pair x y ∈ f) : y ∈ U := by
      obtain ⟨_, z, hz, xz⟩ := (sourceEntries i U V ip iq x).1 hx
      obtain ⟨v, _, unique⟩ := function.2 x ((qEntries i V iq x).1 hx).1
      have equal : y = z := (unique y xy).trans (unique z xz).symm
      exact equal.symm ▸ hz
    refine ⟨?_, sourceEntries i U V ip iq, N.graphRestriction_mem unions separation hV hf, ?_, ?_⟩
    · intro y
      rw [pEntries i U ip y]
      constructor
      · rintro ⟨hy, entry⟩
        have firstEntry := (pair_mem_ordinalFirstRelation delta Y image i y).1 entry
        exact ⟨hy, ((imageEntries i y).1 firstEntry.1).2.2,
          fun k ki witness => firstEntry.2.2.2 k ki
            ((imageEntries k y).2 ⟨ordinal.1 i hi k ki, hy, witness⟩)⟩
      · rintro ⟨hy, witness, least⟩
        exact ⟨hy, (pair_mem_ordinalFirstRelation delta Y image i y).2
          ⟨(imageEntries i y).2 ⟨hi, hy, witness⟩, hi, hy,
            fun k ki entry => least k ki ((imageEntries k y).1 entry).2.2⟩⟩
    · refine ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨x, hx, y, rfl, xy⟩ := mem_graphRestriction.1 hz
        exact ZFSet.pair_mem_prod.2 ⟨hx, maps x y hx xy⟩
      · intro x hx
        obtain ⟨y, xy, unique⟩ := function.2 x ((qEntries i V iq x).1 hx).1
        exact ⟨y, pair_mem_graphRestriction.2 ⟨xy, hx⟩,
          fun z xz => unique z (pair_mem_graphRestriction.1 xz).1⟩
    · intro y hy
      have firstEntry := ((pEntries i U ip y).1 hy).2
      obtain ⟨x, hx, ix, xy⟩ := ((imageEntries i y).1
        ((pair_mem_ordinalFirstRelation delta Y image i y).1 firstEntry).1).2.2
      have inV := (sourceEntries i U V ip iq x).2 ⟨ix, y, hy, xy⟩
      exact ⟨x, inV, pair_mem_graphRestriction.2 ⟨xy, inV⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
