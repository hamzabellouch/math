import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTemplateIntervalFamilies

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Bs brs Hs : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Bs brs Hs)

theorem heightImageCandidate_iff (i : {i : ZFSet.{u} // i ∈ I}) (R : ZFSet.{u}) :
    heightImageCandidate Qs Bs Hs i.val R ↔
      R = relationImage (d.space i) (t.ranges.value i) (t.heights.value i) := by
  constructor
  · rintro ⟨Q, _, B, _, h, _, eQ, eB, eh, equal⟩
    have eqQ := d.spaces.unique eQ (d.space_entry i)
    have eqB := t.ranges.unique eB (t.ranges.value_entry i)
    have eqh := t.heights.unique eh (t.heights.value_entry i)
    exact eqQ ▸ eqB ▸ eqh ▸ equal
  · intro equal
    exact ⟨d.space i, d.spaces.value_mem_doubleUnion i,
      t.ranges.value i, t.ranges.value_mem_doubleUnion i,
      t.heights.value i, t.heights.value_mem_doubleUnion i,
      d.space_entry i, t.ranges.value_entry i, t.heights.value_entry i, equal⟩

end TemplateHeightFamilyInputs

theorem heightOrderCandidate_iff {I Rs brs : ZFSet.{u}}
    (ranges : FunctionGraphOn I Rs) (orders : FunctionGraphOn I brs)
    (i : {i : ZFSet.{u} // i ∈ I}) (r : ZFSet.{u}) :
    heightOrderCandidate Rs brs i.val r ↔
      r = heightOrderRestriction (ranges.value i) (orders.value i) := by
  constructor
  · rintro ⟨R, _, s, _, eR, es, equal⟩
    exact ranges.unique eR (ranges.value_entry i) ▸ orders.unique es (orders.value_entry i) ▸ equal
  · intro equal
    exact ⟨ranges.value i, ranges.value_mem_doubleUnion i,
      orders.value i, orders.value_mem_doubleUnion i,
      ranges.value_entry i, orders.value_entry i, equal⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightImageFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Qs Bs Hs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hBs : Bs ∈ M.sets) (hHs : Hs ∈ M.sets) : heightImageFamily I W Qs Bs Hs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have bBound := M.union_mem unions (M.union_mem unions hBs)
  have hBound := M.union_mem unions (M.union_mem unions hHs)
  let params := extend I (extend W (extend Qs (extend Bs (extend Hs
    (extend (⋃₀ ⋃₀ Qs) (extend (⋃₀ ⋃₀ Bs) (extend (⋃₀ ⋃₀ Hs) Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hQs (Fin.cases hBs (Fin.cases hHs
      (Fin.cases qBound (Fin.cases bBound (Fin.cases hBound (fun i => Fin.elim0 i)))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod I W) = heightImageFamily I W Qs Bs Hs := by
    apply ZFSet.ext
    intro z
    rw [heightImageFamily, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8 _ rfl rfl rfl)
  exact equal ▸ selected

theorem heightOrderFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Rs brs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hRs : Rs ∈ M.sets) (hbrs : brs ∈ M.sets) :
    heightOrderFamily I W Rs brs ∈ M.sets := by
  have rBound := M.union_mem unions (M.union_mem unions hRs)
  have sBound := M.union_mem unions (M.union_mem unions hbrs)
  let params := extend I (extend W (extend Rs (extend brs
    (extend (⋃₀ ⋃₀ Rs) (extend (⋃₀ ⋃₀ brs) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightOrderFamilyEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hRs (Fin.cases hbrs
      (Fin.cases rBound (Fin.cases sBound (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightOrderFamilyEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod I W) = heightOrderFamily I W Rs brs := by
    apply ZFSet.ext
    intro z
    rw [heightOrderFamily, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightOrderFamilyEntryFormula 0 1 2 3 4 5 6 _ rfl rfl)
  exact equal ▸ selected

theorem exists_templateHeightRanges
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss Bs brs Hs : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t₀ : TemplateHeightFamilyInputs d Bs brs Hs)
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hBs : Bs ∈ M.sets)
    (hbrs : brs ∈ M.sets) (hHs : Hs ∈ M.sets) :
    ∃ Rs ∈ M.sets, ∃ ors ∈ M.sets, ∃ t : TemplateHeightFamilyInputs d Rs ors Hs,
      (∀ i, t.ranges.value i = relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i)) ∧
      (∀ i, t.orders.value i = heightOrderRestriction (t.ranges.value i) (t₀.orders.value i)) := by
  let B := familyPointBound Bs
  have hB : B ∈ M.sets := M.familyPointBound_mem unions hBs
  let W := M.groundPower B
  have hW : W ∈ M.sets := M.groundPower_mem powers hB
  let Rs := heightImageFamily I W Qs Bs Hs
  have hRs : Rs ∈ M.sets := M.heightImageFamily_mem pairing unions powers separation hI hW hQs hBs hHs
  have imageGround (i : {i : ZFSet.{u} // i ∈ I}) :
      relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i) ∈ M.sets :=
    M.relationImage_mem separation (d.spaces.value_mem M hQs i)
      (t₀.ranges.value_mem M hBs i) (t₀.heights.value_mem M hHs i)
  have imageBound (i : {i : ZFSet.{u} // i ∈ I}) :
      relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i) ⊆ B := by
    intro a ha
    exact mem_familyPointBound_of_entry (t₀.ranges.value_entry i) ((mem_relationImage _ _ _ a).1 ha).1
  have rangesFunction : ZFSet.IsFunc I W Rs := by
    refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
    intro i hi
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    let R := relationImage (d.space j) (t₀.ranges.value j) (t₀.heights.value j)
    have hR : R ∈ W := (M.mem_groundPower B R).2 ⟨imageGround j, imageBound j⟩
    exact ⟨R, (pair_mem_heightImageFamily I W Qs Bs Hs i R).2
      ⟨hi, hR, (t₀.heightImageCandidate_iff j R).2 rfl⟩,
      fun R' entry => (t₀.heightImageCandidate_iff j R').1
        ((pair_mem_heightImageFamily I W Qs Bs Hs i R').1 entry).2.2⟩
  let ranges : FunctionGraphOn I Rs := ⟨W, rangesFunction⟩
  have rangesEqual (i : {i : ZFSet.{u} // i ∈ I}) :
      ranges.value i = relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i) :=
    (t₀.heightImageCandidate_iff i _).1
      ((pair_mem_heightImageFamily I W Qs Bs Hs i.val _).1 (ranges.value_entry i)).2.2
  have rangesBound (i : {i : ZFSet.{u} // i ∈ I}) : ranges.value i ⊆ B :=
    rangesEqual i ▸ imageBound i
  let U := M.groundRelations B B
  have hU : U ∈ M.sets := M.groundRelations_mem pairing unions powers separation hB hB
  let ors := heightOrderFamily I U Rs brs
  have hors : ors ∈ M.sets := M.heightOrderFamily_mem pairing unions powers separation hI hU hRs hbrs
  have ordersFunction : ZFSet.IsFunc I U ors := by
    refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
    intro i hi
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    let r := heightOrderRestriction (ranges.value j) (t₀.orders.value j)
    have hr : r ∈ M.sets := M.injection_restriction_mem separation
      (ranges.value_mem M hRs j) (ranges.value_mem M hRs j) (t₀.orders.value_mem M hbrs j)
    have bound : r ⊆ ZFSet.prod B B := by
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).2
      exact ZFSet.pair_mem_prod.2 ⟨rangesBound j ha, rangesBound j hb⟩
    exact ⟨r, (pair_mem_heightOrderFamily I U Rs brs i r).2
      ⟨hi, (M.mem_groundRelations B B r).2 ⟨hr, bound⟩,
        (heightOrderCandidate_iff ranges t₀.orders j r).2 rfl⟩,
      fun s entry => (heightOrderCandidate_iff ranges t₀.orders j s).1
        ((pair_mem_heightOrderFamily I U Rs brs i s).1 entry).2.2⟩
  let orders : FunctionGraphOn I ors := ⟨U, ordersFunction⟩
  have ordersEqual (i : {i : ZFSet.{u} // i ∈ I}) :
      orders.value i = heightOrderRestriction (ranges.value i) (t₀.orders.value i) :=
    (heightOrderCandidate_iff ranges t₀.orders i _).1
      ((pair_mem_heightOrderFamily I U Rs brs i.val _).1 (orders.value_entry i)).2.2
  have functions (i : {i : ZFSet.{u} // i ∈ I}) :
      ZFSet.IsFunc (d.space i) (ranges.value i) (t₀.heights.value i) := by
    rw [rangesEqual i]
    exact function_on_relationImage (t₀.function i)
  let t : TemplateHeightFamilyInputs d Rs ors Hs :=
    { ranges := ranges
      orders := orders
      heights := t₀.heights
      linear := fun i => by
        rw [ordersEqual i]
        apply heightOrderRestriction_linear (t₀.linear i)
        intro a ha
        rw [rangesEqual i] at ha
        exact ((mem_relationImage _ _ _ a).1 ha).1
      function := functions
      strict := fun i x y a b below different first second => by
        rw [ordersEqual i]
        exact (pair_mem_heightOrderRestriction _ _ a b).2
          ⟨t₀.strict i x y a b below different first second,
            (ZFSet.pair_mem_prod.1 ((functions i).1 first)).2,
            (ZFSet.pair_mem_prod.1 ((functions i).1 second)).2⟩ }
  exact ⟨Rs, hRs, ors, hors, t, rangesEqual, ordersEqual⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
