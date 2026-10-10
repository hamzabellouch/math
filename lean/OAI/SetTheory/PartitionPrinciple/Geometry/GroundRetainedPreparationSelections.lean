import OAI.SetTheory.PartitionPrinciple.Definability.GroundVaryingPreparationRelations

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def retainedPreparationSelections (_M : TransitiveGround.{u})
    (A L R p levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x alpha row sourceA tail,
    z = ZFSet.pair x (ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail)) ∧
    ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair p tail) ∈ R ∧
    sourceA ⊆ A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ levels) (ZFSet.prod A L)

theorem pair_mem_retainedPreparationSelections (A L R p levels x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.retainedPreparationSelections A L R p levels ↔
      x ∈ A ∧ y ∈ L ∧ ∃ alpha row sourceA tail,
        y = ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail) ∧
        ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair p tail) ∈ R ∧
        sourceA ⊆ A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ levels := by
  rw [retainedPreparationSelections, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, x', alpha, row, sourceA, tail, equal, rest⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, alpha, row, sourceA, tail, value, rest⟩
  · rintro ⟨hx, hy, alpha, row, sourceA, tail, equal, rest⟩
    exact ⟨⟨hx, hy⟩, x, alpha, row, sourceA, tail, congrArg (ZFSet.pair x) equal, rest⟩

private def selectionBody {n} (z A R p levels : Fin n) : BoundedFormula (n + 10) :=
  let old := suffixIndex n 10
  let v := prefixIndex n 10
  .conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1))
    (.conj (BoundedFormula.orderedPairFormula (v 1) (v 2) (v 9))
      (.conj (BoundedFormula.orderedPairFormula (v 9) (v 3) (v 6))
        (.conj (BoundedFormula.orderedPairFormula (v 3) (v 4) (v 5))
          (.conj (BoundedFormula.orderedPairFormula (v 7) (v 2) (v 3))
            (.conj (BoundedFormula.orderedPairFormula (v 8) (old p) (v 6))
              (.conj (BoundedFormula.pairMembershipFormula (v 7) (v 8) (old R))
                (.conj (.allMem (v 5) (.mem 0 (old A).succ))
                  (.conj (.mem (v 0) (v 5))
                    (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old levels))))))))))

private def selectionFormula {n} (z A R p levels : Fin n) : SetFormula n :=
  exBlock 10 (selectionBody z A R p levels).toFormula

private theorem realize_selectionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z A R p levels : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (selectionFormula z A R p levels) env ↔
      ∃ x alpha row sourceA tail,
        env z = ZFSet.pair x (ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail)) ∧
        ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair (env p) tail) ∈ env R ∧
        sourceA ⊆ env A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ env levels := by
  rw [selectionFormula, realize_exBlock]
  have actual (w : Fin 10 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (selectionBody z A R p levels).toFormula (extendMany 10 w env) ↔
      env z = ZFSet.pair (w 0) (w 1) ∧ w 1 = ZFSet.pair (w 2) (w 9) ∧
      w 9 = ZFSet.pair (w 3) (w 6) ∧ w 3 = ZFSet.pair (w 4) (w 5) ∧
      w 7 = ZFSet.pair (w 2) (w 3) ∧ w 8 = ZFSet.pair (env p) (w 6) ∧
      ZFSet.pair (w 7) (w 8) ∈ env R ∧ w 5 ⊆ env A ∧ w 0 ∈ w 5 ∧
      ZFSet.pair (w 0) (w 2) ∈ env levels := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 10 w env ground members)]
    simp only [selectionBody, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix]
    rfl
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨outer, value, output, source, input, prepared, edge, subset, member, level⟩ :=
      (actual w ground).1 body
    refine ⟨w 0, w 2, w 4, w 5, w 6, ?_, ?_, subset, member, level⟩
    · simpa only [value, output, source] using outer
    · simpa only [input, prepared, source] using edge
  · rintro ⟨x, alpha, row, sourceA, tail, equal, edge, subset, member, level⟩
    have hz := equal ▸ members z
    have hx := M.pair_left hz
    have hy := M.pair_right hz
    have ha := M.pair_left hy
    have hout := M.pair_right hy
    have hsource := M.pair_left hout
    have htail := M.pair_right hout
    have hinput := M.orderedPair_mem pairing ha hsource
    have hprepared := M.orderedPair_mem pairing (members p) htail
    let w : Fin 10 → ZFSet.{u} := ![x, ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail),
      alpha, ZFSet.pair row sourceA, row, sourceA, tail,
      ZFSet.pair alpha (ZFSet.pair row sourceA), ZFSet.pair (env p) tail,
      ZFSet.pair (ZFSet.pair row sourceA) tail]
    have ground : ∀ j, w j ∈ M.sets := Fin.cases hx (Fin.cases hy (Fin.cases ha
      (Fin.cases hsource (Fin.cases (M.pair_left hsource) (Fin.cases (M.pair_right hsource)
        (Fin.cases htail (Fin.cases hinput (Fin.cases hprepared
          (Fin.cases hout (fun j => Fin.elim0 j))))))))))
    exact ⟨w, ground, (actual w ground).2
      ⟨equal, rfl, rfl, rfl, rfl, rfl, edge, subset, member, level⟩⟩

theorem retainedPreparationSelections_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L R p levels : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (hR : R ∈ M.sets) (hp : p ∈ M.sets) (hLevels : levels ∈ M.sets) :
    M.retainedPreparationSelections A L R p levels ∈ M.sets := by
  let params : Fin 4 → ZFSet.{u} := ![A, R, p, levels]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hR
    (Fin.cases hp (Fin.cases hLevels (fun j => Fin.elim0 j))))
  have bound := M.prod_mem pairing unions powers separation hA hL
  have selected := M.separation_mem separation (selectionFormula 0 1 2 3 4) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (selectionFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod A L) = M.retainedPreparationSelections A L R p levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, retainedPreparationSelections, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact realize_selectionFormula M pairing 0 1 2 3 4 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

theorem exists_retainedPreparationSelection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A L R p levels : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (hR : R ∈ M.sets) (hp : p ∈ M.sets) (hLevels : levels ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L,
      ZFSet.pair x y ∈ M.retainedPreparationSelections A L R p levels) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A L f ∧
      f ⊆ M.retainedPreparationSelections A L R p levels ∧
      relationImage A L f ∈ M.sets ∧ M.groundEmbeddable (relationImage A L f) ZFSet.omega :=
  M.exists_countableRelationSelection pairing unions powers separation infinite choice hA hL
    (M.retainedPreparationSelections_mem pairing unions powers separation hA hL hR hp hLevels)
    smallA total

end PartitionPilot.Forcing.TransitiveGround

end OAI
