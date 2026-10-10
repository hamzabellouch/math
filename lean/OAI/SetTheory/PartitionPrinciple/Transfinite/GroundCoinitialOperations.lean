import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableRelationSelections

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

def CoinitialBelowCode (order F target B : ZFSet.{u}) : Prop :=
  B ⊆ F ∧ ∀ x ∈ target, ∃ b ∈ B, ZFSet.pair b x ∈ order

namespace BoundedFormula

open SetFormula

def coinitialBelowFormula {n} (order F target B : Fin n) : BoundedFormula n :=
  .conj (.allMem B (.mem 0 F.succ))
    (.allMem target (exMem B.succ (pairMembershipFormula 0 1 order.succ.succ)))

theorem truth_coinitialBelowFormula {n} (order F target B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (coinitialBelowFormula order F target B) env ↔
      CoinitialBelowCode (env order) (env F) (env target) (env B) := by
  simp only [coinitialBelowFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem realize_coinitialBelowFormula (M : TransitiveGround.{u}) {n}
    (order F target B : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (coinitialBelowFormula order F target B).toFormula env ↔
      CoinitialBelowCode (env order) (env F) (env target) (env B) :=
  (realize_toFormula M _ env members).trans
    (truth_coinitialBelowFormula order F target B env)

end BoundedFormula

namespace TransitiveGround

def InternalCountableBelow (M : TransitiveGround.{u}) (order F target : ZFSet.{u}) : Prop :=
  ∃ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega ∧ CoinitialBelowCode order F target B

end TransitiveGround






noncomputable def copyPullback (A L e F : ZFSet.{u}) : ZFSet.{u} :=
  relationImage F A (relationConverse A L e)

theorem mem_copyPullback (A L e F x : ZFSet.{u}) :
    x ∈ copyPullback A L e F ↔
      x ∈ A ∧ ∃ y ∈ F, y ∈ L ∧ ZFSet.pair x y ∈ e := by
  rw [copyPullback, mem_relationImage]
  constructor
  · rintro ⟨hx, y, hy, rel⟩
    exact ⟨hx, y, hy, ((pair_mem_relationConverse A L e x y).1 rel).2⟩
  · rintro ⟨hx, y, hy, hyL, rel⟩
    exact ⟨hx, y, hy, (pair_mem_relationConverse A L e x y).2 ⟨hx, hyL, rel⟩⟩

theorem relationImage_copyPullback {A L e : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e) (F : ZFSet.{u}) :
    relationImage (copyPullback A L e F) L e = F ∩ relationImage A L e := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_inter, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    have equal : y = z := (unique y rel).trans (unique z relz).symm
    exact ⟨equal ▸ hz, hy, x, hxA, rel⟩
  · rintro ⟨hyF, hy, x, hx, rel⟩
    exact ⟨hy, x, (mem_copyPullback A L e F x).2 ⟨hx, y, hyF, hy, rel⟩, rel⟩

theorem CoinitialBelowCode.copy {A L e sourceOrder targetOrder F target B : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : CoinitialBelowCode sourceOrder (copyPullback A L e F) target B) :
    CoinitialBelowCode targetOrder F (relationImage target L e) (relationImage B L e) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage B L e y).1 hy
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 (basis.1 hx)
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    exact (unique y rel).trans (unique z relz).symm ▸ hz
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage target L e y).1 hy
    obtain ⟨b, hb, below⟩ := basis.2 x hx
    have hbA := ((mem_copyPullback A L e F b).1 (basis.1 hb)).1
    obtain ⟨b', relb, _⟩ := func.2 b hbA
    have hbL := (ZFSet.pair_mem_prod.1 (func.1 relb)).2
    exact ⟨b', (mem_relationImage B L e b').2 ⟨hbL, b, hb, relb⟩,
      monotone b x b' y below relb rel⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem copyPullback_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L e F : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (he : e ∈ M.sets) (hF : F ∈ M.sets) : copyPullback A L e F ∈ M.sets :=
  M.relationImage_mem separation hF hA
    (M.relationConverse_mem pairing unions powers separation hA hL he)

theorem internalCountableBelow_copy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F target : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F) target) :
    M.InternalCountableBelow targetOrder F (relationImage target L e) := by
  obtain ⟨B, hB, small, coinitial⟩ := basis
  have subset : B ⊆ A := fun x hx => ((mem_copyPullback A L e F x).1 (coinitial.1 hx)).1
  exact ⟨relationImage B L e, M.relationImage_mem separation hB hL he,
    M.groundEmbeddable_image pairing unions powers separation hB hL
      (M.omega_mem separation infinite) he code subset small,
    coinitial.copy code.function monotone⟩

theorem internalCountableBelow_copy_pullback
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F)
      (copyPullback A L e F)) :
    M.InternalCountableBelow targetOrder F (F ∩ relationImage A L e) := by
  rw [← relationImage_copyPullback code.function F]
  exact M.internalCountableBelow_copy pairing unions powers separation infinite hL he code monotone basis

end TransitiveGround






def FiberCoveredCode (order target parts i B : ZFSet.{u}) : Prop :=
  ∀ x ∈ target, ZFSet.pair i x ∈ parts → ∃ b ∈ B, ZFSet.pair b x ∈ order

noncomputable def basisChoiceRelation (I W order target parts : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ B ∈ W, z = ZFSet.pair i B ∧
    FiberCoveredCode order target parts i B) (ZFSet.prod I W)

theorem pair_mem_basisChoiceRelation (I W order target parts i B : ZFSet.{u}) :
    ZFSet.pair i B ∈ basisChoiceRelation I W order target parts ↔
      i ∈ I ∧ B ∈ W ∧ FiberCoveredCode order target parts i B := by
  rw [basisChoiceRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, A, hA, eq, covers⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, hA, covers⟩
  · rintro ⟨hi, hB, covers⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hB⟩, i, hi, B, hB, rfl, covers⟩

namespace BoundedFormula

open SetFormula

def fiberCoveredFormula {n} (order target parts i B : Fin n) : BoundedFormula n :=
  .allMem target (imp (pairMembershipFormula i.succ 0 parts.succ)
    (exMem B.succ (pairMembershipFormula 0 1 order.succ.succ)))

theorem truth_fiberCoveredFormula {n} (order target parts i B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fiberCoveredFormula order target parts i B) env ↔
      FiberCoveredCode (env order) (env target) (env parts) (env i) (env B) := by
  simp only [fiberCoveredFormula, Truth, truth_imp, truth_exMem, truth_pairMembershipFormula]
  rfl

def basisChoiceEntryFormula {n} (z I W order target parts : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (fiberCoveredFormula order.succ.succ target.succ.succ parts.succ.succ 1 0)))

theorem truth_basisChoiceEntryFormula {n} (z I W order target parts : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (basisChoiceEntryFormula z I W order target parts) env ↔
      ∃ i ∈ env I, ∃ B ∈ env W, env z = ZFSet.pair i B ∧
        FiberCoveredCode (env order) (env target) (env parts) i B := by
  simp only [basisChoiceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fiberCoveredFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem basisChoiceRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W order target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hW : W ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets) :
    basisChoiceRelation I W order target parts ∈ M.sets := by
  let params := extend I (extend W (extend order (extend target (extend parts Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hOrder (Fin.cases hTarget (Fin.cases hParts
      (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod I W) =
      basisChoiceRelation I W order target parts := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, basisChoiceRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_basisChoiceEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem internalCountableBelow_indexed_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I order F target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hOrder : order ∈ M.sets)
    (hF : F ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets)
    (smallI : M.groundEmbeddable I ZFSet.omega)
    (cover : ∀ x ∈ target, ∃ i ∈ I, ZFSet.pair i x ∈ parts)
    (localBases : ∀ i ∈ I, M.InternalCountableBelow order F (relationFiber target parts i)) :
    M.InternalCountableBelow order F target := by
  have hO := M.omega_mem separation infinite
  let W := M.groundSmallSubsets F ZFSet.omega
  have hW : W ∈ M.sets := M.groundSmallSubsets_mem powers separation hF hO
  have choices := M.basisChoiceRelation_mem pairing unions powers separation hI hW hOrder hTarget hParts
  have total (i : ZFSet.{u}) (hi : i ∈ I) :
      ∃ B ∈ W, ZFSet.pair i B ∈ basisChoiceRelation I W order target parts := by
    obtain ⟨B, hB, smallB, positive, below⟩ := localBases i hi
    have hBW : B ∈ W := (M.mem_groundSmallSubsets F ZFSet.omega B).2 ⟨hB, positive, smallB⟩
    exact ⟨B, hBW, (pair_mem_basisChoiceRelation I W order target parts i B).2
      ⟨hi, hBW, fun x hx rel => below x ((mem_relationFiber target parts i x).2 ⟨hx, rel⟩)⟩⟩
  obtain ⟨g, hg, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hW choices total
  let family := relationImage I W g
  have hFamily : family ∈ M.sets := M.relationImage_mem separation hI hW hg
  have smallFamily : M.groundEmbeddable family ZFSet.omega :=
    M.groundEmbeddable_function_image pairing unions powers separation choice hI hW hO hg func smallI
  have candidates (B : ZFSet.{u}) (hB : B ∈ family) : B ∈ W :=
    ((mem_relationImage I W g B).1 hB).1
  have smallBasis (B : ZFSet.{u}) (hB : B ∈ family) : M.groundEmbeddable B ZFSet.omega :=
    ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.2
  refine ⟨family.sUnion, M.union_mem unions hFamily,
    M.groundCountable_family_union pairing unions powers separation infinite choice
      hFamily smallFamily smallBasis, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hB, xB⟩ := ZFSet.mem_sUnion.1 hx
    exact ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.1 xB
  · intro x hx
    obtain ⟨i, hi, ix⟩ := cover x hx
    obtain ⟨B, chosen, _⟩ := func.2 i hi
    have spec := (pair_mem_basisChoiceRelation I W order target parts i B).1 (selected chosen)
    obtain ⟨b, hb, lower⟩ := spec.2.2 x hx ix
    have hB : B ∈ family := (mem_relationImage I W g B).2 ⟨spec.2.1, i, hi, chosen⟩
    exact ⟨b, ZFSet.mem_sUnion.2 ⟨B, hB, hb⟩, lower⟩

end TransitiveGround

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem InternalCountableBelow.mono {order F target smaller : ZFSet.{u}}
    (basis : M.InternalCountableBelow order F target) (subset : smaller ⊆ target) :
    M.InternalCountableBelow order F smaller := by
  obtain ⟨B, hB, small, positive, below⟩ := basis
  exact ⟨B, hB, small, positive, fun x hx => below x (subset hx)⟩

theorem internalCountableBelow_empty (inhabited : M.sets.Nonempty) (order F : ZFSet.{u}) :
    M.InternalCountableBelow order F ∅ := by
  exact ⟨∅, M.empty_mem inhabited, M.empty_groundEmbeddable ZFSet.omega inhabited,
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx),
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx)⟩

theorem internalCountableBelow_of_countable {order F target : ZFSet.{u}}
    (hTarget : target ∈ M.sets) (small : M.groundEmbeddable target ZFSet.omega)
    (positive : target ⊆ F) (refl : ∀ x ∈ target, ZFSet.pair x x ∈ order) :
    M.InternalCountableBelow order F target :=
  ⟨target, hTarget, small, positive, fun x hx => ⟨x, hx, refl x hx⟩⟩

theorem internalCountableBelow_binary_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {order F target₁ target₂ : ZFSet.{u}}
    (first : M.InternalCountableBelow order F target₁)
    (second : M.InternalCountableBelow order F target₂) :
    M.InternalCountableBelow order F (target₁ ∪ target₂) := by
  obtain ⟨B, hB, smallB, positiveB, belowB⟩ := first
  obtain ⟨C, hC, smallC, positiveC, belowC⟩ := second
  refine ⟨B ∪ C, M.binary_union_mem pairing unions hB hC,
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      hB hC smallB smallC, ?_, ?_⟩
  · intro x hx
    exact (ZFSet.mem_union.1 hx).elim (fun hx => positiveB hx) (fun hx => positiveC hx)
  · intro x hx
    rcases ZFSet.mem_union.1 hx with hx | hx
    · obtain ⟨b, hb, lower⟩ := belowB x hx
      exact ⟨b, ZFSet.mem_union.2 (Or.inl hb), lower⟩
    · obtain ⟨c, hc, lower⟩ := belowC x hx
      exact ⟨c, ZFSet.mem_union.2 (Or.inr hc), lower⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
