import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCodedBinaryHeights

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

noncomputable def rectangleLabelCarrier (P : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (natSetCode 3) P

def rectangleOverlapRel (r C B e1 e2 i j x y : ZFSet.{u}) : Prop :=
  (i = j ∧ x = y) ∨
  (i = natSetCode 1 ∧ j = natSetCode 0 ∧ ZFSet.pair x C ∈ r ∧ ZFSet.pair x y ∈ e1) ∨
  (i = natSetCode 0 ∧ j = natSetCode 1 ∧ ZFSet.pair y C ∈ r ∧ ZFSet.pair y x ∈ e1) ∨
  (i = natSetCode 2 ∧ j = natSetCode 0 ∧ ZFSet.pair x C ∈ r ∧ ZFSet.pair x y ∈ e2) ∨
  (i = natSetCode 0 ∧ j = natSetCode 2 ∧ ZFSet.pair y C ∈ r ∧ ZFSet.pair y x ∈ e2) ∨
  ((i = natSetCode 1 ∧ j = natSetCode 2 ∨ i = natSetCode 2 ∧ j = natSetCode 1) ∧
    ZFSet.pair x B ∈ r ∧ x = y)

noncomputable def rectangleOverlapGraph (P r C B e1 e2 : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ natSetCode 3, ∃ j ∈ natSetCode 3, ∃ x ∈ P, ∃ y ∈ P,
    z = ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∧ rectangleOverlapRel r C B e1 e2 i j x y)
    (ZFSet.prod (rectangleLabelCarrier P) (rectangleLabelCarrier P))

theorem mem_rectangleOverlapGraph (P r C B e1 e2 z : ZFSet.{u}) :
    z ∈ rectangleOverlapGraph P r C B e1 e2 ↔
      ∃ i ∈ natSetCode 3, ∃ j ∈ natSetCode 3, ∃ x ∈ P, ∃ y ∈ P,
        z = ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∧ rectangleOverlapRel r C B e1 e2 i j x y := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨i, hi, j, hj, x, hx, y, hy, rfl, rel⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, ZFSet.pair_mem_prod.2 ⟨hj, hy⟩⟩,
      i, hi, j, hj, x, hx, y, hy, rfl, rel⟩

theorem pair_mem_rectangleOverlapGraph (P r C B e1 e2 i j x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∈ rectangleOverlapGraph P r C B e1 e2 ↔
      i ∈ natSetCode 3 ∧ j ∈ natSetCode 3 ∧ x ∈ P ∧ y ∈ P ∧ rectangleOverlapRel r C B e1 e2 i j x y := by
  rw [mem_rectangleOverlapGraph]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, eq, rel⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨ha, hb, hc, hd, rel⟩
  · rintro ⟨hi, hj, hx, hy, rel⟩
    exact ⟨i, hi, j, hj, x, hx, y, hy, rfl, rel⟩

theorem rectangleOverlapGraph_subset (P r C B e1 e2 : ZFSet.{u}) :
    rectangleOverlapGraph P r C B e1 e2 ⊆
      ZFSet.prod (rectangleLabelCarrier P) (rectangleLabelCarrier P) :=
  fun _ h => (ZFSet.mem_sep.1 h).1

namespace BoundedFormula

def localRectangleOverlapFormula {n} (r C B e1 e2 i j x y zero one two : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i j) (.equal x y))
    (disj (.conj (.equal i one) (.conj (.equal j zero)
      (.conj (pairMembershipFormula x C r) (pairMembershipFormula x y e1))))
    (disj (.conj (.equal i zero) (.conj (.equal j one)
      (.conj (pairMembershipFormula y C r) (pairMembershipFormula y x e1))))
    (disj (.conj (.equal i two) (.conj (.equal j zero)
      (.conj (pairMembershipFormula x C r) (pairMembershipFormula x y e2))))
    (disj (.conj (.equal i zero) (.conj (.equal j two)
      (.conj (pairMembershipFormula y C r) (pairMembershipFormula y x e2))))
    (.conj (disj (.conj (.equal i one) (.equal j two)) (.conj (.equal i two) (.equal j one)))
      (.conj (pairMembershipFormula x B r) (.equal x y)))))))

theorem truth_localRectangleOverlapFormula {n} (r C B e1 e2 i j x y zero one two : Fin n)
    (env : Fin n → ZFSet.{u}) (h0 : env zero = natSetCode 0)
    (h1 : env one = natSetCode 1) (h2 : env two = natSetCode 2) :
    Truth (localRectangleOverlapFormula r C B e1 e2 i j x y zero one two) env ↔
      rectangleOverlapRel (env r) (env C) (env B) (env e1) (env e2) (env i) (env j) (env x) (env y) := by
  simp only [localRectangleOverlapFormula, truth_disj, Truth, truth_pairMembershipFormula, h0, h1, h2]
  rfl

def rectangleOverlapEntryFormula {n} (z P r C B e1 e2 zero one two three : Fin n) : BoundedFormula n :=
  exMem three (exMem three.succ (exMem P.succ.succ (exMem P.succ.succ.succ
    (.conj (pairOfPairsFormula z.succ.succ.succ.succ 3 1 2 0)
      (localRectangleOverlapFormula r.succ.succ.succ.succ C.succ.succ.succ.succ B.succ.succ.succ.succ
        e1.succ.succ.succ.succ e2.succ.succ.succ.succ 3 2 1 0
        zero.succ.succ.succ.succ one.succ.succ.succ.succ two.succ.succ.succ.succ)))))

theorem truth_rectangleOverlapEntryFormula {n} (z P r C B e1 e2 zero one two three : Fin n)
    (env : Fin n → ZFSet.{u}) (h0 : env zero = natSetCode 0)
    (h1 : env one = natSetCode 1) (h2 : env two = natSetCode 2) (h3 : env three = natSetCode 3) :
    Truth (rectangleOverlapEntryFormula z P r C B e1 e2 zero one two three) env ↔
      env z ∈ rectangleOverlapGraph (env P) (env r) (env C) (env B) (env e1) (env e2) := by
  simp only [rectangleOverlapEntryFormula, truth_exMem, Truth, truth_pairOfPairsFormula,
    mem_rectangleOverlapGraph, extend, Fin.cases_succ, Fin.cases_zero, h3]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_localRectangleOverlapFormula _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2)
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rectangleOverlapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r C B e1 e2 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets)
    (hE1 : e1 ∈ M.sets) (hE2 : e2 ∈ M.sets) :
    rectangleLabelCarrier P ∈ M.sets ∧ rectangleOverlapGraph P r C B e1 e2 ∈ M.sets := by
  have h0 : natSetCode 0 ∈ M.sets := M.empty_mem ⟨P, hP⟩
  have h1 : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions h0 h0
  have h2 : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions h1 h1
  have h3 : natSetCode 3 ∈ M.sets := M.insert_mem pairing unions h2 h2
  have hL := M.prod_mem pairing unions powers separation h3 hP
  refine ⟨hL, ?_⟩
  let params := extend P (extend r (extend C (extend B (extend e1 (extend e2
    (extend (natSetCode 0) (extend (natSetCode 1) (extend (natSetCode 2) (extend (natSetCode 3) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rectangleOverlapEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hP (Fin.cases hr (Fin.cases hC (Fin.cases hB (Fin.cases hE1 (Fin.cases hE2
      (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun i => Fin.elim0 i)))))))))))
    (M.prod_mem pairing unions powers separation hL hL)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rectangleOverlapEntryFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod (rectangleLabelCarrier P) (rectangleLabelCarrier P)) =
      rectangleOverlapGraph P r C B e1 e2 := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_rectangleOverlapEntryFormula _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl]
    exact ⟨And.right, fun h => ⟨rectangleOverlapGraph_subset _ _ _ _ _ _ h, h⟩⟩
  exact eq ▸ selected
end TransitiveGround

end

section
open SetRealization Compression.RecursiveMaps
universe u

def rectangleVertexCode : Rectangle.Vertex → ZFSet.{u}
  | .root => natSetCode 0
  | .one => natSetCode 1
  | .two => natSetCode 2

theorem rectangleVertexCode_injective : Function.Injective (rectangleVertexCode : Rectangle.Vertex → ZFSet.{u}) := by
  intro i j equal
  cases i <;> cases j <;> simp_all [rectangleVertexCode, natSetCode_injective.eq_iff]

theorem rectangleVertexCode_mem (i : Rectangle.Vertex) : rectangleVertexCode i ∈ (natSetCode 3 : ZFSet.{u}) := by
  cases i <;> exact (natSetCode_mem_iff _ _).2 (by decide)

theorem mem_three_iff_rectangleVertexCode (x : ZFSet.{u}) :
    x ∈ natSetCode 3 ↔ ∃ i, rectangleVertexCode i = x := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode x 3).1 hx
    have values : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases values with rfl | rfl | rfl
    · exact ⟨.root, rfl⟩
    · exact ⟨.one, rfl⟩
    · exact ⟨.two, rfl⟩
  · rintro ⟨i, rfl⟩
    exact rectangleVertexCode_mem i

noncomputable def rectangleLabelPresentation {A : Type u} (s : Presentation A) :
    Presentation (Rectangle.Vertex × A) where
  carrier := rectangleLabelCarrier s.carrier
  encode ix := ZFSet.pair (rectangleVertexCode ix.1) (s.encode ix.2)
  injective := by
    intro x y equal
    have parts := ZFSet.pair_inj.1 equal
    exact Prod.ext (rectangleVertexCode_injective parts.1) (s.injective parts.2)
  mem_carrier z := by
    rw [rectangleLabelCarrier, ZFSet.mem_prod]
    constructor
    · rintro ⟨i, hi, x, hx, eq⟩
      obtain ⟨i, rfl⟩ := (mem_three_iff_rectangleVertexCode i).1 hi
      obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
      exact ⟨(i, x), eq.symm⟩
    · rintro ⟨⟨i, x⟩, rfl⟩
      exact ⟨_, rectangleVertexCode_mem i, _, s.encode_mem x, rfl⟩

variable {A : Type u} (s : Presentation A) {p : MeetOrder A} (tile : Rectangle.Input p)
variable {r e1 e2 : ZFSet.{u}}
variable (order : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ p.le x y)
variable (first : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e1 ↔ tile.g1.toFun x = y)
variable (second : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e2 ↔ tile.g2.toFun x = y)

include order first second in
theorem rectangleOverlapRel_iff (i j : Rectangle.Vertex) (x y : A) :
    rectangleOverlapRel r (s.encode tile.C) (s.encode tile.B) e1 e2
      (rectangleVertexCode i) (rectangleVertexCode j) (s.encode x) (s.encode y) ↔
      tile.copies.Related (i, x) (j, y) := by
  have reverse1 : (p.le y tile.C ∧ tile.g1.toFun y = x) ↔
      (p.le x (tile.g1.toFun tile.C) ∧ tile.g1.inverse x = y) := by
    constructor
    · rintro ⟨below, rfl⟩
      exact ⟨(tile.g1.le_iff _ _).2 below, tile.g1.left_inverse y⟩
    · rintro ⟨below, eq⟩
      rw [← eq]
      exact ⟨tile.inverse1_C x below, tile.g1.right_inverse x⟩
  have reverse2 : (p.le y tile.C ∧ tile.g2.toFun y = x) ↔
      (p.le x (tile.g2.toFun tile.C) ∧ tile.g2.inverse x = y) := by
    constructor
    · rintro ⟨below, rfl⟩
      exact ⟨(tile.g2.le_iff _ _).2 below, tile.g2.left_inverse y⟩
    · rintro ⟨below, eq⟩
      rw [← eq]
      exact ⟨tile.inverse2_C x below, tile.g2.right_inverse x⟩
  cases i <;> cases j <;>
    simp [rectangleOverlapRel, rectangleVertexCode, natSetCode_injective.eq_iff,
      s.injective.eq_iff, order, first, second, CompatibleCopies.Data.Related,
      Rectangle.Input.copies, Rectangle.Input.anchor, Rectangle.Input.transition,
      inverseIso, identityIso, isoOfOrder, tile.greatest]
  · exact reverse1
  · exact reverse2

include order first second in
theorem rectangleOverlapGraph_iff (x y : Rectangle.Vertex × A) :
    ZFSet.pair ((rectangleLabelPresentation s).encode x) ((rectangleLabelPresentation s).encode y) ∈
      rectangleOverlapGraph s.carrier r (s.encode tile.C) (s.encode tile.B) e1 e2 ↔
      tile.copies.Related x y := by
  change ZFSet.pair (ZFSet.pair (rectangleVertexCode x.1) (s.encode x.2))
    (ZFSet.pair (rectangleVertexCode y.1) (s.encode y.2)) ∈ _ ↔ _
  rw [pair_mem_rectangleOverlapGraph]
  simp only [rectangleVertexCode_mem, s.encode_mem, true_and]
  exact rectangleOverlapRel_iff s tile order first second x.1 y.1 x.2 y.2

include order first second in
theorem rectangleOverlap_equivalence :
    EquivalenceRelationCode (rectangleLabelCarrier s.carrier)
      (rectangleOverlapGraph s.carrier r (s.encode tile.C) (s.encode tile.B) e1 e2) := by
  let labels := rectangleLabelPresentation s
  have entries := rectangleOverlapGraph_iff s tile order first second
  refine ⟨rectangleOverlapGraph_subset _ _ _ _ _ _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (labels.mem_carrier x).1 hx
    exact (entries a a).2 (tile.copies.related_refl a)
  · intro x y entry
    have bounds := ZFSet.pair_mem_prod.1 (rectangleOverlapGraph_subset _ _ _ _ _ _ entry)
    obtain ⟨a, rfl⟩ := (labels.mem_carrier x).1 bounds.1
    obtain ⟨b, rfl⟩ := (labels.mem_carrier y).1 bounds.2
    exact (entries b a).2 (tile.copies.related_symm ((entries a b).1 entry))
  · intro x y z xy yz
    have bounds := ZFSet.pair_mem_prod.1 (rectangleOverlapGraph_subset _ _ _ _ _ _ xy)
    have boundZ := (ZFSet.pair_mem_prod.1 (rectangleOverlapGraph_subset _ _ _ _ _ _ yz)).2
    obtain ⟨a, rfl⟩ := (labels.mem_carrier x).1 bounds.1
    obtain ⟨b, rfl⟩ := (labels.mem_carrier y).1 bounds.2
    obtain ⟨c, rfl⟩ := (labels.mem_carrier z).1 boundZ
    exact (entries a c).2 (tile.copies.related_trans ((entries a b).1 xy) ((entries b c).1 yz))

noncomputable def rectangleTilePresentation : Presentation tile.copies.Node :=
  (rectangleLabelPresentation s).quotientPresentation tile.copies.setoid
    (rectangleOverlap_equivalence s tile order first second)
    (rectangleOverlapGraph_iff s tile order first second)

end

section
open SetRealization Compression.RecursiveMaps
universe u

noncomputable def rectangleQuotientOrder (P Q r classifier : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ Q, ∃ y ∈ Q, z = ZFSet.pair x y ∧
    ∃ i ∈ natSetCode 3, ∃ a ∈ P, ∃ b ∈ P,
      ZFSet.pair (ZFSet.pair i a) x ∈ classifier ∧
      ZFSet.pair (ZFSet.pair i b) y ∈ classifier ∧ ZFSet.pair a b ∈ r)
    (ZFSet.prod Q Q)

theorem mem_rectangleQuotientOrder (P Q r classifier z : ZFSet.{u}) :
    z ∈ rectangleQuotientOrder P Q r classifier ↔
      ∃ x ∈ Q, ∃ y ∈ Q, z = ZFSet.pair x y ∧
      ∃ i ∈ natSetCode 3, ∃ a ∈ P, ∃ b ∈ P,
        ZFSet.pair (ZFSet.pair i a) x ∈ classifier ∧
        ZFSet.pair (ZFSet.pair i b) y ∈ classifier ∧ ZFSet.pair a b ∈ r := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · intro h
    obtain ⟨x, hx, y, hy, eq, rest⟩ := h
    subst z
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, rest⟩

theorem pair_mem_rectangleQuotientOrder (P Q r classifier x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ rectangleQuotientOrder P Q r classifier ↔
      x ∈ Q ∧ y ∈ Q ∧ ∃ i ∈ natSetCode 3, ∃ a ∈ P, ∃ b ∈ P,
        ZFSet.pair (ZFSet.pair i a) x ∈ classifier ∧
        ZFSet.pair (ZFSet.pair i b) y ∈ classifier ∧ ZFSet.pair a b ∈ r := by
  rw [mem_rectangleQuotientOrder]
  constructor
  · rintro ⟨a, ha, b, hb, eq, rest⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, rest⟩
  · rintro ⟨hx, hy, rest⟩
    exact ⟨x, hx, y, hy, rfl, rest⟩

theorem rectangleQuotientOrder_subset (P Q r classifier : ZFSet.{u}) :
    rectangleQuotientOrder P Q r classifier ⊆ ZFSet.prod Q Q :=
  fun _ h => (ZFSet.mem_sep.1 h).1

variable {A : Type u} (s : Presentation A) {p : MeetOrder A} (tile : Rectangle.Input p)
variable {r e1 e2 : ZFSet.{u}}
variable (order : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ p.le x y)
variable (first : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e1 ↔ tile.g1.toFun x = y)
variable (second : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e2 ↔ tile.g2.toFun x = y)

noncomputable abbrev rectangleTileOrder :=
  rectangleQuotientOrder s.carrier (rectangleTilePresentation s tile order first second).carrier r
    (equivalenceClassifier (rectangleLabelCarrier s.carrier)
      (rectangleOverlapGraph s.carrier r (s.encode tile.C) (s.encode tile.B) e1 e2))

include order first second

theorem rectangleTileOrder_iff (x y : tile.copies.Node) :
    ZFSet.pair ((rectangleTilePresentation s tile order first second).encode x)
      ((rectangleTilePresentation s tile order first second).encode y) ∈
      rectangleTileOrder s tile order first second ↔ tile.copies.order.le x y := by
  have classifier := (rectangleLabelPresentation s).quotientPresentation_classifier_entry_iff
    tile.copies.setoid (rectangleOverlap_equivalence s tile order first second)
    (rectangleOverlapGraph_iff s tile order first second)
  rw [rectangleTileOrder, pair_mem_rectangleQuotientOrder]
  simp only [(rectangleTilePresentation s tile order first second).encode_mem, true_and]
  constructor
  · rintro ⟨i, hi, a, ha, b, hb, ax, byEntry, ab⟩
    obtain ⟨i, rfl⟩ := (mem_three_iff_rectangleVertexCode i).1 hi
    obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (s.mem_carrier b).1 hb
    have ex : tile.copies.point i a = x := (classifier (i, a) x).1 ax
    have ey : tile.copies.point i b = y := (classifier (i, b) y).1 byEntry
    rw [← ex, ← ey]
    exact (tile.copies.vertex_le i a b).2 ((order a b).1 ab)
  · intro lower
    obtain ⟨i, a, b, ex, ey, ab⟩ := tile.copies.comparison_in_vertex x y lower
    exact ⟨rectangleVertexCode i, rectangleVertexCode_mem i, s.encode a, s.encode_mem a,
      s.encode b, s.encode_mem b, (classifier (i, a) x).2 ex,
      (classifier (i, b) y).2 ey, (order a b).2 ab⟩

theorem rectangleTile_partialOrder : PartialOrderCode
    (rectangleTilePresentation s tile order first second).carrier
    (rectangleTileOrder s tile order first second) := by
  let q := rectangleTilePresentation s tile order first second
  have entries := rectangleTileOrder_iff s tile order first second
  refine ⟨rectangleQuotientOrder_subset _ _ _ _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (q.mem_carrier x).1 hx
    exact (entries a a).2 (tile.copies.order.refl a)
  · intro x hx y hy xy yx
    obtain ⟨a, rfl⟩ := (q.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (q.mem_carrier y).1 hy
    exact congrArg q.encode (tile.copies.order.antisymm ((entries a b).1 xy) ((entries b a).1 yx))
  · intro x hx y hy z hz xy yz
    obtain ⟨a, rfl⟩ := (q.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (q.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (q.mem_carrier z).1 hz
    exact (entries a c).2 (tile.copies.order.trans ((entries a b).1 xy) ((entries b c).1 yz))

theorem rectangleTile_meet_glb (x y : tile.copies.Node) :
    GreatestLowerBoundCode (rectangleTilePresentation s tile order first second).carrier
      (rectangleTileOrder s tile order first second)
      ((rectangleTilePresentation s tile order first second).encode x)
      ((rectangleTilePresentation s tile order first second).encode y)
      ((rectangleTilePresentation s tile order first second).encode (tile.copies.order.meet x y)) := by
  let q := rectangleTilePresentation s tile order first second
  have entries := rectangleTileOrder_iff s tile order first second
  refine ⟨(entries _ _).2 (tile.copies.order.meet_le_left x y),
    (entries _ _).2 (tile.copies.order.meet_le_right x y), ?_⟩
  intro z hz zx zy
  obtain ⟨a, rfl⟩ := (q.mem_carrier z).1 hz
  exact (entries _ _).2 (tile.copies.order.le_meet ((entries _ _).1 zx) ((entries _ _).1 zy))

theorem rectangleTile_meetOrder : MeetOrderCode
    (rectangleTilePresentation s tile order first second).carrier
    (rectangleTileOrder s tile order first second)
    (canonicalMeetGraph (rectangleTilePresentation s tile order first second).carrier
      (rectangleTileOrder s tile order first second)) := by
  apply canonicalMeetGraph_code (rectangleTile_partialOrder s tile order first second)
  intro x hx y hy
  let q := rectangleTilePresentation s tile order first second
  obtain ⟨a, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨b, rfl⟩ := (q.mem_carrier y).1 hy
  exact ⟨q.encode (tile.copies.order.meet a b), q.encode_mem _,
    rectangleTile_meet_glb s tile order first second a b⟩

theorem rectangleTile_meet_entry (x y : tile.copies.Node) :
    ZFSet.pair (ZFSet.pair ((rectangleTilePresentation s tile order first second).encode x)
      ((rectangleTilePresentation s tile order first second).encode y))
      ((rectangleTilePresentation s tile order first second).encode (tile.copies.order.meet x y)) ∈
    canonicalMeetGraph (rectangleTilePresentation s tile order first second).carrier
      (rectangleTileOrder s tile order first second) := by
  apply (pair_mem_canonicalMeetGraph _ _ _ _ _).2
  refine ⟨?_, ?_, ?_, rectangleTile_meet_glb s tile order first second x y⟩ <;>
    exact (rectangleTilePresentation s tile order first second).encode_mem _

end

section
open SetFormula SetRealization Compression.RecursiveMaps
universe u

namespace BoundedFormula

def rectangleQuotientOrderFormula {n} (z P Q r classifier three : Fin n) : BoundedFormula n :=
  exMem Q (exMem Q.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (exMem three.succ.succ (exMem P.succ.succ.succ (exMem P.succ.succ.succ.succ
        (.conj (tripleMembershipFormula 2 1 4 classifier.succ.succ.succ.succ.succ)
          (.conj (tripleMembershipFormula 2 0 3 classifier.succ.succ.succ.succ.succ)
            (pairMembershipFormula 1 0 r.succ.succ.succ.succ.succ))))))))

theorem truth_rectangleQuotientOrderFormula {n} (z P Q r classifier three : Fin n)
    (env : Fin n → ZFSet.{u}) (hthree : env three = natSetCode 3) :
    Truth (rectangleQuotientOrderFormula z P Q r classifier three) env ↔
      env z ∈ rectangleQuotientOrder (env P) (env Q) (env r) (env classifier) := by
  simp only [rectangleQuotientOrderFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, mem_rectangleQuotientOrder,
    extend, Fin.cases_zero, Fin.cases_succ]
  rw [hthree]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem rectangleQuotientOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P Q r classifier : ZFSet.{u}} (hP : P ∈ M.sets) (hQ : Q ∈ M.sets)
    (hr : r ∈ M.sets) (hc : classifier ∈ M.sets) :
    rectangleQuotientOrder P Q r classifier ∈ M.sets := by
  have hzero := M.empty_mem ⟨P, hP⟩
  have hone := M.insert_mem pairing unions hzero hzero
  have htwo := M.insert_mem pairing unions hone hone
  have hthree := M.insert_mem pairing unions htwo htwo
  change (natSetCode 3 : ZFSet.{u}) ∈ M.sets at hthree
  have bound := M.prod_mem pairing unions powers separation hQ hQ
  let params := extend P (extend Q (extend r (extend classifier (extend (natSetCode 3) Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rectangleQuotientOrderFormula 0 1 2 3 4 5) params
    (Fin.cases hP (Fin.cases hQ (Fin.cases hr (Fin.cases hc
      (Fin.cases hthree (fun i => Fin.elim0 i)))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rectangleQuotientOrderFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod Q Q) = rectangleQuotientOrder P Q r classifier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_rectangleQuotientOrderFormula _ _ _ _ _ _ _ rfl]
    change (z ∈ ZFSet.prod Q Q ∧ z ∈ rectangleQuotientOrder P Q r classifier) ↔ _
    exact ⟨And.right, fun hz => ⟨rectangleQuotientOrder_subset _ _ _ _ hz, hz⟩⟩
  exact eq ▸ selected

theorem rectangleTile_ground (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : Type u} (s : Presentation A) {p : MeetOrder A} (tile : Rectangle.Input p)
    {r e1 e2 : ZFSet.{u}}
    (order : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ p.le x y)
    (first : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e1 ↔ tile.g1.toFun x = y)
    (second : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e2 ↔ tile.g2.toFun x = y)
    (hP : s.carrier ∈ M.sets) (hr : r ∈ M.sets) (he1 : e1 ∈ M.sets) (he2 : e2 ∈ M.sets) :
    (rectangleTilePresentation s tile order first second).carrier ∈ M.sets ∧
    rectangleTileOrder s tile order first second ∈ M.sets ∧
    canonicalMeetGraph (rectangleTilePresentation s tile order first second).carrier
      (rectangleTileOrder s tile order first second) ∈ M.sets := by
  have overlap := M.rectangleOverlapGraph_mem pairing unions powers separation hP hr
    (M.transitive hP (s.encode_mem tile.C)) (M.transitive hP (s.encode_mem tile.B)) he1 he2
  have carrier := M.equivalenceClasses_mem powers separation overlap.1 overlap.2
  have classifier := M.equivalenceClassifier_mem pairing unions powers separation overlap.1 overlap.2
  have rel := M.rectangleQuotientOrder_mem pairing unions powers separation hP carrier hr classifier
  exact ⟨carrier, rel, M.canonicalMeetGraph_mem pairing unions powers separation carrier rel⟩

end TransitiveGround

end

section
open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable {A : Type u} (s : Presentation A) {p : MeetOrder A} (tile : Rectangle.Input p)
variable {r e1 e2 : ZFSet.{u}}
variable (order : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ p.le x y)
variable (first : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e1 ↔ tile.g1.toFun x = y)
variable (second : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ e2 ↔ tile.g2.toFun x = y)

noncomputable def rectangleTileVertexGraph (i : Rectangle.Vertex) :=
  indexedRelationSection s.carrier (rectangleTilePresentation s tile order first second).carrier
    (equivalenceClassifier (rectangleLabelCarrier s.carrier)
      (rectangleOverlapGraph s.carrier r (s.encode tile.C) (s.encode tile.B) e1 e2))
    (rectangleVertexCode i)

include order first second

theorem rectangleTileVertexGraph_iff (i : Rectangle.Vertex) (x : A) (y : tile.copies.Node) :
    ZFSet.pair (s.encode x) ((rectangleTilePresentation s tile order first second).encode y) ∈
      rectangleTileVertexGraph s tile order first second i ↔ tile.copies.point i x = y := by
  rw [rectangleTileVertexGraph, pair_mem_indexedRelationSection]
  simp only [s.encode_mem, (rectangleTilePresentation s tile order first second).encode_mem, true_and]
  exact (rectangleLabelPresentation s).quotientPresentation_classifier_entry_iff
    tile.copies.setoid (rectangleOverlap_equivalence s tile order first second)
    (rectangleOverlapGraph_iff s tile order first second) (i, x) y

theorem rectangleTileVertexGraph_eq (i : Rectangle.Vertex) :
    rectangleTileVertexGraph s tile order first second i =
      s.graph (rectangleTilePresentation s tile order first second) (tile.copies.point i) := by
  apply s.relation_ext (rectangleTilePresentation s tile order first second)
    (indexedRelationSection_subset _ _ _ _) (s.graph_isFunc _ _).1
  intro x y
  change ZFSet.pair (s.encode x) ((rectangleTilePresentation s tile order first second).encode y) ∈
    rectangleTileVertexGraph s tile order first second i ↔ _
  rw [rectangleTileVertexGraph_iff, s.pair_mem_graph]

theorem rectangleTileVertex_injection (i : Rectangle.Vertex) :
    InjectionCode s.carrier (rectangleTilePresentation s tile order first second).carrier
      (rectangleTileVertexGraph s tile order first second i) := by
  rw [rectangleTileVertexGraph_eq]
  exact s.graph_injection _ _ (tile.copies.vertex_injective i)

theorem rectangleTileVertex_order_iff (i : Rectangle.Vertex) {x y x' y' : ZFSet.{u}}
    (hx : ZFSet.pair x x' ∈ rectangleTileVertexGraph s tile order first second i)
    (hy : ZFSet.pair y y' ∈ rectangleTileVertexGraph s tile order first second i) :
    ZFSet.pair x' y' ∈ rectangleTileOrder s tile order first second ↔ ZFSet.pair x y ∈ r := by
  rw [rectangleTileVertexGraph_eq] at hx hy
  obtain ⟨a, ha⟩ := (s.mem_graph _ _ _).1 hx
  obtain ⟨b, hb⟩ := (s.mem_graph _ _ _).1 hy
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ha
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 hb
  exact (rectangleTileOrder_iff s tile order first second _ _).trans
    ((tile.copies.vertex_le i a b).trans (order a b).symm)

theorem rectangleTileVertex_embedding {μ : ZFSet.{u}} (source : MeetOrderCode s.carrier r μ)
    (meet : ∀ x y, ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode (p.meet x y)) ∈ μ)
    (i : Rectangle.Vertex) :
    MeetEmbeddingCode s.carrier (rectangleTilePresentation s tile order first second).carrier
      r (rectangleTileOrder s tile order first second) μ
      (canonicalMeetGraph (rectangleTilePresentation s tile order first second).carrier
        (rectangleTileOrder s tile order first second))
      (rectangleTileVertexGraph s tile order first second i) := by
  refine ⟨rectangleTileVertex_injection s tile order first second i, ?_, ?_⟩
  · intro x y x' y' lower hx hy
    exact (rectangleTileVertex_order_iff s tile order first second i hx hy).2 lower
  · intro x y z x' y' z' mxy hx hy hz
    rw [rectangleTileVertexGraph_eq] at hx hy hz
    obtain ⟨a, ha⟩ := (s.mem_graph _ _ _).1 hx
    obtain ⟨b, hb⟩ := (s.mem_graph _ _ _).1 hy
    obtain ⟨c, hc⟩ := (s.mem_graph _ _ _).1 hz
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ha
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 hb
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 hc
    obtain ⟨w, _, unique⟩ := source.operation.2
      (ZFSet.pair (s.encode a) (s.encode b)) (ZFSet.pair_mem_prod.2 ⟨s.encode_mem a, s.encode_mem b⟩)
    have equal : c = p.meet a b := s.injective ((unique _ mxy).trans (unique _ (meet a b)).symm)
    subst c
    have mapped := (tile.copies.vertex i).map_meet a b
    change tile.copies.point i (p.meet a b) = _ at mapped
    rw [mapped]
    exact rectangleTile_meet_entry s tile order first second _ _

theorem rectangleTileVertex_cover (z : ZFSet.{u})
    (hz : z ∈ (rectangleTilePresentation s tile order first second).carrier) :
    ∃ i : Rectangle.Vertex, ∃ x ∈ s.carrier,
      ZFSet.pair x z ∈ rectangleTileVertexGraph s tile order first second i := by
  obtain ⟨a, rfl⟩ := ((rectangleTilePresentation s tile order first second).mem_carrier z).1 hz
  obtain ⟨i, x, hx⟩ := tile.copies.cover a
  exact ⟨i, s.encode x, s.encode_mem x, (rectangleTileVertexGraph_iff s tile order first second i x a).2 hx⟩

theorem rectangleTileVertex_overlap (i j : Rectangle.Vertex) (x y : A) :
    (rectangleTilePresentation s tile order first second).encode (tile.copies.point i x) =
      (rectangleTilePresentation s tile order first second).encode (tile.copies.point j y) ↔
      tile.copies.Related (i, x) (j, y) :=
  (rectangleTilePresentation s tile order first second).injective.eq_iff.trans
    (tile.copies.mk_eq_mk i j x y)

theorem rectangleTileVertex_ideal (i : Rectangle.Vertex) (x : A) {z : ZFSet.{u}}
    (hz : z ∈ (rectangleTilePresentation s tile order first second).carrier)
    (lower : ZFSet.pair z ((rectangleTilePresentation s tile order first second).encode
      (tile.copies.point i x)) ∈ rectangleTileOrder s tile order first second) :
    ∃ y ∈ s.carrier, ZFSet.pair y z ∈ rectangleTileVertexGraph s tile order first second i := by
  obtain ⟨a, rfl⟩ := ((rectangleTilePresentation s tile order first second).mem_carrier z).1 hz
  obtain ⟨y, eq⟩ := tile.copies.vertex_ideal i x a ((rectangleTileOrder_iff s tile order first second _ _).1 lower)
  exact ⟨s.encode y, s.encode_mem y, (rectangleTileVertexGraph_iff s tile order first second i y a).2 eq⟩

theorem TransitiveGround.rectangleTileVertexGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : s.carrier ∈ M.sets) (hr : r ∈ M.sets) (he1 : e1 ∈ M.sets) (he2 : e2 ∈ M.sets)
    (i : Rectangle.Vertex) : rectangleTileVertexGraph s tile order first second i ∈ M.sets := by
  have overlap := M.rectangleOverlapGraph_mem pairing unions powers separation hP hr
    (M.transitive hP (s.encode_mem tile.C)) (M.transitive hP (s.encode_mem tile.B)) he1 he2
  have carrier := M.equivalenceClasses_mem powers separation overlap.1 overlap.2
  have classifier := M.equivalenceClassifier_mem pairing unions powers separation overlap.1 overlap.2
  have hzero := M.empty_mem ⟨s.carrier, hP⟩
  have hone := M.insert_mem pairing unions hzero hzero
  have htwo := M.insert_mem pairing unions hone hone
  have hi : rectangleVertexCode i ∈ M.sets := by
    cases i
    · exact hzero
    · exact hone
    · exact htwo
  exact M.indexedRelationSection_mem pairing unions powers separation hP carrier classifier hi

end

section
open SetRealization Compression.RecursiveMaps SetFormula
universe u

variable {P G r μ A m inv one c b d g h : ZFSet.{u}}

theorem PosetActionCode.section_small_iff (action : PosetActionCode G P m one r A)
    (actor : SetMembers G) (x y : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈
      indexedRelationSection P P A (SetMembers.raw actor) ↔ action.act actor x = y := by
  rw [pair_mem_indexedRelationSection]
  simp only [SetMembers.raw_mem, true_and]
  exact (action.act_eq_iff actor x y).symm

theorem ExternalRectangleCode.exists_ground_tile
    (code : ExternalRectangleCode P G r μ A c b d g h)
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (top : SetMembers P)
    (greatest : ∀ x, meet.toSmallMeetOrder.le x top)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hA : A ∈ M.sets) :
    let tile := (code.toSmallActionRectangle group action meet).toInput top greatest
    ∃ q : Presentation tile.copies.Node, ∃ rel μt : ZFSet.{u}, ∃ vertices : Rectangle.Vertex → ZFSet.{u},
      q.carrier = equivalenceClasses (rectangleLabelCarrier P)
        (rectangleOverlapGraph P r c b (indexedRelationSection P P A g) (indexedRelationSection P P A h)) ∧
      q.carrier ∈ M.sets ∧ rel ∈ M.sets ∧ μt ∈ M.sets ∧
      MeetOrderCode q.carrier rel μt ∧
      (∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ rel ↔ tile.copies.order.le x y) ∧
      (∀ x y, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y))
        (q.encode (tile.copies.order.meet x y)) ∈ μt) ∧
      (∀ i, vertices i ∈ M.sets ∧ MeetEmbeddingCode P q.carrier r rel μ μt (vertices i)) ∧
      (∀ i x y, ZFSet.pair (SetMembers.raw x) (q.encode y) ∈ vertices i ↔ tile.copies.point i x = y) := by
  dsimp only
  let request := code.toSmallActionRectangle group action meet
  let tile := request.toInput top greatest
  let s := SetMembers.presentation P
  have fields := code.toSmallActionRectangle_fields group action meet
  have related : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ meet.toSmallMeetOrder.le x y :=
    fun _ _ => Iff.rfl
  have first : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ indexedRelationSection P P A g ↔
      tile.g1.toFun x = y := by
    intro x y
    have entry := action.section_small_iff request.first x y
    change ZFSet.pair (s.encode x) (s.encode y) ∈ indexedRelationSection P P A
      (SetMembers.raw request.first) ↔ tile.g1.toFun x = y at entry
    rw [show SetMembers.raw request.first = g from fields.2.2.2.1] at entry
    exact entry
  have second : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ indexedRelationSection P P A h ↔
      tile.g2.toFun x = y := by
    intro x y
    have entry := action.section_small_iff request.second x y
    change ZFSet.pair (s.encode x) (s.encode y) ∈ indexedRelationSection P P A
      (SetMembers.raw request.second) ↔ tile.g2.toFun x = y at entry
    rw [show SetMembers.raw request.second = h from fields.2.2.2.2] at entry
    exact entry
  have e1 := M.indexedRelationSection_mem pairing unions powers separation hP hP hA
    (M.transitive hG code.2.2.2.1)
  have e2 := M.indexedRelationSection_mem pairing unions powers separation hP hP hA
    (M.transitive hG code.2.2.2.2.1)
  let q := rectangleTilePresentation s tile related first second
  let rel := rectangleTileOrder s tile related first second
  let μt := canonicalMeetGraph q.carrier rel
  let vertices := rectangleTileVertexGraph s tile related first second
  have ground := M.rectangleTile_ground pairing unions powers separation s tile related first second hP hr e1 e2
  refine ⟨q, rel, μt, vertices, ?_, ground.1, ground.2.1, ground.2.2,
    rectangleTile_meetOrder s tile related first second,
    rectangleTileOrder_iff s tile related first second,
    rectangleTile_meet_entry s tile related first second, ?_, ?_⟩
  · change equivalenceClasses (rectangleLabelCarrier P)
      (rectangleOverlapGraph P r (SetMembers.raw request.C) (SetMembers.raw request.B)
        (indexedRelationSection P P A g) (indexedRelationSection P P A h)) = _
    rw [fields.1, fields.2.1]
  · intro i
    exact ⟨TransitiveGround.rectangleTileVertexGraph_mem s tile related first second M
      pairing unions powers separation hP hr e1 e2 i,
      rectangleTileVertex_embedding s tile related first second meet meet.smallMeet_entry i⟩
  · exact rectangleTileVertexGraph_iff s tile related first second

end

open SetRealization Compression.RecursiveMaps SetFormula
universe u
variable {P G r μ A m inv one C B E g k H rH old D rD c lo hi : ZFSet.{u}}

theorem ExternalRectangleCode.exists_ground_height
    (request : ExternalRectangleCode P G r μ A C B E g k)
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (top : SetMembers P)
    (greatest : ∀ x, meet.toSmallMeetOrder.le x top)
    (height : StrictHeightGraphCode P H r rH old) (linear : StrictLinearOrderCode H rH)
    (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hA : A ∈ M.sets)
    (hH : H ∈ M.sets) (hOld : old ∈ M.sets) (hrH : rH ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (small : M.groundEmbeddable (relationImage P H old) ZFSet.omega)
    (hlo : lo ∈ D) (hhi : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    let tile := (request.toSmallActionRectangle group action meet).toInput top greatest
    ∃ q : Presentation tile.copies.Node, ∃ rel ν h : ZFSet.{u},
      q.carrier = equivalenceClasses (rectangleLabelCarrier P)
        (rectangleOverlapGraph P r C B (indexedRelationSection P P A g) (indexedRelationSection P P A k)) ∧
      q.carrier ∈ M.sets ∧ rel ∈ M.sets ∧ ν ∈ M.sets ∧
      MeetOrderCode q.carrier rel ν ∧
      (∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ rel ↔ tile.copies.order.le x y) ∧
      h ∈ M.sets ∧ IntervalHeightCode q.carrier rel D rD lo hi h ∧
      relationImage q.carrier D h ∈ M.sets ∧
      M.groundEmbeddable (relationImage q.carrier D h) ZFSet.omega := by
  dsimp only
  let rectangle := (request.toSmallActionRectangle group action meet).toInput top greatest
  obtain ⟨q, rel, ν, vertices, carrier, hL, hRel, hν, tileMeet, related, meetEntries, vertexCodes, entries⟩ :=
    request.exists_ground_tile M pairing unions powers separation group action meet top greatest hP hG hr hA
  let tile := TileRequests.Tile.rectangle rectangle
  let s := SetMembers.presentation P
  have vertexGround (i : Rectangle.Vertex) : s.graph q (rectangle.copies.point i) ∈ M.sets := by
    have function := (vertexCodes i).2.injection.function
    have equal : s.decodeFunction q (vertices i) function = rectangle.copies.point i := by
      funext x
      apply (s.decodeFunction_iff q (vertices i) function x _).2
      exact (entries i x _).2 rfl
    rw [← equal, s.graph_decodeFunction q (vertices i) function]
    exact (vertexCodes i).1
  have seedGround : s.graph (SetMembers.presentation H) (height.smallHeight meet linear).value ∈ M.sets := by
    rw [height.smallHeight_graph]
    exact hOld
  have seedSmall : M.groundEmbeddable (relationImage P H
      (s.graph (SetMembers.presentation H) (height.smallHeight meet linear).value)) ZFSet.omega := by
    rw [height.smallHeight_graph]
    exact small
  obtain ⟨h, hground, code, rangeGround, rangeSmall⟩ :=
    M.exists_rectangleTileIntervalHeight pairing unions powers separation collection infinite
      s (SetMembers.presentation H) top greatest linear.smallOrder (height.smallHeight meet linear)
      (fun _ _ => Iff.rfl) linear target injection hP hH seedGround hrH hD hrD hc seedSmall hlo hhi gap
      tile q hL hν related tileMeet.operation meetEntries
      (vertexGround .root) (vertexGround .one) (vertexGround .two)
  exact ⟨q, rel, ν, h, carrier, hL, hRel, hν, tileMeet, related, hground, code, rangeGround, rangeSmall⟩

end PartitionPilot.Forcing

end OAI
