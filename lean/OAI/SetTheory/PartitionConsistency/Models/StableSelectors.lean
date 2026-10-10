import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.GermSelectors

namespace OAI

/-! ## ConditionSelector -/

/-! The countable-germ selector as a genuine condition-by-condition recipe.
There is no total family of generic rows in the ambient universe in this
construction.  A countable condition suffices to decide each selection, and
the decisions are both persistent and covariant. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

/-- A convenient total extension of a partial condition. This is auxiliary
row data, NOT the generic rows; only values in the domain will be used to
make a persistent decision. -/
def rows (p : Condition I κ) (i : I) (a : κ) : Bool :=
  if ((i,a),true) ∈ p.graph then true else false

theorem rows_of_mem (p : Condition I κ) (i : I) (a : κ) (b : Bool)
    (h : ((i,a),b) ∈ p.graph) : p.rows i a = b := by
  cases b
  · have hn : ((i,a),true) ∉ p.graph := fun ht => Bool.false_ne_true (p.functional _ _ _ h ht)
    simp [rows,hn]
  · simp [rows,h]

theorem rows_eq_of_le {p q : Condition I κ} (hqp : q ≤ p) {i : I} {a : κ}
    (ha : (i,a) ∈ p.dom) : q.rows i a = p.rows i a := by
  obtain ⟨b,hb⟩ := (p.mem_dom _).mp ha
  exact (q.rows_of_mem i a b (hqp hb)).trans (p.rows_of_mem i a b hb).symm

@[simp] theorem rows_permute (σ : Equiv.Perm I) (p : Condition I κ) (i : I) (a : κ) :
    (p.permute σ).rows i a = p.rows (σ.symm i) a := by
  simp only [rows,mem_permute]

theorem dom_mono {p q : Condition I κ} (hqp : q ≤ p) : p.dom ⊆ q.dom := by
  intro a ha
  obtain ⟨b,hb⟩ := (p.mem_dom _).mp ha
  exact (q.mem_dom _).mpr ⟨b,hqp hb⟩

/-- Fill only the as-yet-undefined places in a prescribed countable set. -/
def fill (p : Condition I κ) (A : Set (I × κ)) (hA : A.Countable) : Condition I κ where
  graph := p.graph ∪ {z | z.1 ∈ A ∧ z.1 ∉ p.dom ∧ z.2 = false}
  functional := by
    intro a b c hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · exact p.functional a b c hb hc
    · exact False.elim (hc.2.1 ((p.mem_dom a).mpr ⟨b,hb⟩))
    · exact False.elim (hb.2.1 ((p.mem_dom a).mpr ⟨c,hc⟩))
    · exact hb.2.2.trans hc.2.2.symm
  countable_graph := p.countable_graph.union ((hA.image (fun a => (a,false))).mono (by
    rintro ⟨a,b⟩ ⟨ha,_,hb⟩
    exact ⟨a,ha,Prod.ext rfl hb.symm⟩))

theorem fill_le (p : Condition I κ) (A : Set (I × κ)) (hA : A.Countable) :
    p.fill A hA ≤ p := fun _ h => Or.inl h

theorem subset_dom_fill (p : Condition I κ) (A : Set (I × κ)) (hA : A.Countable) :
    A ⊆ (p.fill A hA).dom := by
  intro a ha
  by_cases h : a ∈ p.dom
  · exact dom_mono (p.fill_le A hA) h
  · exact ((p.fill A hA).mem_dom a).mpr ⟨false,Or.inr ⟨ha,h,rfl⟩⟩

end
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.TailSelector.TailData
universe u
noncomputable section
open scoped Classical
open CohenForcing
variable {G I κ : Type u} [Group G] [MulAction G I] (D : TailData G I)
variable [LinearOrder κ]

/-- Eventually the canonical representative of a coset acts just like any
other representative on each detector sequence. -/
theorem representative_eventually (g : G) (δ : D.Nonidentity) :
    ∃ N, ∀ n, N ≤ n → (g : D.Cosets).out • D.detector δ n = g • D.detector δ n := by
  obtain ⟨N,hN⟩ := D.detector_fixed_eventually
    (QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : D.Cosets))) δ
  refine ⟨N,fun n hn => ?_⟩
  have h := congrArg (fun i : I => (g : D.Cosets).out • i) (hN n hn)
  simpa only [← mul_smul,mul_inv_cancel_left] using h.symm

/-- Every bounded detector row is completely assigned after a finite initial
segment. The quantifier over all representatives makes covariance literal. -/
def Complete (p : Condition I κ) (α : κ) : Prop :=
  ∀ g : G, ∀ δ : D.Nonidentity, ∃ N, ∀ n, N ≤ n →
    ∀ b : Set.Iio α, (g • D.detector δ n,b.val) ∈ p.dom

theorem Complete.mono {p q : Condition I κ} {α : κ} (h : D.Complete p α) (hqp : q ≤ p) :
    D.Complete q α := by
  intro g δ
  obtain ⟨N,hN⟩ := h g δ
  exact ⟨N,fun n hn b => Condition.dom_mono hqp (hN n hn b)⟩

theorem Complete.downward {p : Condition I κ} {α β : κ}
    (h : D.Complete p α) (hβα : β ≤ α) : D.Complete p β := by
  intro g δ
  obtain ⟨N,hN⟩ := h g δ
  exact ⟨N,fun n hn b => hN n hn ⟨b.val,b.property.trans_le hβα⟩⟩

/-- Assigned bounded patterns cannot be altered by an extension. -/
theorem Complete.pattern_eq {p q : Condition I κ} {α : κ}
    (h : D.Complete p α) (hqp : q ≤ p) : D.pattern q.rows α = D.pattern p.rows α := by
  funext c δ
  apply (eventualMk_eq_iff _ _).mpr
  obtain ⟨N,hN⟩ := h c.out δ
  refine ⟨N,fun n hn => funext (fun b => ?_)⟩
  exact Condition.rows_eq_of_le hqp (hN n hn b)

theorem Complete.permute {p : Condition I κ} {α : κ}
    (h : D.Complete p α) (σ : G) : D.Complete (p.permute (MulAction.toPerm σ)) α := by
  intro g δ
  obtain ⟨N,hN⟩ := h (σ⁻¹*g) δ
  refine ⟨N,fun n hn b => ?_⟩
  obtain ⟨a,ha⟩ := (p.mem_dom _).mp (hN n hn b)
  apply ((p.permute (MulAction.toPerm σ)).mem_dom _).mpr
  refine ⟨a,?_⟩
  simpa only [Condition.mem_permute,Condition.coordinatePerm_symm_apply,
    MulAction.toPerm_symm_apply,mul_smul] using ha

omit [LinearOrder κ] in
theorem rows_permute (σ : G) (p : Condition I κ) :
    (p.permute (MulAction.toPerm σ)).rows = moveRows σ p.rows := by
  funext i a
  simpa only [moveRows,MulAction.toPerm_symm_apply] using
    Condition.rows_permute (MulAction.toPerm σ) p i a

/-- A good condition actually decides a distinguishing pattern; arbitrary
unassigned row values are never used for a stable selection. -/
def Good (p : Condition I κ) : Prop :=
  ∃ α : κ, D.Complete p α ∧ Function.Injective (D.pattern p.rows α)

theorem Good.mono {p q : Condition I κ} (h : D.Good p) (hqp : q ≤ p) : D.Good q := by
  obtain ⟨α,hc,hi⟩ := h
  refine ⟨α,hc.mono D hqp,?_⟩
  rwa [hc.pattern_eq D hqp]

theorem Good.permute [WellFoundedLT κ] {p : Condition I κ} (h : D.Good p) (σ : G) :
    D.Good (p.permute (MulAction.toPerm σ)) := by
  obtain ⟨α,hc,hi⟩ := h
  refine ⟨α,hc.permute D σ,?_⟩
  rw [rows_permute]
  exact (D.distinguishes_moveRows_iff σ p.rows α).mpr hi

/-- The countable coordinate family used by the fixed representatives. -/
def detectorSites : Set I :=
  Set.range (fun z : D.Cosets × D.Nonidentity × ℕ => z.1.out • D.detector z.2.1 z.2.2)

theorem detectorSites_countable [Countable D.Cosets] : D.detectorSites.Countable :=
  Set.countable_range _

theorem detectorSite_mem (c : D.Cosets) (δ : D.Nonidentity) (n : ℕ) :
    c.out • D.detector δ n ∈ D.detectorSites := ⟨(c,δ,n),rfl⟩

theorem complete_of_covered {p : Condition I κ} {α : κ}
    (h : D.detectorSites ×ˢ Set.Iio α ⊆ p.dom) : D.Complete p α := by
  intro g δ
  obtain ⟨N,hN⟩ := D.representative_eventually g δ
  refine ⟨N,fun n hn b => ?_⟩
  rw [← hN n hn]
  exact h ⟨D.detectorSite_mem (g : D.Cosets) δ n,b.property⟩

private theorem bounded_countable [Nonempty κ]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    {A : Type u} [Countable A] (f : A → κ) : ∃ α, ∀ a, f a < α := by
  let : Encodable A := Encodable.ofCountable A
  let g : ℕ → κ := fun n => (Encodable.decode (α := A) n).elim
    (Classical.choice ‹Nonempty κ›) f
  obtain ⟨α,hα⟩ := hbound g
  refine ⟨α,fun a => ?_⟩
  simpa only [g,Encodable.encodek,Option.elim_some] using hα (Encodable.encode a)

/-- In one countable extension all relevant unequal detector sites acquire
opposite bits below a common countable bound. This argument does not assume
that the ambient universe already contains distinct rows on all of I. -/
theorem good_dense [Nonempty κ] [Uncountable κ] [Countable D.Cosets]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    (hcount : ∀ α : κ, (Set.Iio α).Countable) (p : Condition I κ) :
    ∃ q, q ≤ p ∧ D.Good q := by
  let J := D.detectorSites
  let : Countable J := D.detectorSites_countable.to_subtype
  let A := {z : J × J // z.1 ≠ z.2}
  let R (z : A) (q : Condition I κ) :=
    ∃ a : κ, ((z.val.1.val,a),false) ∈ q.graph ∧ ((z.val.2.val,a),true) ∈ q.graph
  have hdense : ∀ z q, q ≤ p → ∃ r, r ≤ q ∧ R z r := by
    intro z q _
    have hne : z.val.1.val ≠ z.val.2.val := fun h => z.property (Subtype.ext h)
    obtain ⟨r,a,hr,hx,hy⟩ := q.separate_labels hne
    exact ⟨r,hr,a,hx,hy⟩
  obtain ⟨q,hqp,hq⟩ := Condition.countable_fusion p R
    (fun z q r hr ⟨a,hx,hy⟩ => ⟨a,hr hx,hr hy⟩) hdense
  choose bit hfalse htrue using hq
  obtain ⟨α,hα⟩ := bounded_countable hbound bit
  let B := J ×ˢ Set.Iio α
  have hB : B.Countable := D.detectorSites_countable.prod (hcount α)
  let r := q.fill B hB
  have hrq : r ≤ q := q.fill_le B hB
  refine ⟨r,hrq.trans hqp,α,D.complete_of_covered (q.subset_dom_fill B hB),?_⟩
  intro c e he
  by_contra hne
  have hne' : (c.out : D.Cosets) ≠ (e.out : D.Cosets) := by
    simpa only [QuotientGroup.out_eq'] using hne
  obtain ⟨δ,N,hN⟩ := D.detector_separates c.out e.out hne'
  obtain ⟨M,hM⟩ := (eventualMk_eq_iff _ _).mp (congrFun he δ)
  let x : J := ⟨c.out • D.detector δ (N+M),D.detectorSite_mem c δ (N+M)⟩
  let y : J := ⟨e.out • D.detector δ (N+M),D.detectorSite_mem e δ (N+M)⟩
  let z : A := ⟨(x,y),fun h => hN (N+M) (Nat.le_add_right _ _) (congrArg Subtype.val h)⟩
  have hh := congrFun (hM (N+M) (Nat.le_add_left _ _)) (⟨bit z,hα z⟩ : Set.Iio α)
  have hx : r.rows x.val (bit z) = false := r.rows_of_mem _ _ _ (hrq (hfalse z))
  have hy : r.rows y.val (bit z) = true := r.rows_of_mem _ _ _ (hrq (htrue z))
  exact Bool.false_ne_true (hx.symm.trans (hh.trans hy))

variable [WellFoundedLT κ]

theorem leastBound_le (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α)) (α : κ)
    (hα : Function.Injective (D.pattern R α)) : D.leastBound R h ≤ α :=
  not_lt.mp (wellFounded_lt.not_lt_min _ hα)

/-- This candidate does not yet mention a generic filter. -/
def conditionSelector (p : Condition I κ) (h : D.Good p) : D.Cosets :=
  D.selector p.rows ⟨h.choose,h.choose_spec.2⟩

theorem Good.complete_least {p : Condition I κ} (h : D.Good p) :
    D.Complete p (D.leastBound p.rows ⟨h.choose,h.choose_spec.2⟩) :=
  h.choose_spec.1.downward D (D.leastBound_le _ _ _ h.choose_spec.2)

/-- The first distinguishing bound is persistent, not an artifact of how
undefined rows were filled. -/
theorem leastBound_extension {p q : Condition I κ} (hp : D.Good p) (hq : D.Good q)
    (hqp : q ≤ p) :
    D.leastBound q.rows ⟨hq.choose,hq.choose_spec.2⟩ =
      D.leastBound p.rows ⟨hp.choose,hp.choose_spec.2⟩ := by
  let α := D.leastBound p.rows ⟨hp.choose,hp.choose_spec.2⟩
  let β := D.leastBound q.rows ⟨hq.choose,hq.choose_spec.2⟩
  have hc : D.Complete p α := hp.complete_least D
  have hi : Function.Injective (D.pattern q.rows α) := by
    rw [hc.pattern_eq D hqp]
    exact D.leastBound_distinguishes _ _
  have hβα : β ≤ α := D.leastBound_le _ _ _ hi
  have hi' : Function.Injective (D.pattern p.rows β) := by
    rw [← (hc.downward D hβα).pattern_eq D hqp]
    exact D.leastBound_distinguishes _ _
  exact le_antisymm hβα (D.leastBound_le _ _ _ hi')

omit [WellFoundedLT κ] in
theorem bestCoset_congr (R R' : I → κ → Bool) (α : κ)
    (h : D.pattern R α = D.pattern R' α) : D.bestCoset R α = D.bestCoset R' α := by
  unfold bestCoset
  congr 1
  rw [h]

/-- Every stronger condition makes the same coset decision. -/
theorem conditionSelector_extension {p q : Condition I κ} (hp : D.Good p) (hq : D.Good q)
    (hqp : q ≤ p) : D.conditionSelector q hq = D.conditionSelector p hp := by
  unfold conditionSelector selector
  rw [D.leastBound_extension hp hq hqp]
  exact D.bestCoset_congr _ _ _ ((hp.complete_least D).pattern_eq D hqp)

/-- Genuine covariance of the persistent decision made by a Cohen condition. -/
theorem conditionSelector_permute (p : Condition I κ) (hp : D.Good p) (σ : G)
    (hq : D.Good (p.permute (MulAction.toPerm σ))) :
    D.conditionSelector (p.permute (MulAction.toPerm σ)) hq =
      (σ : D.Cosets) * D.conditionSelector p hp := by
  unfold conditionSelector
  have hrow := rows_permute σ p
  have he : ∃ α, Function.Injective (D.pattern (moveRows σ p.rows) α) := by
    simpa only [hrow] using (show ∃ α, Function.Injective
      (D.pattern (p.permute (MulAction.toPerm σ)).rows α) from ⟨hq.choose,hq.choose_spec.2⟩)
  have hh := D.selector_covariance σ p.rows ⟨hp.choose,hp.choose_spec.2⟩ he
  convert hh using 1
  simp only [hrow]

/-- The downward-persistent relation that can be used as a name recipe. -/
def Selected (p : Condition I κ) (c : D.Cosets) : Prop :=
  ∃ h : D.Good p, D.conditionSelector p h = c

theorem Selected.mono {p q : Condition I κ} {c : D.Cosets}
    (h : D.Selected p c) (hqp : q ≤ p) : D.Selected q c := by
  obtain ⟨hp,rfl⟩ := h
  exact ⟨hp.mono D hqp,D.conditionSelector_extension hp (hp.mono D hqp) hqp⟩

theorem selected_unique {p : Condition I κ} {c e : D.Cosets}
    (hc : D.Selected p c) (he : D.Selected p e) : c = e := by
  obtain ⟨hp,rfl⟩ := hc
  obtain ⟨hq,rfl⟩ := he
  rfl

theorem Selected.permute {p : Condition I κ} {c : D.Cosets}
    (h : D.Selected p c) (σ : G) :
    D.Selected (p.permute (MulAction.toPerm σ)) ((σ : D.Cosets)*c) := by
  obtain ⟨hp,rfl⟩ := h
  exact ⟨hp.permute D σ,D.conditionSelector_permute p hp σ _⟩

theorem selected_compatible {p q : Condition I κ} {c e : D.Cosets}
    (hc : D.Selected p c) (he : D.Selected q e) (h : Condition.Compatible p q) : c = e :=
  D.selected_unique (hc.mono D (p.union_le_left q h)) (he.mono D (p.union_le_right q h))

end
end PartitionConsistency.TailSelector.TailData


/-! ## CosetPredicate -/

/-! Coset transport for predicates on the total space of computations.
The inverse moves every argument, in particular the actual Cohen condition. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
variable {I κ : Type u}
instance coordinateAction : MulAction (Equiv.Perm I) (Condition I κ) where
  smul π d := d.permute π
  one_smul := permute_one
  mul_smul := fun π σ d => permute_mul π σ d
@[simp] theorem smul_condition (π : Equiv.Perm I) (d : Condition I κ) :
    π • d = d.permute π := rfl
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.CosetPredicate
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
noncomputable section

def shift (g : G) (R : X → Prop) : X → Prop := fun x => R (g⁻¹ • x)

@[simp] theorem shift_one (R : X → Prop) : shift (1 : G) R = R := by
  funext x
  simp only [shift, inv_one, one_smul]

theorem shift_mul (g h : G) (R : X → Prop) :
    shift (g*h) R = shift g (shift h R) := by
  funext x
  simp only [shift, mul_inv_rev, mul_smul]

theorem shift_at_moved (g : G) (R : X → Prop) (x : X) :
    shift g R (g • x) = R x := by
  simp only [shift, inv_smul_smul]

def Invariant (K : Subgroup G) (R : X → Prop) : Prop :=
  ∀ k ∈ K, ∀ x, R (k • x) ↔ R x

theorem shift_eq (K : Subgroup G) (R : X → Prop) (hR : Invariant K R)
    {g h : G} (he : (g : G ⧸ K) = h) : shift g R = shift h R := by
  have hk : g⁻¹*h ∈ K := QuotientGroup.eq.mp he
  have hi : shift (g⁻¹*h) R = R := by
    funext x
    exact propext (hR _ (K.inv_mem hk) x)
  calc
    shift g R = shift g (shift (g⁻¹*h) R) := by rw [hi]
    _ = shift (g*(g⁻¹*h)) R := (shift_mul _ _ _).symm
    _ = shift h R := by rw [mul_inv_cancel_left]

end
end PartitionConsistency.CosetPredicate


/-! ## Corrected -/

/-! A component assignment on actual conditions: select a residual coset,
compute at the inverse-moved condition, then transport every argument back.
The quotient operation uses proved tail invariance, not an arbitrary choice
of a bijection. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.componentStabilizer hj v
local notation "K" => C.tailFixer hj

abbrev AssignmentPoint := CohenForcing.Condition I κ × Vertex q × labelFiberSet v × (S).Name

def preliminaryPoint (x : AssignmentPoint (κ := κ) hμ (v := v)) : Prop :=
  Preliminary hμ c hcard hsize hmerger hj E hE C x.1 x.2.1 x.2.2.1 x.2.2.2

theorem preliminaryPoint_move (k : K) (x : AssignmentPoint (κ := κ) hμ (v := v))
    (hx : preliminaryPoint hμ c hcard hsize hmerger hj E hE C x) :
    preliminaryPoint hμ c hcard hsize hmerger hj E hE C (k.val • x) := by
  obtain ⟨d,w,j,τ⟩ := x
  change Preliminary hμ c hcard hsize hmerger hj E hE C
    (d.permute k.val.val.val) (k.val.val • w) (k.val • j) (k.val.val.val • τ)
  rw [Vertex.Chain.tailFixer_fixes_label hj v C k j]
  exact preliminary_permute hμ c hcard hsize hmerger hj E hE C k d w j τ hx

theorem preliminaryPoint_invariant : CosetPredicate.Invariant K
    (preliminaryPoint hμ c hcard hsize hmerger hj E hE C) := by
  intro k hk x
  constructor
  · intro h
    have hh := preliminaryPoint_move hμ c hcard hsize hmerger hj E hE C ⟨k⁻¹,(K).inv_mem hk⟩ (k • x) h
    simpa only [inv_smul_smul] using hh
  · exact preliminaryPoint_move hμ c hcard hsize hmerger hj E hE C ⟨k,hk⟩ x

variable [LinearOrder κ] [WellFoundedLT κ]

/-- The persistent selected-coset version of the assignment predicate. -/
def Corrected (d : CohenForcing.Condition I κ) (w : Vertex q)
    (j : labelFiberSet v) (τ : (S).Name) : Prop :=
  ∃ g : G, (C.tailData hj).Selected d (g : G ⧸ K) ∧
    CosetPredicate.shift g (preliminaryPoint hμ c hcard hsize hmerger hj E hE C) (d,w,j,τ)

/-- Independence of the representative of the selected coset. -/
theorem corrected_selected {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name} (g : G)
    (hg : (C.tailData hj).Selected d (g : G ⧸ K)) :
    Corrected hμ c hcard hsize hmerger hj E hE C d w j τ ↔
      Preliminary hμ c hcard hsize hmerger hj E hE C
        (g⁻¹ • d) (g⁻¹ • w) (g⁻¹ • j) (g⁻¹ • τ) := by
  constructor
  · rintro ⟨k,hk,h⟩
    have he : (k : G ⧸ K) = g := (C.tailData hj).selected_unique hk hg
    have hs := CosetPredicate.shift_eq K
      (preliminaryPoint hμ c hcard hsize hmerger hj E hE C)
      (preliminaryPoint_invariant hμ c hcard hsize hmerger hj E hE C) he
    rw [hs] at h
    exact h
  · intro h
    exact ⟨g,hg,h⟩

variable {hμ c hcard hsize hmerger hj E hE C}

theorem corrected_mono {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name} (hed : e ≤ d)
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Corrected hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨g,hg,h⟩ := h
  refine ⟨g,hg.mono _ hed,?_⟩
  exact preliminary_mono ((CohenForcing.Condition.permuteOrderIso g.val.val⁻¹).monotone hed) h

theorem corrected_common {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ) : Vertex.Common v w := by
  obtain ⟨g,_,h⟩ := h
  have hc := Vertex.common_moved hj v g (preliminary_common h)
  change Vertex.Common v (g • (g⁻¹ • w)) at hc
  simpa only [smul_inv_smul] using hc

variable (hμ)

omit [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ] in
/-- Equality transport at a moved vertex, with the moved Cohen coordinate. -/
theorem root_eq_symmetry (g : Vertex.RootGroup q) (d : CohenForcing.Condition I κ)
    (w : Vertex q) (τ σ : (S).Name) :
    (S).atomic.EqF ((g • d,(g • w).diagram) : Poset M I κ) (g • τ) (g • σ) ↔
      (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ := by
  change (S).atomic.EqF ((d.permute g.val,w.diagram.permute g.val) : Poset M I κ)
      (g.val • τ) (g.val • σ) ↔ _
  simpa only [move_coe,permute] using
    ((S).eq_symmetry g.val ((d,w.diagram) : Poset M I κ) τ σ).symm

variable {hμ}

theorem corrected_congr {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ σ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ)
    (he : (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ) :
    Corrected hμ c hcard hsize hmerger hj E hE C d w j σ := by
  obtain ⟨g,hg,h⟩ := h
  exact ⟨g,hg,preliminary_congr h ((root_eq_symmetry hμ g.val⁻¹ d w τ σ).mpr he)⟩

variable (hμ c hcard hsize hmerger hj E hE C)

/-- Both injectivity and single-valuedness survive coset correction. -/
theorem corrected_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j k : labelFiberSet v} {τ σ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ)
    (h' : Corrected hμ c hcard hsize hmerger hj E hE C d w k σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = k := by
  obtain ⟨g,hg,h⟩ := h
  have hh := (corrected_selected hμ c hcard hsize hmerger hj E hE C g hg).mp h'
  rw [← root_eq_symmetry hμ g.val⁻¹ d w τ σ]
  exact (preliminary_eq_iff h hh).trans (MulAction.injective g⁻¹).eq_iff

/-- Covariance under every element of the entire component stabilizer. -/
theorem corrected_permute (g : G) (d : CohenForcing.Condition I κ) (w : Vertex q)
    (j : labelFiberSet v) (τ : (S).Name)
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Corrected hμ c hcard hsize hmerger hj E hE C
      (g • d) (g • w) (g • j) (g • τ) := by
  obtain ⟨k,hk,h⟩ := h
  refine ⟨g*k,?_,?_⟩
  · have hg : MulAction.toPerm g = g.val.val := by ext; rfl
    change (C.tailData hj).Selected (d.permute g.val.val) _
    rw [QuotientGroup.mk_mul]
    have hh := hk.permute (C.tailData hj) g
    rw [hg] at hh
    exact hh
  · change CosetPredicate.shift (g*k)
      (preliminaryPoint hμ c hcard hsize hmerger hj E hE C)
      (g • (d,w,j,τ))
    rw [CosetPredicate.shift_mul,CosetPredicate.shift_at_moved]
    exact h

/-- Pullback along a contraction retains precisely the same representative. -/
theorem corrected_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : labelFiberSet v} {τ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d z j τ) :
    Corrected hμ c hcard hsize hmerger hj E hE C d w j τ := by
  obtain ⟨g,hg,h⟩ := h
  exact ⟨g,hg,preliminary_restrict hμ c hcard hsize hmerger hj E hE C (f.move g.val⁻¹) h⟩

/-- Reflection along a contraction for a name already supported on its target. -/
theorem corrected_descend {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : labelFiberSet v} {τ : LocalName hμ c z.diagram}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    Corrected hμ c hcard hsize hmerger hj E hE C d z j τ.name := by
  obtain ⟨g,hg,h⟩ := h
  exact ⟨g,hg,preliminary_descend hμ c hcard hsize hmerger hj E hE C (f.move g.val⁻¹)
    (τ := τ.transport hμ g.val.val⁻¹) h⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## StableTransport -/

/-! Coordinate transport for the permanently decided availability ideal.
This is used both for coset correction and for moving between component
orbits. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

omit [Infinite M] [Infinite I] in
/-- Moving the entire local equality test also moves its normalized witness. -/
theorem forcedAvailable_permute_iff (π : Equiv.Perm I)
    (d : CohenForcing.Condition I κ) (r : Diagram M I) (τ : LocalName hμ c r) (n : M) :
    ForcedAvailable hμ c (d.permute π) (r.permute π) (τ.transport hμ π) n ↔
      ForcedAvailable hμ c d r τ n := by
  constructor
  · rintro ⟨σ,he⟩
    let ρ := σ.rebase hμ c (Diagram.permute_sub π r n).symm
    obtain ⟨ν,hν⟩ := (LocalName.transportEquiv hμ c π (r.sub n)).surjective ρ
    have hname : π • ν.name = σ.name := congrArg LocalName.name hν
    refine ⟨ν,?_⟩
    apply ((S).eq_symmetry π ((d,r) : Poset M I κ) ν.name τ.name).mpr
    simpa only [move_coe,permute,hname,LocalName.transport_name] using he
  · rintro ⟨σ,he⟩
    refine ⟨(σ.transport hμ π).rebase hμ c (Diagram.permute_sub π r n),?_⟩
    simpa only [move_coe,permute,LocalName.rebase_name,LocalName.transport_name] using
      ((S).eq_symmetry π ((d,r) : Poset M I κ) σ.name τ.name).mp he

/-- The actual ideal is preserved, not merely its cardinality. -/
theorem forcedAvailability_permute (π : Equiv.Perm I)
    (d : CohenForcing.Condition I κ) (r : Diagram M I) (a : M) (τ : LocalName hμ c r) :
    forcedAvailability hμ c hcard hsize hmerger (d.permute π) (r.permute π) a
        (τ.transport hμ π) = forcedAvailability hμ c hcard hsize hmerger d r a τ := by
  apply ConeIdeal.ext
  ext n
  erw [mem_forcedAvailability,mem_forcedAvailability,forcedAvailable_permute_iff]

variable {q : Diagram M I}

/-- An actual local class whose availability has become permanent. Keeping
the literal name as an argument avoids any chosen representative under
transport between vertices. -/
def StableAt (E : (S).Name) (d : CohenForcing.Condition I κ) (w : Vertex q)
    (τ : (S).Name) : Prop :=
  ∃ ρ : LocalName hμ c w.diagram, ρ.name = τ ∧
    (S).Forces ![τ,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)
      (SetLanguage.isClass 0 1 2) ∧
    ∀ e, e ≤ d → forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index ρ = w.ideal

/-- This permutation is allowed to move the component as well as its chain. -/
theorem stableAt_permute (E : (S).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (g : Vertex.RootGroup q) (d : CohenForcing.Condition I κ) (w : Vertex q) (τ : (S).Name)
    (h : StableAt hμ c hcard hsize hmerger E d w τ) :
    StableAt hμ c hcard hsize hmerger E (g • d) (g • w) (g • τ) := by
  obtain ⟨ρ,rfl,hel,hs⟩ := h
  refine ⟨ρ.transport hμ g.val,rfl,?_,?_⟩
  · change (S).Forces ![g.val • ρ.name,labelSet hμ c,E]
      ((d.permute g.val,w.diagram.permute g.val) : Poset M I κ) (SetLanguage.isClass 0 1 2)
    have hv : (fun i => g.val • (![ρ.name,labelSet hμ c,E] : Fin 3 → (S).Name) i) =
        ![g.val • ρ.name,labelSet hμ c,E] := by
      funext i
      fin_cases i
      · rfl
      · exact smul_labelSet hμ c g.val
      · exact hE g.val g.property
    simpa only [move_coe,permute,hv] using
      ((S).forces_symmetry g.val (SetLanguage.isClass 0 1 2)
        ![ρ.name,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)).mp hel
  · change ∀ e, e ≤ d.permute g.val → forcedAvailability hμ c hcard hsize hmerger e
        (w.diagram.permute g.val) w.index (ρ.transport hμ g.val) = w.ideal
    intro e he
    have hed : e.permute g.val⁻¹ ≤ d := by
      have hh := (CohenForcing.Condition.permuteOrderIso g.val⁻¹).monotone he
      change e.permute g.val⁻¹ ≤ (d.permute g.val).permute g.val⁻¹ at hh
      simpa only [CohenForcing.Condition.permute_inv_permute] using hh
    have hh := forcedAvailability_permute hμ c hcard hsize hmerger g.val
      (e.permute g.val⁻¹) w.diagram w.index ρ
    simpa only [CohenForcing.Condition.permute_permute_inv] using hh.trans (hs _ hed)

theorem stableAt_permute_iff (E : (S).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (g : Vertex.RootGroup q) (d : CohenForcing.Condition I κ) (w : Vertex q) (τ : (S).Name) :
    StableAt hμ c hcard hsize hmerger E (g • d) (g • w) (g • τ) ↔
      StableAt hμ c hcard hsize hmerger E d w τ := by
  constructor
  · intro h
    have hh := stableAt_permute hμ c hcard hsize hmerger E hE g⁻¹ (g • d) (g • w) (g • τ) h
    simpa only [inv_smul_smul] using hh
  · exact stableAt_permute hμ c hcard hsize hmerger E hE g d w τ

end
end PartitionConsistency.ProductForcing

end OAI
