import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.GraphFusion
import OAI.SetTheory.PartitionConsistency.Forcing.EquivariantMixing

namespace OAI

/-! ## CodeSelection -/

/-! Least-code selection at the level of forcing conditions. No generic
filter, regular ultrafilter, or selection of values in another universe is
assumed. The equivalence relation has a monotone truth value, and working
codes persist under refinement. -/
namespace PartitionConsistency.ConditionCodeSelection
universe u v
noncomputable section
variable {P : Type u} [Preorder P] {A : Type v}
variable (W : P → A → Prop) (E : P → A → A → Prop)

/-- A working code and the assertion that no smaller code can ever become a
working representative of the same value. -/
def Selected (a : A) (p : P) : Prop :=
  W p a ∧ ∀ q, q ≤ p → ∀ b, WellOrderingRel b a → ¬ (W q b ∧ E q a b)

variable (wmono : ∀ {p q a}, q ≤ p → W p a → W q a)
variable (emono : ∀ {p q a b}, q ≤ p → E p a b → E q a b)
variable (erefl : ∀ p a, E p a a)
variable (esymm : ∀ {p a b}, E p a b → E p b a)
variable (etrans : ∀ {p a b c}, E p a b → E p b c → E p a c)

include wmono in
theorem selected_mono {a : A} {p q : P} (hqp : q ≤ p)
    (h : Selected W E a p) : Selected W E a q :=
  ⟨wmono hqp h.1,fun r hr => h.2 r (hr.trans hqp)⟩

include esymm in
/-- Two persistent least codes agreeing at a condition are literally equal,
not merely equivalent. -/
theorem selected_unique {a b : A} {p : P}
    (ha : Selected W E a p) (hb : Selected W E b p) (hab : E p a b) : a = b := by
  rcases (trichotomous_of WellOrderingRel a b) with h | h | h
  · exact False.elim (hb.2 p le_rfl a h ⟨ha.1,esymm hab⟩)
  · exact h
  · exact False.elim (ha.2 p le_rfl b h ⟨hb.1,hab⟩)

include wmono emono erefl etrans in
/-- Every working code densely admits a selected representative. The
minimum is taken over the set of codes which can agree *somewhere below*
the starting condition; minimality therefore survives every refinement. -/
theorem dense_selected (p : P) (a : A) (ha : W p a) :
    ∃ q, q ≤ p ∧ ∃ b, Selected W E b q ∧ E q a b := by
  let B : Set A := {b | ∃ q, q ≤ p ∧ W q b ∧ E q a b}
  have hB : B.Nonempty := ⟨a,p,le_rfl,wmono le_rfl ha,erefl p a⟩
  let b := WellOrderingRel.isWellOrder.wf.min B hB
  obtain ⟨q,hqp,hb,hab⟩ := WellOrderingRel.isWellOrder.wf.min_mem B hB
  refine ⟨q,hqp,b,⟨hb,?_⟩,hab⟩
  intro r hrq c hcb hc
  apply WellOrderingRel.isWellOrder.wf.not_lt_min B
    (show c ∈ B from ⟨r,hrq.trans hqp,hc.1,etrans (emono hrq hab) hc.2⟩)
  exact hcb

/-- A coordinate transformation acts on conditions but leaves each ground
code in place (the same-code covariance of the source). It therefore also
preserves the persistent least-code predicate. -/
theorem selected_covariance (e : P ≃o P)
    (hw : ∀ p a, W (e p) a ↔ W p a)
    (he : ∀ p a b, E (e p) a b ↔ E p a b) (a : A) (p : P) :
    Selected W E a (e p) ↔ Selected W E a p := by
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨(hw p a).mp ha,fun q hqp b hba h => ?_⟩
    exact hb (e q) (e.monotone hqp) b hba
      ⟨(hw q b).mpr h.1,(he q a b).mpr h.2⟩
  · rintro ⟨ha,hb⟩
    refine ⟨(hw p a).mpr ha,fun q hqp b hba h => ?_⟩
    have hqp' : e.symm q ≤ p := by simpa only [e.symm_apply_apply] using e.symm.monotone hqp
    exact hb (e.symm q) hqp' b hba
      ⟨(hw (e.symm q) b).mp (by simpa only [e.apply_symm_apply] using h.1),
       (he (e.symm q) a b).mp (by simpa only [e.apply_symm_apply] using h.2)⟩

end
end PartitionConsistency.ConditionCodeSelection


/-! ## PrincipalCode -/

/-! The least-code construction without an ambient fully generic filter.
The names and glued quotient values are the actual ones from the local
symbolic system. The principal filter at a condition is used only as a
convenient quotient notation for equality forced by that condition. -/
namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

@[simp] theorem principalFilter_move (p : P) (e : P ≃o P) :
    (principalFilter p).move e = principalFilter (e p) := by
  apply Order.Ideal.ext
  ext q
  change (p ≤ e.symm q) ↔ (e p ≤ q)
  exact (e.to_galoisConnection _ _).symm

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- A code keeps representing a genuine exact-fiber value at every stronger
Cohen condition. This is a predicate on the already defined name collection,
not an extra mathematical hypothesis about that collection. -/
def Works (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C) : Prop :=
  ∀ e, e ≤ d → ∃ b : (D[principalFilter e]).Glued hj v,
    Represents hμ c hcard hsize hmerger hj E hE C (principalFilter e) a b

/-- Eventual equality forced by one Cohen condition. Every comparison is of
actual names at their chain diagrams. -/
def Same (d : CohenForcing.Condition I κ) (a b : ChainCode hμ c C) : Prop :=
  ∃ N, ∀ i, N ≤ i → (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name

variable {hμ c hcard hsize hmerger hj E hE C}

theorem works_mono {d e : CohenForcing.Condition I κ} {a : ChainCode hμ c C}
    (hed : e ≤ d) (ha : Works hμ c hcard hsize hmerger hj E hE C d a) :
    Works hμ c hcard hsize hmerger hj E hE C e a :=
  fun f hfe => ha f (hfe.trans hed)

omit [Infinite M] [Infinite I] in
theorem same_refl (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C) :
    Same hμ c C d a a := ⟨0,fun i _ => (localAtomic hμ (C.vertex i).diagram).eq_refl d _⟩

omit [Infinite M] [Infinite I] in
theorem same_symm {d : CohenForcing.Condition I κ} {a b : ChainCode hμ c C}
    (h : Same hμ c C d a b) : Same hμ c C d b a := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => (localAtomic hμ (C.vertex i).diagram).eq_symm (hN i hi)⟩

omit [Infinite M] [Infinite I] in
theorem same_trans {d : CohenForcing.Condition I κ} {a b f : ChainCode hμ c C}
    (h : Same hμ c C d a b) (h' : Same hμ c C d b f) : Same hμ c C d a f := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := h'
  exact ⟨max N L,fun i hi => (localAtomic hμ (C.vertex i).diagram).eq_trans
    (hN i ((le_max_left _ _).trans hi)) (hL i ((le_max_right _ _).trans hi))⟩

omit [Infinite M] [Infinite I] in
theorem same_mono {d e : CohenForcing.Condition I κ} {a b : ChainCode hμ c C}
    (hed : e ≤ d) (h : Same hμ c C d a b) : Same hμ c C e a b := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => (localAtomic hμ (C.vertex i).diagram).eq_mono hed (hN i hi)⟩

/-- At one vertex, equality of the glued points is precisely equality of
the local symbolic quotient values. -/
theorem at_eq_iff {F : GenericFilter (CohenForcing.Condition I κ)} {w : Vertex q}
    {τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name}
    {b b' : (D[F]).Glued hj v}
    (hb : At hμ c hcard hsize hmerger hj E hE F w τ b)
    (hb' : At hμ c hcard hsize hmerger hj E hE F w σ b') :
    b = b' ↔ (localAtomic hμ w.diagram).EqG F τ σ := by
  obtain ⟨hw,x,ρ,hρ,hx,rfl⟩ := hb
  obtain ⟨hw',y,ν,hν,hy,rfl⟩ := hb'
  rw [← hρ,← hν]
  rw [← LocalQuotient.ofName_eq F ρ ν,hx,hy]
  constructor
  · intro h
    exact congrArg (fun z : (D[F]).vertexFiber w => z.val.val)
      ((D[F]).toGlued_injective hj v w hw h)
  · intro h
    have he : x = y := Subtype.ext (Subtype.ext h)
    subst y
    rfl

/-- Eventual forced equality detects equality of genuinely represented
points. This theorem applies to each principal quotient, without assuming
that the filter meets ANY dense sets. -/
theorem same_iff_represents_eq {d : CohenForcing.Condition I κ} {a b : ChainCode hμ c C}
    {x y : (D[principalFilter d]).Glued hj v}
    (ha : Represents hμ c hcard hsize hmerger hj E hE C (principalFilter d) a x)
    (hb : Represents hμ c hcard hsize hmerger hj E hE C (principalFilter d) b y) :
    Same hμ c C d a b ↔ x = y := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hb
  have hiff (i : ℕ) (hn : N ≤ i) (hl : L ≤ i) :
      x = y ↔ (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name :=
    (at_eq_iff (hN i hn) (hL i hl)).trans
      ((localAtomic hμ (C.vertex i).diagram).eqG_principal d _ _)
  constructor
  · rintro ⟨K,hK⟩
    exact (hiff (max (max N L) K)
      ((le_max_left N L).trans (le_max_left _ _))
      ((le_max_right N L).trans (le_max_left _ _))).mpr (hK _ (le_max_right _ _))
  · intro he
    exact ⟨max N L,fun i hi => (hiff i
      ((le_max_left _ _).trans hi) ((le_max_right _ _).trans hi)).mp he⟩

variable (hμ c hcard hsize hmerger hj E hE C)

/-- Persistent least codes, defined over the fixed ground wellordering. -/
abbrev Selected (a : ChainCode hμ c C) (d : CohenForcing.Condition I κ) : Prop :=
  ConditionCodeSelection.Selected (Works hμ c hcard hsize hmerger hj E hE C)
    (Same hμ c C) a d

theorem selected_mono {a : ChainCode hμ c C} {d e : CohenForcing.Condition I κ}
    (hed : e ≤ d) (ha : Selected hμ c hcard hsize hmerger hj E hE C a d) :
    Selected hμ c hcard hsize hmerger hj E hE C a e :=
  ConditionCodeSelection.selected_mono
    (Works hμ c hcard hsize hmerger hj E hE C) (Same hμ c C)
    (fun h ha => works_mono h ha) hed ha

theorem selected_unique {a b : ChainCode hμ c C} {d : CohenForcing.Condition I κ}
    (ha : Selected hμ c hcard hsize hmerger hj E hE C a d)
    (hb : Selected hμ c hcard hsize hmerger hj E hE C b d)
    (hab : Same hμ c C d a b) : a = b :=
  ConditionCodeSelection.selected_unique
    (Works hμ c hcard hsize hmerger hj E hE C) (Same hμ c C)
    (fun h => same_symm h) ha hb hab

theorem dense_selected (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a) :
    ∃ e, e ≤ d ∧ ∃ b, Selected hμ c hcard hsize hmerger hj E hE C b e ∧ Same hμ c C e a b :=
  ConditionCodeSelection.dense_selected
    (Works hμ c hcard hsize hmerger hj E hE C) (Same hμ c C)
    (fun h hw => works_mono h hw)
    (fun h he => same_mono h he) same_refl (fun h h' => same_trans h h') d a ha

/-- The working-code predicate is invariant under a tail fixer acting on the
condition. The code itself, and its prescribed ground ordering, do not move. -/
theorem works_covariance (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (a : ChainCode hμ c C) :
    Works hμ c hcard hsize hmerger hj E hE C (d.permute k.val.val.val) a ↔
    Works hμ c hcard hsize hmerger hj E hE C d a := by
  let e := CohenForcing.Condition.permuteOrderIso (κ := κ) k.val.val.val
  have hf (f : CohenForcing.Condition I κ) :
      (∃ x : (D[principalFilter (e f)]).Glued hj v,
        Represents hμ c hcard hsize hmerger hj E hE C (principalFilter (e f)) a x) ↔
      ∃ x : (D[principalFilter f]).Glued hj v,
        Represents hμ c hcard hsize hmerger hj E hE C (principalFilter f) a x := by
    rw [← principalFilter_move f e]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨y,rfl⟩ := (transport hμ c hcard hsize hmerger hj E hE (principalFilter f) k.val).surjective x
      exact ⟨y,(represents_same_code hμ c hcard hsize hmerger hj E hE C _ k a y).mp hx⟩
    · rintro ⟨y,hy⟩
      exact ⟨transport hμ c hcard hsize hmerger hj E hE (principalFilter f) k.val y,
        (represents_same_code hμ c hcard hsize hmerger hj E hE C _ k a y).mpr hy⟩
  constructor
  · intro h f hfd
    exact (hf f).mp (h (e f) (e.monotone hfd))
  · intro h f hfd
    change f ≤ e d at hfd
    have hfd' : e.symm f ≤ d := by
      simpa only [e.symm_apply_apply] using e.symm.monotone hfd
    have hh := (hf (e.symm f)).mpr (h (e.symm f) hfd')
    exact (show e (e.symm f) = f from e.apply_symm_apply f) ▸ hh

omit [Infinite M] [Infinite I] in
/-- Eventual equality has the same covariance, again for the unchanged
codes. This uses literal fixation on a tail, not invariance of the code set's
wellordering under coordinatewise transport. -/
theorem same_covariance (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (a b : ChainCode hμ c C) :
    Same hμ c C (d.permute k.val.val.val) a b ↔ Same hμ c C d a b := by
  obtain ⟨N,hN⟩ := tail_fixed hμ c hj C k
  have he (i : ℕ) (hi : N ≤ i) :
      (localAtomic hμ (C.vertex i).diagram).EqF (d.permute k.val.val.val) (a i).name (b i).name ↔
      (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name := by
    have hdg : (C.vertex i).diagram.permute k.val.val.val = (C.vertex i).diagram :=
      congrArg Vertex.diagram (hN i hi).1
    have hh := (system hμ).eq_symmetry k.val.val.val
      ((d,(C.vertex i).diagram) : Poset M I κ) (a i).name (b i).name
    simpa only [localAtomic,move_coe,permute,hdg,(hN i hi).2 (a i),(hN i hi).2 (b i)] using hh.symm
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)).mp
      (hL i ((le_max_right _ _).trans hi))⟩
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)).mpr
      (hL i ((le_max_right _ _).trans hi))⟩

/-- Condition-level covariance of least-code selection. All auxiliary
wellorders remain fixed. -/
theorem selected_covariance (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (a : ChainCode hμ c C) :
    Selected hμ c hcard hsize hmerger hj E hE C a (d.permute k.val.val.val) ↔
      Selected hμ c hcard hsize hmerger hj E hE C a d :=
  ConditionCodeSelection.selected_covariance _ _
    (CohenForcing.Condition.permuteOrderIso k.val.val.val)
    (works_covariance hμ c hcard hsize hmerger hj E hE C k)
    (same_covariance hμ c hj C k) a d

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## PersistentCode -/

/-! Stable availability gives actual working ground codes, persistently at
every refinement. This supplies the density input for least-code ranks,
without a countable family of external fully generic filters. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- Eligibility adds no restriction to the availability witnesses below a
supporting root: a representative of an eligible class is itself eligible,
by local decision. -/
theorem eligibleSystem_availability_eq (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (a : M) (ha : r.sub a = q) (x : (D[F]).Obj r) :
    (D[F]).availability r a x =
      (allLocalSystem (c := c) hμ hcard hsize hmerger F).availability r a x.val := by
  apply ConeIdeal.ext
  ext n
  change (n ≤ (show LeftDivOrder M from a) ∧ ∃ y : (D[F]).Obj (r.sub n),
      (D[F]).restrict (r.self_le_sub n) y = x) ↔
    n ≤ (show LeftDivOrder M from a) ∧ ∃ y : LocalQuotient (c := c) hμ F (r.sub n),
      LocalQuotient.restrict F (r.self_le_sub n) y = x.val
  apply and_congr_right
  intro hn
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y.val,congrArg Subtype.val hy⟩
  · rintro ⟨y,hy⟩
    have hrq : r.sub n ≤ q := ha ▸ r.sub_mono hn
    have hey : Eligible hμ c F (r.sub n) E y :=
      (eligible_restrict_iff hμ c hsize hmerger F E (r.self_le_sub n)
        (supported_mono hμ hrq E hE) y).mp (hy.symm ▸ x.property.2)
    exact ⟨⟨y,hrq,hey⟩,Subtype.ext hy⟩

/-- For any chosen name, the actual exact-fiber predicate in a principal
quotient agrees with eligibility and its computed forced availability. -/
theorem exists_fiber_principal (d : CohenForcing.Condition I κ) (v : Vertex q)
    (τ : LocalName hμ c v.diagram)
    (hel : (system hμ).Forces ![τ.name,labelSet hμ c,E]
      ((d,v.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2))
    (hU : forcedAvailability hμ c hcard hsize hmerger d v.diagram v.index τ = v.ideal) :
    ∃ x : (D[principalFilter d]).vertexFiber v,
      LocalQuotient.ofName (principalFilter d) τ = x.val.val := by
  let x : (D[principalFilter d]).Obj v.diagram :=
    ⟨LocalQuotient.ofName (principalFilter d) τ,⟨v.index,v.root⟩,d,(mem_principalFilter d d).mpr le_rfl,hel⟩
  refine ⟨⟨x,?_⟩,rfl⟩
  rw [eligibleSystem_availability_eq hμ c hcard hsize hmerger E hE
    (principalFilter d) v.diagram v.index v.root x]
  exact hU

namespace ChainCode
variable (hj : HasConditionalJoins (LeftDivOrder M)) {v : Vertex q} (C : Vertex.Chain v)

/-- An explicit eligible name with permanently constant ideal at the root
has a code which works at EVERY refinement of the condition. At each chain
vertex the code's entry remains the exact same ground normalized name. -/
theorem exists_working_code_of_stable (d : CohenForcing.Condition I κ)
    (τ : LocalName hμ c v.diagram)
    (hel : (system hμ).Forces ![τ.name,labelSet hμ c,E]
      ((d,v.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2))
    (hstable : ∀ e, e ≤ d →
      forcedAvailability hμ c hcard hsize hmerger e v.diagram v.index τ = v.ideal) :
    ∃ a : ChainCode hμ c C,
      Works hμ c hcard hsize hmerger hj E hE C d a ∧
      ∀ i, (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) (a i).name τ.name := by
  have hex (e : CohenForcing.Condition I κ) (hed : e ≤ d) :
      ∃ x : (D[principalFilter e]).vertexFiber v,
        LocalQuotient.ofName (principalFilter e) τ = x.val.val := by
    exact exists_fiber_principal hμ c hcard hsize hmerger E hE e v τ
      ((system hμ).atomic.forceFormula_mono
        (WithTop.coe_le_coe.mpr (show (e,v.diagram) ≤ (d,v.diagram) from ⟨hed,le_rfl⟩)) hel)
      (hstable e hed)
  obtain ⟨x,hx⟩ := hex d le_rfl
  have harr (i : ℕ) : Nonempty (v.Arrow (C.vertex i)) := by
    simpa only [C.first] using C.increasing 0 i (Nat.zero_le i)
  let f (i : ℕ) : v.Arrow (C.vertex i) := (harr i).some
  let hdiag (i : ℕ) : v.diagram ≤ (C.vertex i).diagram := ⟨(f i).index,(f i).diagram⟩
  have hcodes (i : ℕ) : ∃ σ : LocalName hμ c (C.vertex i).diagram,
      (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) σ.name τ.name := by
    obtain ⟨y,hy⟩ := (D[principalFilter d]).arrowMap_bijective hj (f i) |>.2 x
    obtain ⟨σ,hσ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ
      (principalFilter d) (C.vertex i).diagram) y.val.val
    refine ⟨σ,?_⟩
    apply ((localAtomic hμ v.diagram).eqG_principal d σ.name τ.name).mp
    apply (LocalQuotient.ofName_eq (principalFilter d) (σ.restrict (hdiag i)) τ).mp
    calc
      LocalQuotient.ofName (principalFilter d) (σ.restrict (hdiag i)) =
          LocalQuotient.restrict (principalFilter d) (hdiag i) y.val.val := congrArg (LocalQuotient.restrict (principalFilter d) (hdiag i)) hσ
      _ = x.val.val := congrArg (fun z : (D[principalFilter d]).vertexFiber v => z.val.val) hy
      _ = LocalQuotient.ofName (principalFilter d) τ := hx.symm
  choose a ha using hcodes
  refine ⟨a,?_,ha⟩
  intro e hed
  obtain ⟨x',hx'⟩ := hex e hed
  refine ⟨(D[principalFilter e]).toGlued hj v v (Vertex.Common.refl v) x',0,fun i _ => ?_⟩
  obtain ⟨y,hy⟩ := (D[principalFilter e]).arrowMap_bijective hj (f i) |>.2 x'
  have heq : LocalQuotient.ofName (principalFilter e) (a i) = y.val.val := by
    apply LocalQuotient.restrict_injective (principalFilter e) hsize hmerger (hdiag i)
    have ht : LocalQuotient.ofName (principalFilter e) ((a i).restrict (hdiag i)) =
        LocalQuotient.ofName (principalFilter e) τ := by
      apply (LocalQuotient.ofName_eq (principalFilter e) _ _).mpr
      apply ((localAtomic hμ v.diagram).eqG_principal e _ _).mpr
      exact (system hμ).atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (e,v.diagram) ≤ (d,v.diagram) from ⟨hed,le_rfl⟩)) (ha i)
    exact ht.trans (hx'.trans
      (congrArg (fun z : (D[principalFilter e]).vertexFiber v => z.val.val) hy).symm)
  refine ⟨C.common i,y,a i,rfl,heq,?_⟩
  rw [← (D[principalFilter e]).toGlued_arrow hj v v (C.vertex i)
    (Vertex.Common.refl v) (C.common i) (f i) y,hy]

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## OrdinalName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The semantic transitivity clause, with unrestricted HS names. -/
def TransF (p : P) (σ : S.Name) : Prop :=
  ∀ (τ ν : S.Name) (q : P), q ≤ p →
    S.atomic.MemF q τ σ → S.atomic.MemF q ν τ → S.atomic.MemF q ν σ

/-- A transitive set of transitive sets; used to prove ordinal preservation,
not as a replacement for the ordinal formula in the statement of ACwo. -/
def OrdF (p : P) (σ : S.Name) : Prop :=
  S.TransF p σ ∧ ∀ (τ : S.Name) (q : P), q ≤ p → S.atomic.MemF q τ σ → S.TransF q τ

theorem transF_mono {p q : P} {σ : S.Name} (h : q ≤ p) (ht : S.TransF p σ) :
    S.TransF q σ := fun τ ν r hr => ht τ ν r (hr.trans h)

theorem transF_congr {p : P} {σ τ : S.Name} (he : S.atomic.EqF p σ τ) :
    S.TransF p σ ↔ S.TransF p τ := by
  have forward {σ τ : S.Name} (he : S.atomic.EqF p σ τ) (h : S.TransF p σ) :
      S.TransF p τ := by
    intro ν χ q hqp hν hχ
    have hem := S.atomic.eq_mono hqp he
    exact (S.atomic.mem_congr (S.atomic.eq_refl q χ) hem).mp
      (h ν χ q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν) hem).mpr hν) hχ)
  exact ⟨forward he,forward (S.atomic.eq_symm he)⟩

theorem ordF_mono {p q : P} {σ : S.Name} (h : q ≤ p) (ho : S.OrdF p σ) :
    S.OrdF q σ := ⟨S.transF_mono h ho.1,fun τ r hr => ho.2 τ r (hr.trans h)⟩

theorem ordF_congr {p : P} {σ τ : S.Name} (he : S.atomic.EqF p σ τ) :
    S.OrdF p σ ↔ S.OrdF p τ := by
  have forward {σ τ : S.Name} (he : S.atomic.EqF p σ τ) (h : S.OrdF p σ) :
      S.OrdF p τ := by
    refine ⟨(S.transF_congr he).mp h.1,?_⟩
    intro ν q hqp hν
    exact h.2 ν q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν)
      (S.atomic.eq_mono hqp he)).mpr hν)
  exact ⟨forward he,forward (S.atomic.eq_symm he)⟩

theorem ordF_mem {p : P} {σ τ : S.Name} (ho : S.OrdF p σ)
    (hm : S.atomic.MemF p τ σ) : S.OrdF p τ := by
  refine ⟨ho.2 τ p le_rfl hm,?_⟩
  intro ν q hqp hν
  exact ho.2 ν q hqp (ho.1 τ ν q hqp (S.atomic.mem_mono hqp hm) hν)

theorem forces_transitiveSet {n} (v : Fin n → S.Name) (p : P) (x : Fin n) :
    S.Forces v p (SetLanguage.transitiveSet x) ↔ S.TransF p (v x) := by
  simp only [Forces,SetLanguage.transitiveSet,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_mem]
  constructor
  · intro h τ ν q hqp hτ hν
    exact h τ ν q hqp hτ q le_rfl hν
  · intro h τ ν q hqp hτ r hrq hν
    exact h τ ν r (hrq.trans hqp) (S.atomic.mem_mono hrq hτ) hν

/-- The literal ordinal sentence implies the semantic hereditary transitivity
used in the rank induction. Internal well-foundedness is not confused with
external well-foundedness of a model. -/
theorem ordF_of_forces_ordinal {n} (v : Fin n → S.Name) (p : P) (x : Fin n)
    (ho : S.Forces v p (SetLanguage.ordinal x)) : S.OrdF p (v x) := by
  have ht : S.Forces v p (SetLanguage.transitiveSet x) := ho.1
  have hl : S.Forces v p (SetLanguage.membershipLinear x) := ho.2.1
  have ht' := (S.forces_transitiveSet v p x).mp ht
  refine ⟨ht',?_⟩
  intro τ q hqp hτ ν χ r hrq hν hχ
  simp only [Forces,SetLanguage.membershipLinear,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem] at hl
  have hτ' := S.atomic.mem_mono hrq hτ
  have hν' := ht' τ ν r (hrq.trans hqp) hτ' hν
  have hχ' := ht' ν χ r (hrq.trans hqp) hν' hχ
  exact hl.2.1 χ ν τ r (hrq.trans hqp) hχ' r le_rfl hν' r le_rfl hτ' r le_rfl ⟨hχ,hν⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Ordinal preservation for unrestricted HS names. A condition forcing a
transitive set of transitive sets has an extension deciding it to be a ground
ordinal. The quantitative bound is proved by induction on literal name rank. -/
theorem ordF_eq_check_le (σ : S.Name) (p : P) (ho : S.OrdF p σ) :
    ∃ q, q ≤ p ∧ ∃ β : Ordinal.{u}, β ≤ σ.raw.rank ∧
      S.atomic.EqF q σ (Name.check β.toZFSet) := by
  classical
  induction σ using (InvImage.wf (fun σ : S.Name => σ.raw) child_wf).induction generalizing p with
  | h σ ih =>
    have hbounded : ∀ (ν : S.Name) (q : P), q ≤ p → S.atomic.MemF q ν σ →
        S.atomic.MemF q ν (Name.check σ.raw.rank.toZFSet) := by
      intro ν q hqp hm
      apply (S.mem_check _ ν q).mpr
      intro r hrq
      obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := (S.mem_iff.mp hm) r hrq
      have hτσ : S.atomic.MemF s τ σ := S.mem_of_edge he hsc
      obtain ⟨t,hts,β,hβ,hτ⟩ := ih τ ⟨S.code c,he⟩ s
        (S.ordF_mem (S.ordF_mono (hsr.trans (hrq.trans hqp)) ho) hτσ)
      exact ⟨t,hts.trans hsr,β.toZFSet,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr
          (hβ.trans_lt (Child.rank_lt ⟨S.code c,he⟩)),
        S.atomic.eq_trans (S.atomic.eq_mono hts heq) hτ⟩
    have hmiss : ¬ S.atomic.MemF p (Name.check σ.raw.rank.toZFSet) σ := by
      intro hm
      exact ZFSet.mem_irrefl _ ((S.mem_check_check _ _ p).mp
        (hbounded _ p le_rfl hm))
    obtain ⟨α,hα,hmin⟩ := Ordinal.lt_wf.has_min
      {α : Ordinal.{u} | ¬ S.atomic.MemF p (Name.check α.toZFSet) σ} ⟨σ.raw.rank,hmiss⟩
    have hαle : α ≤ σ.raw.rank := le_of_not_gt (hmin _ hmiss)
    have hbelow : ∀ β < α, S.atomic.MemF p (Name.check β.toZFSet) σ := by
      intro β hβ
      by_contra hn
      exact hmin β hn hβ
    have hneg : ∃ q, q ≤ p ∧ ∀ r, r ≤ q →
        ¬ S.atomic.MemF r (Name.check α.toZFSet) σ := by
      by_contra hn
      push Not at hn
      exact hα (S.atomic_regular.2 p (Name.check α.toZFSet) σ hn)
    obtain ⟨q,hqp,hneg⟩ := hneg
    refine ⟨q,hqp,α,hαle,S.eq_of_same_members ?_⟩
    intro ν r hrq
    constructor
    · intro hm
      apply (S.mem_check _ ν r).mpr
      intro s hsr
      obtain ⟨t,hts,y,hy,hey⟩ := (S.mem_check _ ν r).mp
        (hbounded ν r (hrq.trans hqp) hm) s hsr
      obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      have hβσ : S.atomic.MemF t (Name.check β.toZFSet) σ :=
        (S.atomic.mem_congr hey (S.atomic.eq_refl t σ)).mp
          (S.atomic.mem_mono (hts.trans hsr) hm)
      have hβα : β < α := by
        by_contra hn
        rcases (not_lt.mp hn).eq_or_lt with h | h
        · exact hneg t (hts.trans (hsr.trans hrq)) (h.symm ▸ hβσ)
        · exact hneg t (hts.trans (hsr.trans hrq))
            (ho.1 (Name.check β.toZFSet) (Name.check α.toZFSet) t
              (hts.trans (hsr.trans (hrq.trans hqp))) hβσ
              (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr h) t))
      exact ⟨t,hts,β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hβα,hey⟩
    · intro hm
      apply S.atomic_regular.2
      intro s hsr
      obtain ⟨t,hts,y,hy,hey⟩ := (S.mem_check _ ν r).mp hm s hsr
      obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      exact ⟨t,hts,(S.atomic.mem_congr hey (S.atomic.eq_refl t σ)).mpr
        (S.atomic.mem_mono (hts.trans (hsr.trans (hrq.trans hqp))) (hbelow β hβ))⟩

/-- Dense decision of any name satisfying the actual ordinal formula. This
applies at arbitrary rank, not merely to normalized subset names. -/
theorem forces_ordinal_decide {n} (v : Fin n → S.Name) (p : P) (x : Fin n)
    (ho : S.Forces v p (SetLanguage.ordinal x)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ β : Ordinal.{u},
      S.atomic.EqF r (v x) (Name.check β.toZFSet) := by
  intro q hqp
  obtain ⟨r,hrq,β,_,he⟩ := S.ordF_eq_check_le (v x) q
    (S.ordF_mono hqp (S.ordF_of_forces_ordinal v p x ho))
  exact ⟨r,hrq,β,he⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
