import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.OrbitAssignments

namespace OAI

/-! ## AssignedGraph -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

/-- A bounded graph entry is witnessed by a genuine local assignment, with
forced equality to its literal label and its normalized class name. -/
def GraphWitness (p : Poset M I κ) (x y : (S).Name) : Prop :=
  ∃ (d : CohenForcing.Condition I κ) (w : Vertex q) (j : I)
    (τ : LocalName hμ c w.diagram),
    p ≤ (d,w.diagram) ∧ Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name ∧
    (S).atomic.EqF p x (label hμ c j) ∧ (S).atomic.EqF p y τ.name

/-- Density closure of the literal entry relation. -/
def GraphHolds (p : Poset M I κ) (x y : (S).Name) : Prop :=
  ∀ r, r ≤ p → ∃ s, s ≤ r ∧ GraphWitness hμ c hcard hsize hmerger hj H E hE s x y

theorem graphWitness_mono {p r : Poset M I κ} {x y : (S).Name} (hr : r ≤ p)
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    GraphWitness hμ c hcard hsize hmerger hj H E hE r x y := by
  obtain ⟨d,w,j,τ,hp,ha,hx,hy⟩ := h
  exact ⟨d,w,j,τ,hr.trans hp,ha,(S).atomic.eq_mono hr hx,(S).atomic.eq_mono hr hy⟩

def graphRelation : (S).BinaryRelation where
  holds := GraphHolds hμ c hcard hsize hmerger hj H E hE
  mono h hh r hr := hh r (hr.trans h)
  regular h r hr := by
    obtain ⟨s,hs,hh⟩ := h r hr
    obtain ⟨t,ht,hw⟩ := hh s le_rfl
    exact ⟨t,ht.trans hs,hw⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : (S).Name} (hx : (S).atomic.EqF p x x')
        (hy : (S).atomic.EqF p y y')
        (h : GraphHolds hμ c hcard hsize hmerger hj H E hE p x y) :
        GraphHolds hμ c hcard hsize hmerger hj H E hE p x' y' := by
      intro r hr
      obtain ⟨s,hs,d,w,j,τ,hp,ha,hxj,hyτ⟩ := h r hr
      exact ⟨s,hs,d,w,j,τ,hp,ha,
        (S).atomic.eq_trans ((S).atomic.eq_symm ((S).atomic.eq_mono (hs.trans hr) hx)) hxj,
        (S).atomic.eq_trans ((S).atomic.eq_symm ((S).atomic.eq_mono (hs.trans hr) hy)) hyτ⟩
    exact ⟨step hx hy,step ((S).atomic.eq_symm hx) ((S).atomic.eq_symm hy)⟩

theorem graphWitness_holds {p : Poset M I κ} {x y : (S).Name}
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x y :=
  fun r hr => ⟨r,le_rfl,graphWitness_mono hμ c hcard hsize hmerger hj H E hE hr h⟩

/-- Each literal entry really has its value in the quotient set. -/
theorem graphWitness_bounds {p : Poset M I κ} {x y : (S).Name}
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    (S).atomic.MemF p x (labelSet hμ c) ∧ (S).atomic.MemF p y (quotientName hμ c E) := by
  obtain ⟨d,w,j,τ,hp,ha,hx,hy⟩ := h
  obtain ⟨_,_,hclass,_⟩ := assigned_stable hμ c hcard hsize hmerger hj H E hE ha
  exact ⟨((S).atomic.mem_congr hx ((S).atomic.eq_refl p _)).mpr (label_mem_labelSet hμ c j p),
    ((S).atomic.mem_congr hy ((S).atomic.eq_refl p _)).mpr
      ((S).atomic.mem_mono hp ((mem_quotientName_iff_isClass hμ c E τ.name _).mpr hclass))⟩

/-- Moving the condition, diagram, name and label together preserves the
literal graph predicate. The change of Cohen computation is essential. -/
theorem graphWitness_move (g : Vertex.RootGroup q) {p : Poset M I κ} {x y : (S).Name}
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    GraphWitness hμ c hcard hsize hmerger hj H E hE ((S).move g.val p) (g • x) (g • y) := by
  obtain ⟨d,w,j,τ,hp,ha,hx,hy⟩ := h
  refine ⟨g • d,g • w,g • j,τ.transport hμ g.val,?_,
    assigned_permute hμ c hcard hsize hmerger hj H E hE g ha,?_,?_⟩
  · change (S).move g.val p ≤ ((d.permute g.val,w.diagram.permute g.val) : Poset M I κ)
    simpa only [move_coe,permute] using ((S).move g.val).monotone hp
  · change (S).atomic.EqF ((S).move g.val p) (g.val • x) (label hμ c (g.val j))
    simpa only [smul_label] using ((S).eq_symmetry g.val p x (label hμ c j)).mp hx
  · exact ((S).eq_symmetry g.val p y τ.name).mp hy

theorem graphRelation_move (g : Equiv.Perm I) (hg : g ∈ SupportFilter.Fix q.range)
    (p : Poset M I κ) (x y : (S).Name)
    (h : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x y) :
    (graphRelation hμ c hcard hsize hmerger hj H E hE).holds ((S).move g p) (g • x) (g • y) := by
  intro r hr
  obtain ⟨s,hs,hw⟩ := h (((S).move g).symm r) (((S).move g).symm_apply_le.mpr hr)
  exact ⟨(S).move g s,((S).move g).le_symm_apply.mp hs,
    graphWitness_move hμ c hcard hsize hmerger hj H E hE ⟨g,hg⟩ hw⟩

/-- The collected graph is a set-sized HS name with the single support D_q. -/
def assignmentGraph : (S).Name :=
  (graphRelation hμ c hcard hsize hmerger hj H E hE).graph
    (labelSet hμ c) (quotientName hμ c E) (SupportFilter.Fix q.range)
    (localList_support hμ hcard q) (fun g _ => smul_labelSet hμ c g)
    (fun g hg => quotientName_fixed hμ c E g (hE g hg))
    (graphRelation_move hμ c hcard hsize hmerger hj H E hE)

/-- Single-valuedness is proved at common extensions of actual diagram
entries; no common preassigned component is assumed. -/
theorem graphRelation_one [Uncountable κ] (hc : Function.Injective c)
    {p : Poset M I κ} {x y z : (S).Name}
    (h : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x y)
    (h' : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x z) :
    (S).atomic.EqF p y z := by
  let : Nonempty (Diagram M I) := ⟨q⟩
  apply (S).atomic_regular.1
  intro r hr
  obtain ⟨s,hs,d,w,j,τ,hsp,ha,hxj,hyτ⟩ := h r hr
  obtain ⟨t,ht,e,v,k,σ,htp,hb,hxk,hzσ⟩ := h' s (hs.trans hr)
  obtain ⟨a,hat⟩ := exists_condition_below t
  have haj := WithTop.coe_le_coe.mp (hat.trans (ht.trans hsp))
  have hak := WithTop.coe_le_coe.mp (hat.trans htp)
  have hjk : j = k := by
    by_contra hn
    exact label_not_equal hμ c hc hn (a : Poset M I κ)
      ((S).atomic.eq_trans ((S).atomic.eq_symm ((S).atomic.eq_mono (hat.trans ht) hxj))
        ((S).atomic.eq_mono hat hxk))
  subst k
  have heq := assigned_compatible_one hμ c hcard hsize hmerger hj H E hE ha hb
    haj.1 hak.1 a.2 haj.2 hak.2
  exact ⟨a,(hat.trans ht).trans hs,(S).atomic.eq_trans
    ((S).atomic.eq_mono (hat.trans ht) hyτ)
    ((S).atomic.eq_trans heq ((S).atomic.eq_symm ((S).atomic.eq_mono hat hzσ)))⟩

/-- Equal graph values have equal labels, even before the cardinality
conditions used to prove totality have been imposed. -/
theorem graphRelation_inj {p : Poset M I κ} {x y z : (S).Name}
    (h : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x z)
    (h' : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p y z) :
    (S).atomic.EqF p x y := by
  let : Nonempty (Diagram M I) := ⟨q⟩
  apply (S).atomic_regular.1
  intro r hr
  obtain ⟨s,hs,d,w,j,τ,hsp,ha,hxj,hzτ⟩ := h r hr
  obtain ⟨t,ht,e,v,k,σ,htp,hb,hyk,hzσ⟩ := h' s (hs.trans hr)
  obtain ⟨a,hat⟩ := exists_condition_below t
  have haj := WithTop.coe_le_coe.mp (hat.trans (ht.trans hsp))
  have hak := WithTop.coe_le_coe.mp (hat.trans htp)
  have heq := (S).atomic.eq_trans
    ((S).atomic.eq_symm ((S).atomic.eq_mono (hat.trans ht) hzτ)) ((S).atomic.eq_mono hat hzσ)
  have hjk := assigned_compatible_inj hμ c hcard hsize hmerger hj H E hE ha hb
    haj.1 hak.1 a.2 haj.2 hak.2 heq
  subst k
  exact ⟨a,(hat.trans ht).trans hs,(S).atomic.eq_trans
    ((S).atomic.eq_mono (hat.trans ht) hxj) ((S).atomic.eq_symm ((S).atomic.eq_mono hat hyk))⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## GraphDensity -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
variable (e₀ : M)
variable (hcomp : Cardinal.mk ((Set.range (fun x : M => e₀*x))ᶜ : Set M) = Cardinal.mk M)
variable (d₀ : CohenForcing.Condition I κ)
variable (hsel : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ e : CohenForcing.Condition I κ,
  ∃ f, f ≤ e ∧ ((Vertex.orbitChain hj H a).tailData hj).Good f)
variable (hcount : ∀ d : CohenForcing.Condition I κ, d ≤ d₀ →
  ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ g : Vertex.RootGroup q,
    OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) (g • d))

include e₀ hcomp hsel hcount

/-- All label coordinates can be covered by strengthened diagrams. Thus
dense local totality gives totality of the one actual graph. -/
theorem graphRelation_total (x : (S).Name) (p : Poset M I κ)
    (hp : p ≤ (d₀,q)) (hx : (S).atomic.MemF p x (labelSet hμ c)) :
    ∀ r, r ≤ p → ∃ s, s ≤ r ∧ ∃ y : (S).Name,
      (S).atomic.MemF s y (quotientName hμ c E) ∧
      (graphRelation hμ c hcard hsize hmerger hj H E hE).holds s x y := by
  intro r hr
  obtain ⟨s,hs,j,hxj⟩ := (mem_labelSet hμ c x p).mp hx r hr
  let : Nonempty (Diagram M I) := ⟨q⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  have ha := WithTop.coe_le_coe.mp ((has.trans hs).trans (hr.trans hp))
  have hsizej : Cardinal.mk ({j} : Set I) ≤ Cardinal.mk M := by
    simpa only [Cardinal.mk_singleton] using
      Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk M)
  obtain ⟨t,hta,hjt⟩ := Diagram.extend_through hsize e₀ hcomp a.2 hsizej
  have ht : t ≤ a.2 := ⟨e₀,hta⟩
  obtain ⟨b,hb⟩ := ht.trans ha.2
  let w := labelVertex t b hb j (hjt (Set.mem_singleton j))
  obtain ⟨d,hda,τ,hA⟩ := assigned_total hμ c hcard hsize hmerger hj H E hE a.1 hsel
    (hcount a.1 ha.1) w j (labelVertex_mem t b hb j (hjt (Set.mem_singleton j)))
  have hds : ((d,t) : Poset M I κ) ≤ s := (WithTop.coe_le_coe.mpr (show (d,t) ≤ a from ⟨hda,ht⟩)).trans has
  have hw : GraphWitness hμ c hcard hsize hmerger hj H E hE (d,t) x τ.name :=
    ⟨d,w,j,τ,le_rfl,hA,(S).atomic.eq_mono hds hxj,(S).atomic.eq_refl _ _⟩
  exact ⟨(d,t),hds.trans hs,τ.name,
    (graphWitness_bounds hμ c hcard hsize hmerger hj H E hE hw).2,
    graphWitness_holds hμ c hcard hsize hmerger hj H E hE hw⟩

/-- Every actual quotient member is locally a canonical class of some label.
After placing that label in a diagram and stabilizing availability, the
onto assertion for its exact fiber supplies a graph preimage. -/
theorem graphRelation_onto (y : (S).Name) (p : Poset M I κ)
    (hp : p ≤ (d₀,q)) (hy : (S).atomic.MemF p y (quotientName hμ c E)) :
    ∀ r, r ≤ p → ∃ s, s ≤ r ∧ ∃ x : (S).Name,
      (S).atomic.MemF s x (labelSet hμ c) ∧
      (graphRelation hμ c hcard hsize hmerger hj H E hE).holds s x y := by
  intro r hr
  obtain ⟨s,hs,j,hyj⟩ := (mem_quotientName hμ c E y p).mp hy r hr
  let : Nonempty (Diagram M I) := ⟨q⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  have ha := WithTop.coe_le_coe.mp ((has.trans hs).trans (hr.trans hp))
  have hsizej : Cardinal.mk ({j} : Set I) ≤ Cardinal.mk M := by
    simpa only [Cardinal.mk_singleton] using
      Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk M)
  obtain ⟨t,hta,hjt⟩ := Diagram.extend_through hsize e₀ hcomp a.2 hsizej
  have ht : t ≤ a.2 := ⟨e₀,hta⟩
  obtain ⟨b,hb⟩ := ht.trans ha.2
  have hEt := supported_mono hμ (ht.trans ha.2) E hE
  let τ := localLabelClass hμ c t E hEt j (hjt (Set.mem_singleton j))
  obtain ⟨d,hda,hstable⟩ := forcedAvailability_dense_stable hμ c hcard hsize hmerger H hj
    a.1 t b τ
  let w : Vertex q := ⟨t,b,hb,forcedAvailability hμ c hcard hsize hmerger d t b τ⟩
  have hτ : StableAt hμ c hcard hsize hmerger E d w τ.name :=
    ⟨τ,rfl,forces_localLabelClass_isClass hμ c t E hEt j (hjt (Set.mem_singleton j)) (d,t),hstable⟩
  obtain ⟨f,hfd,k,hA⟩ := assigned_onto hμ c hcard hsize hmerger hj H E hE d hsel
    (hcount d (hda.trans ha.1)) w τ.name hτ
  have hfs : ((f,t) : Poset M I κ) ≤ s :=
    (WithTop.coe_le_coe.mpr (show (f,t) ≤ a from ⟨hfd.trans hda,ht⟩)).trans has
  have hw : GraphWitness hμ c hcard hsize hmerger hj H E hE (f,t) (label hμ c k) y :=
    ⟨f,w,k,τ,le_rfl,hA,(S).atomic.eq_refl _ _,(S).atomic.eq_mono hfs hyj⟩
  exact ⟨(f,t),hfs.trans hs,label hμ c k,label_mem_labelSet hμ c k ((f,t) : Poset M I κ),
    graphWitness_holds hμ c hcard hsize hmerger hj H E hE hw⟩

/-- Under the explicitly stated dense count and selector facts the actual
HS graph is a bijection. These facts are discharged for the concrete monoid
and forcing in the construction, rather than being model axioms. -/
theorem assignmentGraph_bijection [Uncountable κ] (hc : Function.Injective c) :
    (S).Forces ![assignmentGraph hμ c hcard hsize hmerger hj H E hE,
      labelSet hμ c,quotientName hμ c E] ((d₀,q) : Poset M I κ)
      ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  apply And.intro
  · apply (graphRelation hμ c hcard hsize hmerger hj H E hE).graph_surjection
    · exact graphRelation_total hμ c hcard hsize hmerger hj H E hE e₀ hcomp d₀ hsel hcount
    · intro p _ x y z
      exact graphRelation_one hμ c hcard hsize hmerger hj H E hE hc
    · exact graphRelation_onto hμ c hcard hsize hmerger hj H E hE e₀ hcomp d₀ hsel hcount
  · apply (graphRelation hμ c hcard hsize hmerger hj H E hE).graph_injection
    · exact graphRelation_total hμ c hcard hsize hmerger hj H E hE e₀ hcomp d₀ hsel hcount
    · intro p _ x y z
      exact graphRelation_one hμ c hcard hsize hmerger hj H E hE hc
    · intro p _ x y z
      exact graphRelation_inj hμ c hcard hsize hmerger hj H E hE

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## CountableHull -/

/-! Small hulls for countably-ary operations, used for the chain condition of
countable Cohen forcing. The construction is a genuine well-founded term
algebra; no elementary-submodel or large-cardinal assumption is needed. -/
namespace PartitionConsistency.CountableHull
universe u
noncomputable section
open scoped Classical
variable {A X : Type u}

private def Arity : Option A → Type u
  | none => PEmpty
  | some _ => ULift.{u} ℕ

private def evaluate (base : X) (op : A → (ℕ → X) → X) : WType (@Arity A) → X :=
  WType.elim _ (fun ⟨a,args⟩ => match a with
    | none => base
    | some a => op a (fun n => args ⟨n⟩))

/-- Closure under any small family of countably-ary operations has size at
most a fixed point of countable exponentiation. -/
theorem exists_closed {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpower : μ ^ Cardinal.aleph0 = μ) (hA : Cardinal.mk A ≤ μ)
    (base : X) (op : A → (ℕ → X) → X) :
    ∃ S : Set X, Cardinal.mk S ≤ μ ∧ base ∈ S ∧
      ∀ a f, (∀ n, f n ∈ S) → op a f ∈ S := by
  have hlabels : Cardinal.mk (Option A) ≤ μ := by
    simpa only [Cardinal.mk_option] using
      (add_le_add hA (Cardinal.one_le_aleph0.trans hω)).trans_eq (Cardinal.add_eq_self hω)
  have harity (a : Option A) : Cardinal.mk (Arity a) ≤ Cardinal.aleph0 := by
    cases a <;> simp [Arity]
  have htree : Cardinal.mk (WType (@Arity A)) ≤ μ := by
    apply WType.cardinalMk_le_of_le
    calc
      Cardinal.sum (fun a : Option A => μ ^ Cardinal.mk (Arity a)) ≤
          Cardinal.sum (fun _ : Option A => μ) := by
        apply Cardinal.sum_le_sum
        intro a
        exact (Cardinal.power_le_power_left (ne_of_gt (Cardinal.aleph0_pos.trans_le hω)) (harity a)).trans_eq hpower
      _ = Cardinal.mk (Option A) * μ := by simp
      _ ≤ μ * μ := mul_le_mul' hlabels le_rfl
      _ = μ := Cardinal.mul_eq_self hω
  refine ⟨Set.range (evaluate base op),?_,?_,?_⟩
  · exact Cardinal.mk_range_le.trans htree
  · exact ⟨WType.mk none PEmpty.elim,rfl⟩
  · intro a f hf
    choose t ht using hf
    exact ⟨WType.mk (some a) (fun n => t n.down),by
      change op a (fun n => evaluate base op (t n)) = op a f
      exact congrArg (op a) (funext ht)⟩

end
end PartitionConsistency.CountableHull


/-! ## CohenChain -/

/-! Chain condition for the actual countable Cohen conditions. The small
hull is a well-founded term algebra, so this proof adds no hypothesis about
an elementary submodel or a delta-system. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

private theorem exists_code (d : Condition I κ) :
    ∃ f : ℕ → Option ((I × κ) × Bool),
      Set.range f = Set.insert none (Option.some '' d.graph) := by
  obtain ⟨f,hf⟩ := ((d.countable_graph.image Option.some).insert none).exists_eq_range
    (Set.insert_nonempty _ _)
  exact ⟨f,hf.symm⟩

private def code (d : Condition I κ) : ℕ → Option ((I × κ) × Bool) :=
  (exists_code d).choose

private theorem code_range (d : Condition I κ) :
    Set.range (code d) = Set.insert none (Option.some '' d.graph) :=
  (exists_code d).choose_spec

private theorem enriched_graph_injective : Function.Injective
    (fun d : Condition I κ => Set.insert none (Option.some '' d.graph)) := by
  intro d e h
  apply ext
  ext z
  have hz := Set.ext_iff.mp h (some z)
  change (some z = none ∨ ∃ x ∈ d.graph, some x = some z) ↔
    (some z = none ∨ ∃ x ∈ e.graph, some x = some z) at hz
  simpa only [Option.some_ne_none,Option.some.injEq,exists_eq_right,false_or] using hz

private theorem code_injective : Function.Injective (code (I := I) (κ := κ)) := by
  intro d e h
  apply enriched_graph_injective
  dsimp only
  rw [← code_range,← code_range,h]

private def decode (f : ℕ → Option ((I × κ) × Bool)) : Condition I κ :=
  if h : ∃ d : Condition I κ, Set.range f = Set.insert none (Option.some '' d.graph)
    then h.choose else ⊤

private theorem decode_code (d : Condition I κ) : decode (code d) = d := by
  have h : ∃ e : Condition I κ,
      Set.range (code d) = Set.insert none (Option.some '' e.graph) := ⟨d,code_range d⟩
  rw [decode,dite_eq_left h]
  exact enriched_graph_injective (h.choose_spec.symm.trans (code_range d))

private def compatibleChoice (A : Set (Condition I κ)) (d : Condition I κ) : Condition I κ :=
  if h : ∃ e ∈ A, Compatible d e then h.choose else ⊤

private theorem compatibleChoice_spec (A : Set (Condition I κ)) (d : Condition I κ)
    (h : ∃ e ∈ A, Compatible d e) :
    compatibleChoice A d ∈ A ∧ Compatible d (compatibleChoice A d) := by
  rw [compatibleChoice,dite_eq_left h]
  exact h.choose_spec

private def flip : Option ((I × κ) × Bool) → Option ((I × κ) × Bool)
  | none => none
  | some (a,b) => some (a,!b)

private def restrictedGraph (p : Condition I κ) (S : Set (Option ((I × κ) × Bool))) :
    Condition I κ where
  graph := {z | z ∈ p.graph ∧ some z ∈ S}
  functional a b c hb hc := p.functional a b c hb.1 hc.1
  countable_graph := p.countable_graph.mono (fun _ h => h.1)

/-- Every pairwise incompatible set of countable binary conditions has size
at most any infinite fixed point of countable exponentiation. In particular
the forcing is `(2^ℵ₀)⁺`-c.c., irrespective of its coordinate set. -/
theorem antichain_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpower : μ ^ Cardinal.aleph0 = μ) (A : Set (Condition I κ))
    (hA : ∀ p ∈ A, ∀ q ∈ A, Compatible p q → p = q) : Cardinal.mk A ≤ μ := by
  let op (a : ULift.{u} (Bool × ℕ)) (f : ℕ → Option ((I × κ) × Bool)) :=
    if a.down.1 then code (compatibleChoice A (decode f)) a.down.2 else flip (f a.down.2)
  have hops : Cardinal.mk (ULift.{u} (Bool × ℕ)) ≤ μ := by
    simpa only [Cardinal.mk_uLift,Cardinal.mk_prod,Cardinal.mk_bool,Cardinal.mk_nat,
      Cardinal.lift_aleph0,Cardinal.lift_id,Cardinal.ofNat_mul_aleph0] using hω
  obtain ⟨S,hS,hnone,hclosed⟩ :=
    CountableHull.exists_closed hω hpower hops (none : Option ((I × κ) × Bool)) op
  have hflip (z : Option ((I × κ) × Bool)) (hz : z ∈ S) : flip z ∈ S :=
    hclosed ⟨(false,0)⟩ (fun _ => z) (fun _ => hz)
  have hbits (a : I × κ) (b c : Bool) (h : some (a,b) ∈ S) : some (a,c) ∈ S := by
    cases b <;> cases c
    · exact h
    · exact hflip _ h
    · exact hflip _ h
    · exact h
  have hcode {d : Condition I κ} (hs : ∀ z ∈ d.graph, some z ∈ S) :
      ∀ n, code d n ∈ S := by
    intro n
    have hn := Set.range_subset_iff.mp (show Set.range (code d) ⊆ S by
      rw [code_range]
      exact Set.insert_subset hnone (by rintro _ ⟨z,hz,rfl⟩; exact hs z hz)) n
    exact hn
  have hin (p : Condition I κ) (hp : p ∈ A) : ∀ z ∈ p.graph, some z ∈ S := by
    let d := restrictedGraph p S
    have hd : Compatible d p := fun a b c hb hc => p.functional a b c hb.1 hc
    have hb := compatibleChoice_spec A d ⟨p,hp,hd⟩
    let b := compatibleChoice A d
    have hbS (n : ℕ) : code b n ∈ S := by
      have hh := hclosed ⟨(true,n)⟩ (code d) (hcode (fun z hz => hz.2))
      simpa [op,decode_code,b] using hh
    have hbgraph (z : (I × κ) × Bool) (hz : z ∈ b.graph) : some z ∈ S := by
      have hr : some z ∈ Set.range (code b) := by
        rw [code_range]
        exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hz)
      obtain ⟨n,hn⟩ := hr
      exact hn ▸ hbS n
    have hbp : Compatible p b := by
      intro a x y hx hy
      apply hb.2 a x y ⟨hx,?_⟩ hy
      exact hbits a y x (hbgraph _ hy)
    have he : p = b := hA p hp b hb.1 hbp
    exact he ▸ hbgraph
  let pack (p : A) : ℕ → S := fun n => ⟨code p.val n,hcode (hin p.val p.property) n⟩
  have hpack : Function.Injective pack := by
    intro p q h
    apply Subtype.ext
    apply code_injective
    exact funext (fun n => congrArg Subtype.val (congrFun h n))
  calc
    Cardinal.mk A ≤ Cardinal.mk (ℕ → S) := Cardinal.mk_le_of_injective hpack
    _ = Cardinal.mk S ^ Cardinal.aleph0 := by simp
    _ ≤ μ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hS
    _ = μ := hpower

/-- The source chain condition, with its precise successor-continuum bound. -/
theorem antichain_continuum (A : Set (Condition I κ))
    (hA : ∀ p ∈ A, ∀ q ∈ A, Compatible p q → p = q) :
    Cardinal.mk A ≤ Cardinal.continuum :=
  antichain_cardinal_le Cardinal.aleph0_le_continuum Cardinal.continuum_power_aleph0 A hA

end
end PartitionConsistency.CohenForcing.Condition


/-! ## ChainPreservation -/

/-! Cardinal preservation from the actual chain condition. The statements
below concern the internal set-graph surjection sentence and arbitrary name
ranks. No existence of an ambient fully generic filter is used. -/
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v
noncomputable section
open ForcingQuotient
variable {P : Type u} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- A chain bound on the concrete forcing order. Compatibility here means
existence of a common stronger condition, not agreement of two names. -/
def ChainBound (ν : Cardinal.{u}) : Prop :=
  ∀ A : Set P, (∀ p ∈ A, ∀ q ∈ A, Compatible p q → p = q) → Cardinal.mk A ≤ ν

omit [OrderTop P] in
/-- A separating family of conditions injects into an antichain. -/
theorem ChainBound.cardinal_le {ν : Cardinal.{u}} (hcc : ChainBound (P := P) ν)
    {X : Type u} (c : X → P)
    (hc : ∀ x y, Compatible (c x) (c y) → x = y) : Cardinal.mk X ≤ ν := by
  have hinj : Function.Injective c := by
    intro x y he
    exact hc x y ⟨c x,le_rfl,he ▸ le_rfl⟩
  let pack : X → Set.range c := fun x => ⟨c x,⟨x,rfl⟩⟩
  have hp : Function.Injective pack := fun x y he => hinj (congrArg Subtype.val he)
  apply (Cardinal.mk_le_of_injective hp).trans
  exact hcc _ (by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ h
    exact congrArg c (hc x y h))

omit [OrderTop P] in
/-- Counting an indexed relation whose witnesses with compatible conditions
and equal records must have the same value. -/
theorem ChainBound.cardinal_le_mul {ν : Cardinal.{u}} (hcc : ChainBound (P := P) ν)
    {A B : Type u} (R : P → A → B → Prop)
    (total : ∀ b, ∃ a p, R p a b)
    (single : ∀ a b b' p q, R p a b → R q a b' → Compatible p q → b = b') :
    Cardinal.mk B ≤ Cardinal.mk A * ν := by
  let V (a : A) := {b : B // ∃ p, R p a b}
  have hV (a : A) : Cardinal.mk (V a) ≤ ν := by
    let c : V a → P := fun b => b.property.choose
    apply hcc.cardinal_le c
    intro b b' hc
    apply Subtype.ext
    exact single a b.val b'.val (c b) (c b') b.property.choose_spec b'.property.choose_spec hc
  let pack : B → Σ a : A, V a := fun b => ⟨(total b).choose,⟨b,(total b).choose_spec⟩⟩
  have hi : Function.Injective pack := by
    intro b b' he
    exact congrArg (fun t : Σ a : A, V a => t.2.val) he
  calc
    Cardinal.mk B ≤ Cardinal.mk (Σ a : A, V a) := Cardinal.mk_le_of_injective hi
    _ = Cardinal.sum (fun a : A => Cardinal.mk (V a)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : A => ν) := Cardinal.sum_le_sum _ _ hV
    _ = Cardinal.mk A * ν := by simp

/-- For a fixed ground argument of an internal function, the possible
values which belong to a ground set form a set of size at most the chain
bound. Only the actual function-on formula supplies single-valuedness. -/
theorem possibleValues_cardinal_le {A B : Type u}
    (a : A → ZFSet.{u}) (b : B → ZFSet.{u}) (hb : Function.Injective b)
    (f : S.Name) (p : P)
    (hf : S.Forces ![f,Name.check (ZFSet.range a)] p (SetLanguage.functionOn 0 1))
    {ν : Cardinal.{u}} (hcc : ChainBound (P := P) ν) (i : A) :
    Cardinal.mk {j : B // ∃ q, q ≤ p ∧
      S.App q f (Name.check (a i)) (Name.check (b j))} ≤ ν := by
  classical
  let V := {j : B // ∃ q, q ≤ p ∧ S.App q f (Name.check (a i)) (Name.check (b j))}
  let cond : V → P := fun j => j.property.choose
  have hcond (j : V) : cond j ≤ p ∧ S.App (cond j) f (Name.check (a i)) (Name.check (b j.val)) :=
    j.property.choose_spec
  have separate (j k : V) (h : Compatible (cond j) (cond k)) : j = k := by
    obtain ⟨r,hrj,hrk⟩ := h
    apply Subtype.ext
    apply hb
    apply (S.eq_check_iff (b j.val) (b k.val) r).mp
    exact S.functionOn_unique ![f,Name.check (ZFSet.range a)] r 0 1
      (S.atomic.forceFormula_mono (hrj.trans (hcond j).1) hf)
      (Name.check (a i)) (Name.check (b j.val)) (Name.check (b k.val))
      (S.check_mem_of_mem (ZFSet.mem_range.mpr ⟨i,rfl⟩) r)
      (S.app_mono hrj (hcond j).2) (S.app_mono hrk (hcond k).2)
  exact hcc.cardinal_le cond separate

/-- A forced surjection between two ground sets bounds the ground size of
the codomain by the domain size times the forcing's chain bound. This is the
possible-values proof of cardinal preservation, with no cardinal-preservation
premise hidden in the definition of a forcing extension. -/
theorem cardinal_le_of_forces_surjection {A B : Type u}
    (a : A → ZFSet.{u}) (b : B → ZFSet.{u}) (hb : Function.Injective b)
    (f : S.Name) (p : P)
    (hf : S.Forces ![f,Name.check (ZFSet.range a),Name.check (ZFSet.range b)] p
      (SetLanguage.surjection 0 1 2))
    {ν : Cardinal.{u}} (hcc : ChainBound (P := P) ν) :
    Cardinal.mk B ≤ Cardinal.mk A * ν := by
  have hsur := (S.forces_surjection _ p 0 1 2).mp hf
  have hfun := ((S.forces_mapsTo _ p 0 1 2).mp hsur.1).1
  have hex (j : B) : ∃ i : A, ∃ q, q ≤ p ∧
      S.App q f (Name.check (a i)) (Name.check (b j)) := by
    obtain ⟨q,hqp,x,hx,he⟩ := hsur.2 (Name.check (b j)) p le_rfl
      (S.check_mem_of_mem (ZFSet.mem_range.mpr ⟨j,rfl⟩) p) p le_rfl
    obtain ⟨r,hrq,z,hz,hxz⟩ := (S.mem_check (ZFSet.range a) x q).mp hx q le_rfl
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨i,r,hrq.trans hqp,
      (S.app_congr (S.atomic.eq_refl r f) hxz (S.atomic.eq_refl r (Name.check (b j)))).mp
        (S.app_mono hrq he)⟩
  let V (i : A) := {j : B // ∃ q, q ≤ p ∧ S.App q f (Name.check (a i)) (Name.check (b j))}
  let pack : B → Σ i : A, V i := fun j => ⟨(hex j).choose,⟨j,(hex j).choose_spec⟩⟩
  have hinj : Function.Injective pack := by
    intro j k he
    exact congrArg (fun t : Σ i : A, V i => t.2.val) he
  calc
    Cardinal.mk B ≤ Cardinal.mk (Σ i : A, V i) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.sum (fun i : A => Cardinal.mk (V i)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : A => ν) := Cardinal.sum_le_sum _ _
      (fun i => S.possibleValues_cardinal_le a b hb f p hfun hcc i)
    _ = Cardinal.mk A * ν := by simp

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
