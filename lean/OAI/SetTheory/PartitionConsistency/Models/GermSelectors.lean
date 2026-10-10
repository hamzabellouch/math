import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.QuotientActions

namespace OAI

/-! ## PreAssignment -/

/-! The preliminary component assignment, as a persistent relation on actual
forcing conditions and actual HS names. The ordinal table is fixed once,
and the names for ranks/order types are computed from the persistent least
codes rather than from arbitrary principal-filter wellorders. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "ordT" => ordinalType hμ c hcard hsize hmerger hj E hE C
local notation "ordR" => ordinalRank hμ c hcard hsize hmerger hj E hE C
local notation "Sel" => IsSelected hμ c hcard hsize hmerger hj E hE C
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

/-- The bounded ground table depends on the component's fixed coding data,
never on a condition or a moved generic computation. -/
def ordinalTable : OrderAssignment.Table (labelFiberSet v) (ordT).raw.rank :=
  OrderAssignment.chooseTable _ _

/-- `j` is assigned to the class named by `τ` at the local vertex `w`.
Both ordinal values in this definition are forced values of actual names. -/
def Preliminary (d : CohenForcing.Condition I κ) (w : Vertex q)
    (j : labelFiberSet v) (τ : (S).Name) : Prop :=
  ∃ (θ : Ordinal.{u}) (hb : θ ≤ (ordT).raw.rank)
    (hc : θ.card = Cardinal.mk (labelFiberSet v)) (a : Index hμ c C),
    Sel a d ∧ (S).atomic.EqF ((d,v.diagram) : Poset M I κ) ordT (Name.check θ.toZFSet) ∧
    (S).atomic.EqF ((d,v.diagram) : Poset M I κ) (ordR a)
      (Name.check (OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C)
        θ hb hc j).val.toZFSet) ∧ Links hμ c C d w τ (code hμ c C a)

variable {hμ c hcard hsize hmerger hj E hE C}

theorem preliminary_mono {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name} (hed : e ≤ d)
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  have hh : ((e,v.diagram) : Poset M I κ) ≤ (d,v.diagram) :=
    WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩
  exact ⟨θ,hb,hc,a,isSelected_mono hμ c hcard hsize hmerger hj E hE C hed ha,
    (S).atomic.eq_mono hh ht,(S).atomic.eq_mono hh hr,links_mono hed hl⟩

theorem preliminary_common {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ) : Vertex.Common v w := by
  obtain ⟨_,_,_,_,_,_,_,hl⟩ := h
  exact links_common hl

theorem preliminary_congr {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ σ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ)
    (he : (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C d w j σ := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  exact ⟨θ,hb,hc,a,ha,ht,hr,links_congr hl he⟩

omit [Infinite M] [Infinite I] in
/-- This equality concerns actual forced ordinal values. It is independent
of the enumeration's arbitrary but once-for-all ground choices. -/
private theorem ordinal_value_unique (d : CohenForcing.Condition I κ) (τ : (S).Name)
    {θ ψ : Ordinal.{u}}
    (hθ : (S).atomic.EqF ((d,v.diagram) : Poset M I κ) τ (Name.check θ.toZFSet))
    (hψ : (S).atomic.EqF ((d,v.diagram) : Poset M I κ) τ (Name.check ψ.toZFSet)) : θ = ψ := by
  apply Ordinal.toZFSet_injective
  exact ((S).eq_check_iff _ _ ((d,v.diagram) : Poset M I κ)).mp
    ((S).atomic.eq_trans ((S).atomic.eq_symm hθ) hψ)

/-- Injectivity and single-valuedness together: two assigned values are
forced equal at the local vertex if and only if their ground labels agree. -/
theorem preliminary_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j k : labelFiberSet v} {τ σ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ)
    (h' : Preliminary hμ c hcard hsize hmerger hj E hE C d w k σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = k := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  obtain ⟨ψ,hb',hc',b,hbsel,ht',hr',hl'⟩ := h'
  have heθ := ordinal_value_unique d ordT ht ht'
  subst ψ
  constructor
  · intro he
    have hs := (links_eq_iff_same hsize hmerger hl hl').mp he
    have hab : a = b := (code hμ c C).injective
      (selected_unique hμ c hcard hsize hmerger hj E hE C ha hbsel hs)
    subst b
    have hij := ordinal_value_unique d (ordR a) hr hr'
    exact (OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C)
      θ hb hc).injective (Subtype.ext hij)
  · rintro rfl
    have heq : (S).atomic.EqF ((d,v.diagram) : Poset M I κ) (ordR a) (ordR b) :=
      (S).atomic.eq_trans hr ((S).atomic.eq_symm hr')
    have hab := (ordinalRank_eq_iff hμ c hcard hsize hmerger hj E hE C a b d ha hbsel).mp heq
    subst b
    exact (links_eq_iff_same hsize hmerger hl hl').mpr (same_refl d _)

variable (hμ c hcard hsize hmerger hj E hE C)

/-- Every assigned local representative is eligible and keeps exactly the
vertex's availability ideal at every stronger Cohen condition. -/
theorem preliminary_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : LocalName hμ c w.diagram}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    (S).Forces ![τ.name,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)
      (SetLanguage.isClass 0 1 2) ∧
    ∀ e, e ≤ d → forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index τ = w.ideal := by
  obtain ⟨_,_,_,a,ha,_,_,hl⟩ := h
  exact links_stable hμ c hcard hsize hmerger hj E hE C d (code hμ c C a) ha.1 w τ hl

/-- Restrictions are the canonical identifications in the component. -/
theorem preliminary_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : labelFiberSet v} {τ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d z j τ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  exact ⟨θ,hb,hc,a,ha,ht,hr,links_restrict hμ c C d f τ _ hl⟩

/-- Local decision gives the converse when the representative is supported
on the successor diagram. -/
theorem preliminary_descend {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : labelFiberSet v} {τ : LocalName hμ c z.diagram}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    Preliminary hμ c hcard hsize hmerger hj E hE C d z j τ.name := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  exact ⟨θ,hb,hc,a,ha,ht,hr,links_descend hμ c hsize hmerger hj C d f τ _ hl⟩

/-- The equation for every member of the tail group, including its moved
Cohen condition and moved vertex. Ground code order is unchanged. -/
theorem preliminary_permute (g : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (w : Vertex q) (j : labelFiberSet v) (τ : (S).Name)
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C (d.permute g.val.val.val)
      (g.val.val • w) j (g.val.val.val • τ) := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  have hg : g.val.val.val ∈ tailGroup hj C := (tailGroup_mem hj C _).mpr ⟨g,rfl⟩
  refine ⟨θ,hb,hc,a,isSelected_covariance hμ c hcard hsize hmerger hj E hE C _ hg a d ha,?_,?_,
    links_permute hμ c hj C g d w τ _ hl⟩
  · exact tail_eq_permute hμ c hsize hmerger hj C g d _ _
      (ordinalType_fixed hμ c hcard hsize hmerger hj E hE C)
      (fun π _ => Name.smul_check S π _) ht
  · exact tail_eq_permute hμ c hsize hmerger hj C g d _ _
      (ordinalRank_fixed hμ c hcard hsize hmerger hj E hE C a)
      (fun π _ => Name.smul_check S π _) hr

/-- The exact cardinal-count hypothesis used by the two density proofs.
It is a theorem for the concrete system (not a construction premise). -/
def OrdinalCount (d : CohenForcing.Condition I κ) : Prop :=
  ∀ e, e ≤ d → ∀ θ : Ordinal.{u},
    (S).atomic.EqF ((e,v.diagram) : Poset M I κ) ordT (Name.check θ.toZFSet) →
      θ.card = Cardinal.mk (labelFiberSet v)

/-- Dense totality at an arbitrary vertex of the component. -/
theorem preliminary_total (d : CohenForcing.Condition I κ)
    (hcount : OrdinalCount hμ c hcard hsize hmerger hj E hE C d)
    (w : Vertex q) (hw : Vertex.Common v w) (j : labelFiberSet v) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      Preliminary hμ c hcard hsize hmerger hj E hE C e w j τ.name := by
  obtain ⟨e,hed,θ,hb,ht⟩ := ordinalType_decide hμ c hcard hsize hmerger hj E hE C d
  have hc := hcount e hed θ ht
  let β := OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C) θ hb hc j
  obtain ⟨f,hfe,a,ha,hr⟩ := member_ordinalRank hμ c hcard hsize hmerger hj E hE C e θ ht β
  obtain ⟨τ,hτ⟩ := working_linked hμ c hcard hsize hmerger hj E hE C f (code hμ c C a) ha.1 w hw
  refine ⟨f,hfe.trans hed,τ,θ,hb,hc,a,ha,?_,hr,hτ⟩
  exact (S).atomic.eq_mono (WithTop.coe_le_coe.mpr (show (f,v.diagram) ≤ (e,v.diagram) from
    ⟨hfe,le_rfl⟩)) ht

/-- Dense surjectivity onto every persistent linked class, before any
selector or coset representative is chosen. -/
theorem preliminary_onto (d : CohenForcing.Condition I κ)
    (hcount : OrdinalCount hμ c hcard hsize hmerger hj E hE C d)
    (w : Vertex q) (τ : (S).Name) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a)
    (hl : Links hμ c C d w τ a) :
    ∃ e, e ≤ d ∧ ∃ j : labelFiberSet v,
      Preliminary hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨e,hed,b,hb,hab⟩ := dense_selected hμ c hcard hsize hmerger hj E hE C d a ha
  let ib := (code hμ c C).symm b
  have hb' : Sel ib e := by simpa only [ib,Equiv.apply_symm_apply,IsSelected] using hb
  have hl' : Links hμ c C e w τ (code hμ c C ib) := by
    simpa only [ib,Equiv.apply_symm_apply] using links_same (links_mono hed hl) hab
  obtain ⟨f,hfe,θ,hθ,ht⟩ := ordinalType_decide hμ c hcard hsize hmerger hj E hE C e
  have hc := hcount f (hfe.trans hed) θ ht
  have hbf := isSelected_mono hμ c hcard hsize hmerger hj E hE C hfe hb'
  obtain ⟨g,hgf,β,hr⟩ := ordinalRank_decide hμ c hcard hsize hmerger hj E hE C ib f hbf θ ht
  let j := (OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C) θ hθ hc).symm β
  refine ⟨g,hgf.trans (hfe.trans hed),j,θ,hθ,hc,ib,
    isSelected_mono hμ c hcard hsize hmerger hj E hE C hgf hbf,?_,?_,
    links_mono (hgf.trans hfe) hl'⟩
  · exact (S).atomic.eq_mono (WithTop.coe_le_coe.mpr (show (g,v.diagram) ≤ (f,v.diagram) from
      ⟨hgf,le_rfl⟩)) ht
  · simpa only [j,Equiv.apply_symm_apply] using hr

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## Germ -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u t
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I} {v : Vertex q}
noncomputable section
variable (C : Chain v)

/-- The unique contraction from the initial vertex to a chain vertex. -/
def fromRoot (i : ℕ) : Arrow v (C.vertex i) := by
  simpa only [C.first] using (C.increasing 0 i (Nat.zero_le i)).some

def index (i : ℕ) : M := (C.fromRoot i).index

@[simp] theorem fromRoot_index (i : ℕ) : (C.fromRoot i).index = C.index i := rfl

theorem index_diagram (i : ℕ) : v.diagram.sub (C.index i) = (C.vertex i).diagram :=
  (C.fromRoot i).diagram

theorem index_transition (i j : ℕ) (f : Arrow (C.vertex i) (C.vertex j)) :
    C.index i * f.index = C.index j := by
  exact congrArg Arrow.index (Subsingleton.elim ((C.fromRoot i).comp f) (C.fromRoot j))

theorem index_zero : C.index 0 = 1 := by
  apply Diagram.index_unique (r := v.diagram)
  rw [C.index_diagram,C.first,Diagram.sub_one]

/-- These are the literal alignments of the moved chain with contractions
of its initial vertex. There is no replacement relation assumed here. -/
def Alignments (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) : Set (ℕ × M) :=
  {p | ∃ f : Arrow v (π.val • C.vertex p.1), f.index = p.2}

theorem alignments_nonempty (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) : (C.Alignments hj π).Nonempty := by
  have ht : Common v ((π⁻¹).val • v) := (π⁻¹).property
  obtain ⟨i,⟨f⟩⟩ := C.cofinal _ ht
  have g : Arrow v (π.val • C.vertex i) := by
    simpa only [Subgroup.coe_inv,smul_inv_smul] using f.move π.val
  exact ⟨(i,g.index),g,rfl⟩

/-- Each alignment index is bounded by an original chain index. -/
theorem alignment_bounded (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) {p : ℕ × M} (hp : p ∈ C.Alignments hj π) :
    ∃ N, p.2 ∣ C.index N := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨N,⟨g⟩⟩ := C.cofinal _ (Common.of_arrow f)
  have hh := congrArg Arrow.index (Subsingleton.elim (f.comp g) (C.fromRoot N))
  exact ⟨N,g.index,by simpa only [Arrow.comp,fromRoot_index,hf] using hh.symm⟩

/-- Arbitrary cofinal advances are admissible replacements in the precise
sense required by finite old-gate descent. -/
theorem alignment_replacement (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) {p : ℕ × M} (hp : p ∈ C.Alignments hj π) (N : ℕ) :
    ∃ l' d, (l',p.2*d) ∈ C.Alignments hj π ∧ p.1 ≤ l' ∧
      C.index p.1*d = C.index l' ∧ C.index N ∣ p.2*d := by
  obtain ⟨f,hf⟩ := hp
  have ht : Common v ((π⁻¹).val • C.vertex N) :=
    common_moved hj v (π⁻¹) (C.common N)
  obtain ⟨k,⟨g⟩⟩ := C.cofinal _ ht
  let l' := max p.1 k
  let d := (C.increasing p.1 l' (le_max_left _ _)).some
  let e := (C.increasing k l' (le_max_right _ _)).some
  have g' : Arrow (C.vertex N) (π.val • C.vertex l') := by
    simpa only [Subgroup.coe_inv,smul_inv_smul] using (g.comp e).move π.val
  let f' := f.comp (d.move π.val)
  refine ⟨l',d.index,⟨f',by change f.index*d.index = p.2*d.index; rw [hf]⟩,
    le_max_left _ _,C.index_transition _ _ d,g'.index,?_⟩
  have hh := congrArg Arrow.index (Subsingleton.elim ((C.fromRoot N).comp g') f')
  simpa only [Arrow.comp,Arrow.move,fromRoot_index,hf,f'] using hh.symm

/-- Having the same alignment identifies the two actual quotient cosets.
This is independent of any choice of a descent path. -/
theorem coset_eq_of_alignment (hj : HasConditionalJoins (LeftDivOrder M))
    (π σ : componentStabilizer hj v) {p : ℕ × M}
    (hπ : p ∈ C.Alignments hj π) (hσ : p ∈ C.Alignments hj σ) :
    (QuotientGroup.mk' (C.tailFixer hj) π) = QuotientGroup.mk' (C.tailFixer hj) σ := by
  apply QuotientGroup.eq.mpr
  obtain ⟨f,hf⟩ := hπ
  obtain ⟨g,hg⟩ := hσ
  refine ⟨p.1,?_⟩
  rintro j ⟨x,rfl⟩
  have hdiag : (C.vertex p.1).diagram.permute π.val.val =
      (C.vertex p.1).diagram.permute σ.val.val := by
    rw [← smul_diagram,← smul_diagram,← f.diagram,← g.diagram,hf,hg]
  have hh := congrArg (fun r : Diagram M I => r x) hdiag
  change π.val.val.symm (σ.val.val ((C.vertex p.1).diagram x)) = (C.vertex p.1).diagram x
  change π.val.val ((C.vertex p.1).diagram x) = σ.val.val ((C.vertex p.1).diagram x) at hh
  rw [← hh,Equiv.symm_apply_apply]

/-- Conditional use of the already proved finite gate descent. This is NOT
an existence theorem for the countable-base rearrangement: the tower `T`
and its base/terminal assertions are still explicit hypotheses. It shows
exactly how such a rearrangement would finish the countable-germs argument. -/
theorem countable_quotient_of_gateTower
    (hj : HasConditionalJoins (LeftDivOrder M)) (T : GateTower.{u,t} M)
    (hbase : (T.stage 0 : Set M).Countable)
    (hn : ∀ i, C.index i ∈ T.stage 0)
    (hq : ∀ i j d, C.index i*d = C.index j → d ∈ T.stage 0)
    (ω : Ordinal.{t}) (hω : T.stage ω = ⊤) :
    Countable (componentStabilizer hj v ⧸ C.tailFixer hj) := by
  have halign : ∀ π : componentStabilizer hj v,
      ∃ p : ℕ × T.stage 0, (p.1,p.2.val) ∈ C.Alignments hj π := by
    intro π
    obtain ⟨p,hp⟩ := C.alignments_nonempty hj π
    obtain ⟨a,ha,hmem,_⟩ := T.finite_descent_terminal (C.index) (C.Alignments hj π) hn hq
      (fun p hp => C.alignment_bounded hj π hp)
      (fun p hp N => C.alignment_replacement hj π hp N) ω hω p hp
    exact ⟨(a.1,⟨a.2,hmem⟩),ha⟩
  let chooseCode (c : componentStabilizer hj v ⧸ C.tailFixer hj) : ℕ × T.stage 0 :=
    (halign c.out).choose
  have hcode (c : componentStabilizer hj v ⧸ C.tailFixer hj) :
      ((chooseCode c).1,(chooseCode c).2.val) ∈ C.Alignments hj c.out :=
    (halign c.out).choose_spec
  have hinj : Function.Injective chooseCode := by
    intro c e he
    have hc := hcode c
    rw [he] at hc
    have hh := C.coset_eq_of_alignment hj c.out e.out hc (hcode e)
    simpa only [QuotientGroup.mk'_apply,Quotient.out_eq] using hh
  let : Countable (T.stage 0) := hbase.to_subtype
  exact hinj.countable

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain


/-! ## Selector -/

/-! A combinatorial coset-selector argument. The existence of a countable-base
tower and symmetric names for its assignments are established separately. -/

namespace PartitionConsistency.TailSelector
universe u v w
noncomputable section
open scoped Classical

/-- Equality after discarding a finite initial segment of a sequence. -/
def eventualSetoid (A : Type*) : Setoid (ℕ → A) where
  r f g := ∃ N, ∀ n, N ≤ n → f n = g n
  iseqv := ⟨fun _ => ⟨0,fun _ _ => rfl⟩,
    fun ⟨N,hN⟩ => ⟨N,fun n hn => (hN n hn).symm⟩,
    fun ⟨N,hN⟩ ⟨M,hM⟩ =>
      ⟨max N M,fun n hn => (hN n ((le_max_left _ _).trans hn)).trans
        (hM n ((le_max_right _ _).trans hn))⟩⟩

abbrev Eventual (A : Type*) := Quotient (eventualSetoid A)

def eventualMk {A : Type*} (f : ℕ → A) : Eventual A := Quotient.mk _ f

theorem eventualMk_eq_iff {A : Type*} (f g : ℕ → A) :
    eventualMk f = eventualMk g ↔ ∃ N, ∀ n, N ≤ n → f n = g n :=
  Quotient.eq

/-- The tails and the actual normal subgroup of eventual pointwise fixers.
For components, these data are supplied by `Chain.tailFixer_normal`.
No bijections or selector are included among the data. -/
structure TailData (G : Type u) (I : Type v) [Group G] [MulAction G I] where
  tail : ℕ → Set I
  antitone : Antitone tail
  K : Subgroup G
  normal : K.Normal
  mem_iff : ∀ k, k ∈ K ↔ ∃ N, ∀ i ∈ tail N, k • i = i

namespace TailData
variable {G : Type u} {I : Type v} [Group G] [MulAction G I] (D : TailData G I)
instance : D.K.Normal := D.normal

abbrev Cosets := G ⧸ D.K
abbrev Nonidentity := {δ : D.Cosets // δ ≠ 1}

/-- The fixed representative of a nonidentity coset cannot fix any entire
chain tail. -/
theorem detector_exists (δ : D.Nonidentity) (n : ℕ) :
    ∃ i ∈ D.tail n, δ.val.out • i ≠ i := by
  by_contra! h
  have hk : δ.val.out ∈ D.K := (D.mem_iff _).mpr ⟨n,h⟩
  have he := (QuotientGroup.eq_one_iff δ.val.out).mpr hk
  exact δ.property (by simpa only [QuotientGroup.out_eq'] using he)

def detector (δ : D.Nonidentity) (n : ℕ) : I := (D.detector_exists δ n).choose

theorem detector_mem (δ : D.Nonidentity) (n : ℕ) : D.detector δ n ∈ D.tail n :=
  (D.detector_exists δ n).choose_spec.1

theorem detector_moved (δ : D.Nonidentity) (n : ℕ) :
    δ.val.out • D.detector δ n ≠ D.detector δ n :=
  (D.detector_exists δ n).choose_spec.2

theorem detector_fixed_eventually {k : G} (hk : k ∈ D.K) (δ : D.Nonidentity) :
    ∃ N, ∀ n, N ≤ n → k • D.detector δ n = D.detector δ n := by
  obtain ⟨N,hN⟩ := (D.mem_iff k).mp hk
  exact ⟨N,fun n hn => hN _ (D.antitone hn (D.detector_mem δ n))⟩

variable {κ : Type w} [LinearOrder κ]

/-- A pattern is a tuple of sequences of bounded binary rows, modulo eventual
equality. The order later used on this type is fixed, not recomputed from rows. -/
abbrev Pattern (α : κ) := D.Nonidentity → Eventual (Set.Iio α → Bool)

def rawPattern (R : I → κ → Bool) (α : κ) (g : G) : D.Pattern α :=
  fun δ => eventualMk (fun n b => R (g • D.detector δ n) b.val)

theorem rawPattern_congr (R : I → κ → Bool) (α : κ) {g h : G}
    (he : (g : D.Cosets) = (h : D.Cosets)) :
    D.rawPattern R α g = D.rawPattern R α h := by
  funext δ
  obtain ⟨N,hN⟩ := D.detector_fixed_eventually (QuotientGroup.eq.mp he) δ
  apply (eventualMk_eq_iff _ _).mpr
  refine ⟨N,fun n hn => ?_⟩
  have hs : g • D.detector δ n = h • D.detector δ n := by
    have hh := congrArg (fun i : I => g • i) (hN n hn)
    simpa only [← mul_smul,mul_inv_cancel_left] using hh.symm
  rw [hs]

/-- Evaluating at the standard representative is harmless: the preceding
lemma proves independence of the representative. -/
def pattern (R : I → κ → Bool) (α : κ) (c : D.Cosets) : D.Pattern α :=
  D.rawPattern R α c.out

@[simp] theorem pattern_mk (R : I → κ → Bool) (α : κ) (g : G) :
    D.pattern R α (g : D.Cosets) = D.rawPattern R α g :=
  D.rawPattern_congr R α (QuotientGroup.out_eq' _)

/-- This is transport of the row data, not an automorphism of one fixed
universe of evaluated symmetric names. -/
def moveRows (σ : G) (R : I → κ → Bool) : I → κ → Bool :=
  fun i => R (σ⁻¹ • i)

@[simp] theorem rawPattern_moveRows (σ g : G) (R : I → κ → Bool) (α : κ) :
    D.rawPattern (moveRows σ R) α (σ*g) = D.rawPattern R α g := by
  funext δ
  apply congrArg eventualMk
  funext n b
  change R (σ⁻¹ • ((σ*g) • D.detector δ n)) b.val = R (g • D.detector δ n) b.val
  rw [mul_smul,inv_smul_smul]

/-- The actual pattern objects, not just their cardinalities, are identical
under left multiplication in the quotient and transport of rows. -/
theorem pattern_covariance (σ : G) (R : I → κ → Bool) (α : κ) (c : D.Cosets) :
    D.pattern (moveRows σ R) α ((σ : D.Cosets) * c) = D.pattern R α c := by
  induction c using Quotient.inductionOn with
  | h g => rw [← QuotientGroup.mk_mul,D.pattern_mk,D.pattern_mk,D.rawPattern_moveRows]

/-- Distinct cosets are detected at every sufficiently late position of one
of the fixed detector sequences. -/
theorem detector_separates (g h : G) (hne : (g : D.Cosets) ≠ (h : D.Cosets)) :
    ∃ δ : D.Nonidentity, ∃ N, ∀ n, N ≤ n →
      g • D.detector δ n ≠ h • D.detector δ n := by
  let δ : D.Nonidentity := ⟨((g⁻¹*h : G) : D.Cosets),by
    intro he
    exact hne (QuotientGroup.eq.mpr ((QuotientGroup.eq_one_iff _).mp he))⟩
  have he : (δ.val.out : D.Cosets) = ((g⁻¹*h : G) : D.Cosets) :=
    QuotientGroup.out_eq' δ.val
  obtain ⟨N,hN⟩ := D.detector_fixed_eventually (QuotientGroup.eq.mp he) δ
  refine ⟨δ,N,fun n hn heq => ?_⟩
  have hh : (g⁻¹*h) • D.detector δ n = δ.val.out • D.detector δ n := by
    have hh := congrArg (fun i : I => δ.val.out • i) (hN n hn)
    simpa only [← mul_smul,mul_inv_cancel_left] using hh
  have hh' := congrArg (fun i : I => g⁻¹ • i) heq
  rw [inv_smul_smul,← mul_smul,hh] at hh'
  exact D.detector_moved δ n hh'.symm

/-- Each pair is separated by every bound above one common countable bound.
Only injectivity of the rows and countable boundedness of κ are used. -/
theorem pair_separated [Nonempty κ]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    (R : I → κ → Bool) (hR : Function.Injective R) (c e : D.Cosets) (hne : c ≠ e) :
    ∃ α : κ, ∀ β, α ≤ β → D.pattern R β c ≠ D.pattern R β e := by
  have hne' : (c.out : D.Cosets) ≠ (e.out : D.Cosets) := by
    simpa only [QuotientGroup.out_eq'] using hne
  obtain ⟨δ,N,hN⟩ := D.detector_separates c.out e.out hne'
  have hbits (n : ℕ) : ∃ b : κ,
      R (c.out • D.detector δ (n+N)) b ≠ R (e.out • D.detector δ (n+N)) b := by
    by_contra! he
    exact hN _ (Nat.le_add_left _ _) (hR (funext he))
  choose bit hbit using hbits
  obtain ⟨α,hα⟩ := hbound bit
  refine ⟨α,fun β hαβ he => ?_⟩
  have hδ := congrFun he δ
  obtain ⟨M,hM⟩ := (eventualMk_eq_iff _ _).mp hδ
  have hh := congrFun (hM (M+N) (Nat.le_add_right _ _))
    (⟨bit M,(hα M).trans_le hαβ⟩ : Set.Iio β)
  exact hbit M hh

/-- Countably many germs require only one strictly bounded collection of
bits. No closure of the diagram forcing, or choice inside a symmetric model,
is being assumed in this statement. -/
theorem distinguished_bound [Nonempty κ] [Countable D.Cosets]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    (R : I → κ → Bool) (hR : Function.Injective R) :
    ∃ α : κ, Function.Injective (D.pattern R α) := by
  have hp (p : D.Cosets × D.Cosets) :
      ∃ α : κ, ∀ β, α ≤ β → p.1 ≠ p.2 → D.pattern R β p.1 ≠ D.pattern R β p.2 := by
    by_cases he : p.1 = p.2
    · exact ⟨Classical.choice ‹Nonempty κ›,fun _ _ h => False.elim (h he)⟩
    · obtain ⟨α,hα⟩ := D.pair_separated hbound R hR p.1 p.2 he
      exact ⟨α,fun β hβ _ => hα β hβ⟩
  choose bound hbound' using hp
  obtain ⟨enumerate,henumerate⟩ := exists_surjective_nat (D.Cosets × D.Cosets)
  obtain ⟨α,hα⟩ := hbound (bound ∘ enumerate)
  refine ⟨α,fun c e he => ?_⟩
  by_contra hne
  obtain ⟨n,hn⟩ := henumerate (c,e)
  exact hbound' (c,e) α (by simpa only [Function.comp_apply,hn] using (hα n).le) hne he

variable [WellFoundedLT κ]

/-- The first distinguishing bound in the fixed ordinal ordering. The proof
of existence is an input only to this definition, not to its application to
countable germs in `distinguished_bound`. -/
def leastBound (R : I → κ → Bool) (h : ∃ α, Function.Injective (D.pattern R α)) : κ :=
  wellFounded_lt.min {α | Function.Injective (D.pattern R α)} h

theorem leastBound_distinguishes (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α)) :
    Function.Injective (D.pattern R (D.leastBound R h)) :=
  wellFounded_lt.min_mem _ h

omit [WellFoundedLT κ] in
theorem distinguishes_moveRows_iff (σ : G) (R : I → κ → Bool) (α : κ) :
    Function.Injective (D.pattern (moveRows σ R) α) ↔ Function.Injective (D.pattern R α) := by
  constructor
  · intro hinj c e he
    apply mul_left_cancel (a := (σ : D.Cosets))
    apply hinj
    simpa only [D.pattern_covariance] using he
  · intro hinj c e he
    have hc := D.pattern_covariance σ R α ((σ : D.Cosets)⁻¹*c)
    have he' := D.pattern_covariance σ R α ((σ : D.Cosets)⁻¹*e)
    simp only [mul_inv_cancel_left] at hc he'
    have hh := hinj (hc.symm.trans (he.trans he'))
    exact mul_left_cancel hh

theorem leastBound_covariance (σ : G) (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α))
    (h' : ∃ α, Function.Injective (D.pattern (moveRows σ R) α)) :
    D.leastBound (moveRows σ R) h' = D.leastBound R h := by
  have hs : {α | Function.Injective (D.pattern (moveRows σ R) α)} =
      {α | Function.Injective (D.pattern R α)} := by
    ext α
    exact D.distinguishes_moveRows_iff σ R α
  unfold leastBound
  congr 1

/-- Minimization is on pattern objects with their fixed wellordering, not on
an arbitrary ordering of the cosets. -/
def bestCoset (R : I → κ → Bool) (α : κ) : D.Cosets :=
  (InvImage.wf (D.pattern R α) WellOrderingRel.isWellOrder.wf).min
    Set.univ Set.univ_nonempty

omit [WellFoundedLT κ] in
theorem bestCoset_minimal (R : I → κ → Bool) (α : κ) (c : D.Cosets) :
    ¬ WellOrderingRel (D.pattern R α c) (D.pattern R α (D.bestCoset R α)) :=
  (InvImage.wf (D.pattern R α) WellOrderingRel.isWellOrder.wf).not_lt_min
    Set.univ (Set.mem_univ c)

omit [WellFoundedLT κ] in
theorem bestCoset_covariance (σ : G) (R : I → κ → Bool) (α : κ)
    (hα : Function.Injective (D.pattern R α)) :
    D.bestCoset (moveRows σ R) α = (σ : D.Cosets) * D.bestCoset R α := by
  let c := D.bestCoset (moveRows σ R) α
  let e := D.bestCoset R α
  have hc : D.pattern (moveRows σ R) α c = D.pattern R α ((σ : D.Cosets)⁻¹*c) := by
    simpa only [mul_inv_cancel_left] using D.pattern_covariance σ R α ((σ : D.Cosets)⁻¹*c)
  have hmin : ¬ WellOrderingRel (D.pattern R α e) (D.pattern R α ((σ : D.Cosets)⁻¹*c)) := by
    have hh := D.bestCoset_minimal (moveRows σ R) α ((σ : D.Cosets)*e)
    rwa [D.pattern_covariance,hc] at hh
  have hmin' := D.bestCoset_minimal R α ((σ : D.Cosets)⁻¹*c)
  have heq : D.pattern R α ((σ : D.Cosets)⁻¹*c) = D.pattern R α e := by
    rcases trichotomous_of WellOrderingRel (D.pattern R α ((σ : D.Cosets)⁻¹*c))
      (D.pattern R α e) with hlt | heq | hgt
    · exact (hmin' hlt).elim
    · exact heq
    · exact (hmin hgt).elim
  have hh := congrArg (fun d : D.Cosets => (σ : D.Cosets)*d) (hα heq)
  simpa only [mul_inv_cancel_left,c,e] using hh

/-- The coset selected at the least distinguishing bound. -/
def selector (R : I → κ → Bool) (h : ∃ α, Function.Injective (D.pattern R α)) : D.Cosets :=
  D.bestCoset R (D.leastBound R h)

/-- Source equation (coset-selector-covariance), proved with the actual row
objects on both sides, including invariance of the least distinguishing bound. -/
theorem selector_covariance (σ : G) (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α))
    (h' : ∃ α, Function.Injective (D.pattern (moveRows σ R) α)) :
    D.selector (moveRows σ R) h' = (σ : D.Cosets) * D.selector R h := by
  unfold selector
  rw [D.leastBound_covariance σ R h h']
  exact D.bestCoset_covariance σ R _ (D.leastBound_distinguishes R h)

omit [LinearOrder κ] [WellFoundedLT κ] in
/-- Transport preserves the distinguishing property of complete rows. -/
theorem moveRows_injective (σ : G) (R : I → κ → Bool) (hR : Function.Injective R) :
    Function.Injective (moveRows σ R) := by
  intro i j he
  have hh := congrArg (fun x : I => σ • x) (hR he)
  simpa only [smul_inv_smul] using hh

/-- With countability and regularity in hand the defining existence proof is
provided by `distinguished_bound`, rather than assumed of the chosen patterns. -/
def countableSelector [Nonempty κ] [Countable D.Cosets]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    (R : I → κ → Bool) (hR : Function.Injective R) : D.Cosets :=
  D.selector R (D.distinguished_bound hbound R hR)

theorem countableSelector_covariance [Nonempty κ] [Countable D.Cosets]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    (σ : G) (R : I → κ → Bool) (hR : Function.Injective R) :
    D.countableSelector hbound (moveRows σ R) (moveRows_injective σ R hR) =
      (σ : D.Cosets) * D.countableSelector hbound R hR :=
  D.selector_covariance σ R _ _

end TailData
end
end PartitionConsistency.TailSelector

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u
open DiagramOrder DiagramForcing TailSelector
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I} {v : Vertex q}
noncomputable section

/-- The abstract tail data are supplied by the actual component stabilizer
and the union of its pointwise tail fixers previously constructed. -/
def tailData (C : Chain v) (hj : HasConditionalJoins (LeftDivOrder M)) :
    TailData (componentStabilizer hj v) I where
  tail := fun i => (C.vertex i).diagram.range
  antitone := C.ranges_antitone
  K := C.tailFixer hj
  normal := inferInstance
  mem_iff := C.mem_tailFixer hj

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain

end OAI
