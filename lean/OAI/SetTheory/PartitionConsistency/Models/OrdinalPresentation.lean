import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.UniformNames

namespace OAI

/-! ## Completion -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

namespace BinaryRelation
/-- Any fixed formula with two distinguished free variables gives a regular
binary forcing relation. Its other free variables remain actual parameters. -/
def ofFormula {n} (v : Fin n → S.Name) (φ : Formula (n+2)) : S.BinaryRelation where
  holds p x y := S.Forces (Fin.snoc (Fin.snoc v x) y) p φ
  mono h hp := S.atomic.forceFormula_mono h hp
  regular h := S.atomic.forceFormula_of_dense S.atomic_regular h
  congr hx hy := by
    apply S.atomic.forceFormula_tuple_congr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hy
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hx
      · simpa only [Fin.snoc_castSucc] using S.atomic.eq_refl _ (v j)

omit [OrderTop P] in
theorem ofFormula_symmetry {n} (v : Fin n → S.Name) (φ : Formula (n+2))
    (g : Γ) (hv : ∀ i, g • v i = v i) (p : P) (x y : S.Name) :
    (ofFormula S v φ).holds p x y ↔
      (ofFormula S v φ).holds (S.move g p) (g • x) (g • y) := by
  have hh := S.forces_symmetry g φ (Fin.snoc (Fin.snoc v x) y) p
  have he : (fun i => g • Fin.snoc (Fin.snoc v x) y i) =
      Fin.snoc (Fin.snoc v (g • x)) (g • y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_castSucc,Fin.snoc_last]
      · simp only [Fin.snoc_castSucc,hv]
  change S.Forces _ _ _ ↔ S.Forces _ _ _
  simpa only [he] using hh
end BinaryRelation

/-- Use a partial graph's value when it belongs to the codomain, and otherwise
use the specified default. The variables are `f,X,x₀,a,y`, respectively. -/
def defaultFormula : Formula 5 :=
  ((SetLanguage.edge 0 3 4).conj (.mem 4 1)).disj
    ((Formula.ex ((SetLanguage.edge 0 3 5).conj (.mem 5 1))).neg.conj (.equal 4 2))

def defaultRelation (f X x₀ : S.Name) : S.BinaryRelation :=
  BinaryRelation.ofFormula S ![f,X,x₀] defaultFormula

def NoValue (f X : S.Name) (p : P) (a : S.Name) : Prop :=
  ∀ q, q ≤ p → ∀ y : S.Name, S.App q f a y → S.atomic.MemF q y X → False

omit [OrderTop P] in
theorem noValue_mono {f X a : S.Name} {p q : P} (h : q ≤ p)
    (hn : S.NoValue f X p a) : S.NoValue f X q a :=
  fun r hr => hn r (hr.trans h)

omit [OrderTop P] in
/-- An exact description of the default relation's Boolean disjunction.
The fallback is used only when every possible bounded graph value is ruled out. -/
theorem defaultRelation_iff (f X x₀ a y : S.Name) (p : P) :
    (S.defaultRelation f X x₀).holds p a y ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧
        ((S.App r f a y ∧ S.atomic.MemF r y X) ∨
          (S.NoValue f X r a ∧ S.atomic.EqF r y x₀)) := by
  simp only [defaultRelation,BinaryRelation.ofFormula,defaultFormula,Forces,
    ForcingQuotient.AtomicData.forceFormula_disj,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_ex,S.atomic.forceFormula_neg S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_edge]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,hr | hr⟩ := h q hqp
    · exact ⟨r,hrq,Or.inl hr⟩
    · refine ⟨r,hrq,Or.inr ⟨?_,hr.2⟩⟩
      intro t htr z ha hz
      apply hr.1 t htr
      intro b hbt
      exact ⟨b,le_rfl,z,S.app_mono hbt ha,S.atomic.mem_mono hbt hz⟩
  · intro h q hqp
    obtain ⟨r,hrq,hr | hr⟩ := h q hqp
    · exact ⟨r,hrq,Or.inl hr⟩
    · refine ⟨r,hrq,Or.inr ⟨?_,hr.2⟩⟩
      intro t htr hh
      obtain ⟨b,hbt,z,ha,hz⟩ := hh t le_rfl
      exact hr.1 b (hbt.trans htr) z ha hz

omit [OrderTop P] in
theorem defaultRelation_of_app {f X x₀ a y : S.Name} {p : P}
    (ha : S.App p f a y) (hy : S.atomic.MemF p y X) :
    (S.defaultRelation f X x₀).holds p a y := by
  apply (S.defaultRelation_iff f X x₀ a y p).mpr
  intro q hqp
  exact ⟨q,le_rfl,Or.inl ⟨S.app_mono hqp ha,S.atomic.mem_mono hqp hy⟩⟩

omit [OrderTop P] in
/-- The default construction is densely total, with values actually in `X`,
whenever the default belongs to `X`. -/
theorem defaultRelation_total (f X x₀ a : S.Name) {p : P} (hx₀ : S.atomic.MemF p x₀ X) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name,
      S.atomic.MemF r y X ∧ (S.defaultRelation f X x₀).holds r a y := by
  intro q hqp
  by_cases hh : ∃ r, r ≤ q ∧ ∃ y : S.Name, S.App r f a y ∧ S.atomic.MemF r y X
  · obtain ⟨r,hrq,y,ha,hy⟩ := hh
    exact ⟨r,hrq,y,hy,S.defaultRelation_of_app ha hy⟩
  · refine ⟨q,le_rfl,x₀,S.atomic.mem_mono hqp hx₀,?_⟩
    apply (S.defaultRelation_iff f X x₀ a x₀ q).mpr
    intro r hrq
    refine ⟨r,le_rfl,Or.inr ⟨?_,S.atomic.eq_refl r x₀⟩⟩
    intro t htr y ha hy
    exact hh ⟨t,htr.trans hrq,y,ha,hy⟩

omit [OrderTop P] in
/-- Completing a genuinely single-valued partial graph preserves uniqueness. -/
theorem defaultRelation_unique (f X x₀ : S.Name)
    (hf : ∀ p, ∀ a y z : S.Name, S.App p f a y → S.App p f a z → S.atomic.EqF p y z)
    (p : P) (a y z : S.Name) (hy : (S.defaultRelation f X x₀).holds p a y)
    (hz : (S.defaultRelation f X x₀).holds p a z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,hr⟩ := (S.defaultRelation_iff f X x₀ a y p).mp hy q hqp
  obtain ⟨s,hsr,hs⟩ := (S.defaultRelation_iff f X x₀ a z p).mp hz r (hrq.trans hqp)
  refine ⟨s,hsr.trans hrq,?_⟩
  rcases hr with ⟨hr,hyX⟩ | ⟨hr,hy₀⟩ <;> rcases hs with ⟨hs,hzX⟩ | ⟨hs,hz₀⟩
  · exact hf s a y z (S.app_mono hsr hr) hs
  · exact (hs s le_rfl y (S.app_mono hsr hr) (S.atomic.mem_mono hsr hyX)).elim
  · exact (hr s hsr z hs hzX).elim
  · exact S.atomic.eq_trans (S.atomic.eq_mono hsr hy₀) (S.atomic.eq_symm hz₀)

omit [OrderTop P] in
theorem defaultRelation_symmetry (f X x₀ : S.Name) (g : Γ)
    (hf : g • f = f) (hX : g • X = X) (hx₀ : g • x₀ = x₀)
    (p : P) (a y : S.Name) :
    (S.defaultRelation f X x₀).holds p a y ↔
      (S.defaultRelation f X x₀).holds (S.move g p) (g • a) (g • y) := by
  apply BinaryRelation.ofFormula_symmetry
  intro i
  fin_cases i <;> assumption

/-- A ground-indexed family of completed partial maps, with an actual ordered
pair as input. Local witnesses are regularized, as in existential forcing. -/
def completionRelation (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name) : S.BinaryRelation where
  holds p x y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : O, ∃ a : S.Name,
    S.atomic.EqF r x (a.opair (Name.check i.val)) ∧
      (S.defaultRelation (f i) X x₀).holds r a y
  mono h hh q hq := hh q (hq.trans h)
  regular hh q hq := by
    obtain ⟨r,hrq,hr⟩ := hh q hq
    obtain ⟨s,hsr,i,a,ha,hR⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,i,a,ha,hR⟩
  congr hxx' hyy' := by
    constructor
    · intro h q hqp
      obtain ⟨r,hrq,i,a,ha,hR⟩ := h q hqp
      have hrp := hrq.trans hqp
      exact ⟨r,hrq,i,a,S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hrp hxx')) ha,
        ((S.defaultRelation (f i) X x₀).congr (S.atomic.eq_refl r a)
          (S.atomic.eq_mono hrp hyy')).mp hR⟩
    · intro h q hqp
      obtain ⟨r,hrq,i,a,ha,hR⟩ := h q hqp
      have hrp := hrq.trans hqp
      exact ⟨r,hrq,i,a,S.atomic.eq_trans (S.atomic.eq_mono hrp hxx') ha,
        ((S.defaultRelation (f i) X x₀).congr (S.atomic.eq_refl r a)
          (S.atomic.eq_mono hrp hyy')).mpr hR⟩

theorem completionRelation_at (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name)
    (i : O) (a y : S.Name) (p : P) (h : (S.defaultRelation (f i) X x₀).holds p a y) :
    (S.completionRelation O f X x₀).holds p (a.opair (Name.check i.val)) y :=
  fun q hqp => ⟨q,le_rfl,i,a,S.atomic.eq_refl q _,(S.defaultRelation _ X x₀).mono hqp h⟩

theorem completionRelation_symmetry (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name)
    (g : Γ) (hf : ∀ i, g • f i = f i) (hX : g • X = X) (hx₀ : g • x₀ = x₀)
    (p : P) (x y : S.Name) (h : (S.completionRelation O f X x₀).holds p x y) :
    (S.completionRelation O f X x₀).holds (S.move g p) (g • x) (g • y) := by
  intro q hqp
  have hqp' : (S.move g).symm q ≤ p := (S.move g).symm_apply_le.mpr hqp
  obtain ⟨r,hrq,i,a,ha,hR⟩ := h _ hqp'
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,g • a,?_,?_⟩
  · simpa only [Name.smul_opair,Name.smul_check] using (S.eq_symmetry g r x _).mp ha
  · exact (S.defaultRelation_symmetry (f i) X x₀ g (hf i) hX hx₀ r a y).mp hR

/-- Uniqueness for a family of partial functions survives both completion and
packaging into one Cartesian-domain graph. -/
theorem completionRelation_unique (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name)
    (hf : ∀ i p, ∀ a y z : S.Name, S.App p (f i) a y → S.App p (f i) a z →
      S.atomic.EqF p y z) (p : P) (x y z : S.Name)
    (hy : (S.completionRelation O f X x₀).holds p x y)
    (hz : (S.completionRelation O f X x₀).holds p x z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,i,a,ha,hy⟩ := hy q hqp
  obtain ⟨s,hsr,j,b,hb,hz⟩ := hz r (hrq.trans hqp)
  have hh := S.eq_opair_iff.mp (S.atomic.eq_trans
    (S.atomic.eq_symm (S.atomic.eq_mono hsr ha)) hb)
  have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val s).mp hh.2)
  subst j
  refine ⟨s,hsr.trans hrq,?_⟩
  apply S.defaultRelation_unique (f i) X x₀ (hf i) s b y z
  · exact ((S.defaultRelation (f i) X x₀).congr hh.1 (S.atomic.eq_refl s y)).mp
      ((S.defaultRelation (f i) X x₀).mono hsr hy)
  · exact hz

/-- The completed relation is total on the literal product name. -/
theorem completionRelation_total (O : ZFSet.{u}) (f : O → S.Name) (A X x₀ : S.Name)
    {p : P} (hx₀ : S.atomic.MemF p x₀ X) (x : S.Name) {q : P} (hqp : q ≤ p)
    (hx : S.atomic.MemF q x (S.cartesianName A (Name.check O))) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name,
      S.atomic.MemF s y X ∧ (S.completionRelation O f X x₀).holds s x y := by
  intro r hrq
  obtain ⟨s,hsr,a,b,_,hb,hx⟩ := (S.mem_cartesianName A (Name.check O) x q).mp hx r hrq
  obtain ⟨t,hts,i,hi,hbi⟩ := (S.mem_check O b s).mp hb s le_rfl
  let i' : O := ⟨i,hi⟩
  obtain ⟨v,hvt,y,hy,hf⟩ := S.defaultRelation_total (f i') X x₀ a
    (S.atomic.mem_mono (hts.trans (hsr.trans (hrq.trans hqp))) hx₀) t le_rfl
  refine ⟨v,hvt.trans (hts.trans hsr),y,hy,?_⟩
  have hx' := S.atomic.eq_trans (S.atomic.eq_mono (hvt.trans hts) hx)
    (S.eq_opair_congr (S.atomic.eq_refl v a) (S.atomic.eq_mono hvt hbi))
  exact ((S.completionRelation O f X x₀).congr hx' (S.atomic.eq_refl v y)).mpr
    (S.completionRelation_at O f X x₀ i' a y v hf)

/-- Auxiliary graph construction for a family of invariant partial orbit maps.
The support is precisely a common support for the three displayed set names. -/
def completionGraph (O : ZFSet.{u}) (f : O → S.Name) (A X x₀ : S.Name)
    (hf : ∀ g : Γ, ∀ i, g • f i = f i) : S.Name :=
  let H := S.productSupport A X ⊓ MulAction.stabilizer Γ x₀.val
  (S.completionRelation O f X x₀).graph (S.cartesianName A (Name.check O)) X H
    (S.normal.2.2.1 _ _ (S.productSupport_mem A X) x₀.hs.symmetric)
    (fun g hg => S.cartesianName_fixed A (Name.check O) g (Subtype.ext hg.1.1) (Name.smul_check S g O))
    (fun _ hg => Subtype.ext hg.1.2)
    (fun g hg p x y h => S.completionRelation_symmetry O f X x₀ g (hf g)
      (Subtype.ext hg.1.2) (Subtype.ext hg.2) p x y h)

/-- A densely covering family of invariant partial functions yields an actual
internal surjection from `A × O` onto `X`. All graph and domain names have been
constructed; the family and its covering property are explicit inputs here. -/
theorem completionGraph_surjection (O : ZFSet.{u}) (f : O → S.Name) (A X x₀ : S.Name)
    (hinv : ∀ g : Γ, ∀ i, g • f i = f i)
    (hf : ∀ i p, ∀ a y z : S.Name, S.App p (f i) a y → S.App p (f i) a z →
      S.atomic.EqF p y z) (p : P) (hx₀ : S.atomic.MemF p x₀ X)
    (hcover : ∀ y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q y X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ i : O, ∃ a : S.Name,
        S.atomic.MemF s a A ∧ S.App s (f i) a y) :
    S.Forces ![S.completionGraph O f A X x₀ hinv,S.cartesianName A (Name.check O),X]
      p (SetLanguage.surjection 0 1 2) := by
  unfold completionGraph
  refine BinaryRelation.graph_surjection (S.completionRelation O f X x₀)
    (S.cartesianName A (Name.check O)) X
    (S.productSupport A X ⊓ MulAction.stabilizer Γ x₀.val)
    (S.normal.2.2.1 _ _ (S.productSupport_mem A X) x₀.hs.symmetric)
    (fun g hg => S.cartesianName_fixed A (Name.check O) g (Subtype.ext hg.1.1) (Name.smul_check S g O))
    (fun _ hg => Subtype.ext hg.1.2)
    (fun g hg p x y h => S.completionRelation_symmetry O f X x₀ g (hinv g)
      (Subtype.ext hg.1.2) (Subtype.ext hg.2) p x y h) p ?_ ?_ ?_
  · exact fun x q hqp hx => S.completionRelation_total O f A X x₀ hx₀ x hqp hx
  · exact fun q _ x y z => S.completionRelation_unique O f X x₀ hf q x y z
  · intro y q hqp hy r hrq
    obtain ⟨s,hsr,i,a,ha,hf⟩ := hcover y q hqp hy r hrq
    refine ⟨s,hsr,a.opair (Name.check i.val),?_,?_⟩
    · exact (S.opair_mem_cartesianName A (Name.check O) a (Name.check i.val) s).mpr
        ⟨ha,S.check_mem_of_mem i.property s⟩
    · exact S.completionRelation_at O f X x₀ i a y s
        (S.defaultRelation_of_app hf (S.atomic.mem_mono (hsr.trans hrq) hy))

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Presentation -/

namespace PartitionConsistency
universe u
noncomputable section

/-- Every small type can be enumerated by the elements of an actual ground
ordinal. This is an external use of Choice, not of Choice in the symmetric
model being constructed. -/
theorem exists_ordinal_equiv (α : Type (u+1)) [Small.{u} α] :
    ∃ o : Ordinal.{u}, Nonempty (o.toZFSet ≃ α) := by
  let o := (Cardinal.mk (Shrink.{u} α)).ord
  refine ⟨o,Cardinal.eq.mp ?_⟩
  rw [ZFSet.cardinalMk_coe_sort,Ordinal.card_toZFSet]
  change Cardinal.lift.{u+1} (Cardinal.mk (Shrink.{u} α)).ord.card = Cardinal.mk α
  rw [Cardinal.card_ord]
  exact Cardinal.lift_mk_shrink''.{u+1,u} α

end
end PartitionConsistency

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- All literal member names of `X` together with all their supporting
diagrams. No rank bound is placed on `X` or on its descendants. -/
def PresentationIndex (X : (system (M := M) (I := I) (κ := κ) hμ).Name) :=
  {ip : Edges X.raw × Diagram M I //
    ∀ g ∈ SupportFilter.Fix ip.2.range, g • X.child ip.1.property = X.child ip.1.property}

instance (X : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    Small.{u} (PresentationIndex hμ X) := by
  unfold PresentationIndex
  infer_instance

/-- The partial function associated to a presentation record is a literal
orbit graph, not a selected representative in an evaluated universe. -/
def presentationPartial (c : κ → ZFSet.{u})
    (X : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (i : PresentationIndex hμ X) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  orbitGraph hμ c (X.child i.val.1.property) i.val.2

@[simp] theorem smul_presentationPartial (c : κ → ZFSet.{u})
    (X : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (i : PresentationIndex hμ X) (π : Equiv.Perm I) :
    π • presentationPartial hμ c X i = presentationPartial hμ c X i :=
  smul_orbitGraph hμ c _ _ π

/-- Single-valuedness uses genuine label separation and the support recorded
in the index. It is proved uniformly for all records. -/
theorem presentationPartial_unique [Uncountable κ] (c : κ → ZFSet.{u})
    (hc : Function.Injective c)
    (X : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (i : PresentationIndex hμ X) (p : Poset M I κ)
    (a y z : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hy : (system hμ).App p (presentationPartial hμ c X i) a y)
    (hz : (system hμ).App p (presentationPartial hμ c X i) a z) :
    (system hμ).atomic.EqF p y z :=
  orbitGraph_unique hμ c hc _ _ i.property a y z p hy hz

/-- Every member is densely reached by one of the presentation's partial
functions. The supporting diagram is chosen below the condition witnessing
membership, rather than presumed to belong to a generic filter. -/
theorem presentationPartial_cover [Infinite I]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u})
    (X y : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hy : (system hμ).atomic.MemF t y X) :
    ∀ q, q ≤ t → ∃ r, r ≤ q ∧ ∃ i : PresentationIndex hμ X,
      ∃ a : (system (M := M) (I := I) (κ := κ) hμ).Name,
        (system hμ).atomic.MemF r a (labelSet (M := M) (I := I) hμ c) ∧
        (system hμ).App r (presentationPartial hμ c X i) a y := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨emb⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨emb⟩⟩
  intro q hqt
  obtain ⟨r,hrq,σ,b,hσ,hrb,hyσ⟩ := S.mem_iff.mp hy q hqt
  let j : Edges X.raw := ⟨(σ.raw,S.code b),hσ⟩
  have hj : X.child j.property = σ := Name.ext rfl
  obtain ⟨J,hJ,hfix⟩ := name_support hμ σ
  obtain ⟨d,hdr⟩ := exists_condition_below r
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through hsize e he d.2 (by rwa [hcard])
  have hs : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ := by
    intro g hg
    exact hfix g ((SupportFilter.mem_Fix _ _).mpr (fun z hz =>
      (SupportFilter.mem_Fix _ _).mp hg z (hcover hz)))
  let i : PresentationIndex hμ X := ⟨(j,p),by simpa only [hj] using hs⟩
  let s : Poset M I κ := (d.1,p)
  have hsd : s ≤ (d : Poset M I κ) := WithTop.coe_le_coe.mpr ⟨le_rfl,⟨e,hp⟩⟩
  have hsr := hsd.trans hdr
  have ha := S.app_mono (WithTop.coe_le_coe.mpr (show (d.1,p) ≤ ((⊤ : CohenForcing.Condition I κ),p) from
      ⟨le_top,le_rfl⟩)) (orbitGraph_app_self hμ c σ p)
  have hi : presentationPartial hμ c X i = orbitGraph hμ c σ p := by
    change orbitGraph hμ c (X.child j.property) p = _
    rw [hj]
  refine ⟨s,hsr.trans hrq,i,label (M := M) hμ c (p 1),label_mem_labelSet hμ c _ s,?_⟩
  rw [hi]
  exact (S.app_congr (S.atomic.eq_refl s _) (S.atomic.eq_refl s _)
    (S.atomic.eq_symm (S.atomic.eq_mono hsr hyσ))).mp ha

/-- The unrestricted-rank presentation theorem. Given a single member of `X`
at a condition, this constructs an actual internal graph forced to surject
from the Cartesian product of the invariant label set with a ground ordinal.
There is no inaccessible cardinal, name-rank bound, or assumed coverage. -/
theorem ordinal_presentation [Infinite I] [Uncountable κ]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u}) (hc : Function.Injective c)
    (X x₀ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ)
    (hx₀ : (system hμ).atomic.MemF p x₀ X) :
    ∃ η : Ordinal.{u}, ∃ f : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (system hμ).Forces ![f,(system (M := M) (I := I) (κ := κ) hμ).cartesianName
        (labelSet (M := M) (I := I) hμ c) (Name.check η.toZFSet),X]
          p (SetLanguage.surjection 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨η,⟨ε⟩⟩ := exists_ordinal_equiv (PresentationIndex hμ X)
  let f : η.toZFSet → S.Name := fun i => presentationPartial hμ c X (ε i)
  have hinv : ∀ g : Equiv.Perm I, ∀ i, g • f i = f i :=
    fun g i => smul_presentationPartial hμ c X (ε i) g
  have hfun : ∀ i r, ∀ a y z : S.Name, S.App r (f i) a y → S.App r (f i) a z →
      S.atomic.EqF r y z := fun i r a y z => presentationPartial_unique hμ c hc X (ε i) r a y z
  refine ⟨η,S.completionGraph η.toZFSet f (labelSet (M := M) (I := I) hμ c) X x₀ hinv,?_⟩
  apply S.completionGraph_surjection η.toZFSet f _ X x₀ hinv hfun p hx₀
  intro y q _ hy r hrq
  obtain ⟨s,hsr,i,a,ha,hf⟩ := presentationPartial_cover hμ hcard hsize e he c X y q hy r hrq
  refine ⟨s,hsr,ε.symm i,a,ha,?_⟩
  simpa only [f,Equiv.apply_symm_apply] using hf

end
end PartitionConsistency.ProductForcing

end OAI
