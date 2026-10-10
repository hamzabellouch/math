import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.LocalQuotients

namespace OAI

/-! ## Record -/


/-! The ground record calculation for local quotients. These results count
literal witnesses of local representation by a covariant family of names.
They do not assume that every normalized subset is such a class, or assert
that every local E-class has a witness without the forcing argument. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
variable {A I κ : Type u}

/-- Pull back just the coordinates in an injective diagram. -/
def pullback (d : Condition I κ) (r : A ↪ I) : Condition A κ where
  graph := (fun z : (A × κ) × Bool => ((r z.1.1,z.1.2),z.2)) ⁻¹' d.graph
  functional a b c hb hc := d.functional (r a.1,a.2) b c hb hc
  countable_graph := d.countable_graph.preimage (by
    rintro ⟨⟨a,k⟩,b⟩ ⟨⟨a',k'⟩,b'⟩ h
    have ha := r.injective (congrArg (fun z : (I × κ) × Bool => z.1.1) h)
    have hk := congrArg (fun z : (I × κ) × Bool => z.1.2) h
    have hb := congrArg (fun z : (I × κ) × Bool => z.2) h
    simp only at ha hk hb
    subst a'; subst k'; subst b'; rfl)

@[simp] theorem mem_pullback (d : Condition I κ) (r : A ↪ I) (z : (A × κ) × Bool) :
    z ∈ (d.pullback r).graph ↔ ((r z.1.1,z.1.2),z.2) ∈ d.graph := Iff.rfl

/-- The recorded partial function determines the original supported Cohen
condition up to the specified coordinate permutation. -/
theorem permute_eq_of_pullback_eq (r s : A ↪ I) (π : Equiv.Perm I)
    (hπ : ∀ x, π (r x) = s x) (d c : Condition I κ)
    (hd : d.support ⊆ Set.range r) (hc : c.support ⊆ Set.range s)
    (h : d.pullback r = c.pullback s) : d.permute π = c := by
  have hrecord (x : A) (k : κ) (b : Bool) :
      ((r x,k),b) ∈ d.graph ↔ ((s x,k),b) ∈ c.graph := by
    change ((x,k),b) ∈ (d.pullback r).graph ↔ ((x,k),b) ∈ (c.pullback s).graph
    rw [h]
  apply ext
  ext z
  constructor
  · intro hz
    have hmem := (mem_permute π d z).mp hz
    obtain ⟨x,hx⟩ := hd ((mem_support d _).mpr ⟨z.1.2,z.2,hmem⟩)
    have he : s x = z.1.1 := (hπ x).symm.trans ((congrArg π hx).trans (π.apply_symm_apply _))
    have hh := (hrecord x z.1.2 z.2).mp (hx ▸ hmem)
    simpa only [he] using hh
  · intro hz
    obtain ⟨x,hx⟩ := hc ((mem_support c _).mpr ⟨z.1.2,z.2,hz⟩)
    apply (mem_permute π d z).mpr
    have he : r x = π.symm z.1.1 := by
      apply π.injective
      rw [hπ,hx,π.apply_symm_apply]
    have hh := (hrecord x z.1.2 z.2).mpr (hx ▸ hz)
    simpa only [he] using hh

/-- A countable graph can be enumerated after adjoining `none`, including
when the condition is empty. -/
private theorem graph_code (d : Condition I κ) :
    ∃ f : ℕ → Option ((I × κ) × Bool),
      Set.range f = Set.insert none (Option.some '' d.graph) := by
  obtain ⟨f,hf⟩ := ((d.countable_graph.image Option.some).insert none).exists_eq_range
    (Set.insert_nonempty _ _)
  exact ⟨f,hf.symm⟩

/-- There are at most μ countable Cohen conditions on a space of size at
most μ when μ is a fixed point of countable exponentiation. -/
theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hμ : μ ^ Cardinal.aleph0 = μ) (hI : Cardinal.mk I ≤ μ)
    (hκ : Cardinal.mk κ ≤ μ) : Cardinal.mk (Condition I κ) ≤ μ := by
  let f (d : Condition I κ) := (graph_code d).choose
  have hf : Function.Injective f := by
    intro d c h
    apply ext
    have he : Set.insert none (Option.some '' d.graph) =
        Set.insert none (Option.some '' c.graph) :=
      ((graph_code d).choose_spec.symm.trans (congrArg Set.range h)).trans
        (graph_code c).choose_spec
    ext z
    have hz := Set.ext_iff.mp he (some z)
    change (some z = none ∨ ∃ x ∈ d.graph, some x = some z) ↔
      (some z = none ∨ ∃ x ∈ c.graph, some x = some z) at hz
    simpa only [Option.some_ne_none,Option.some.injEq,exists_eq_right,false_or] using hz
  have hbool : Cardinal.lift.{u} (Cardinal.mk Bool) ≤ μ := by
    rw [Cardinal.mk_bool,Cardinal.lift_ofNat]
    exact Cardinal.natCast_le_aleph0.trans hω
  have hop : Cardinal.mk (Option ((I × κ) × Bool)) ≤ μ := by
    simp only [Cardinal.mk_option,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_uzero]
    exact (add_le_add
      ((mul_le_mul' ((mul_le_mul' hI hκ).trans_eq (Cardinal.mul_eq_self hω)) hbool).trans_eq
        (Cardinal.mul_eq_self hω)) (Cardinal.one_le_aleph0.trans hω)).trans_eq
          (Cardinal.add_eq_self hω)
  calc
    Cardinal.mk (Condition I κ) ≤ Cardinal.mk (ℕ → Option ((I × κ) × Bool)) :=
      Cardinal.mk_le_of_injective hf
    _ = Cardinal.mk (Option ((I × κ) × Bool)) ^ Cardinal.aleph0 := by simp
    _ ≤ μ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hop
    _ = μ := hμ

end
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

/-- The actual triple (b,x,t⁻¹d) in the local-quotient proof. -/
abbrev LocalRecord := M × M × CohenForcing.Condition M κ

/-- A local representation by the covariant family, with its literal
stronger diagram and supported Cohen condition. -/
structure LocalWitness (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (C : I → (system (M := M) hμ).Name) (τ : LocalName hμ c r) where
  diagram : Diagram M I
  rootIndex : M
  root : diagram.sub rootIndex = r
  labelIndex : M
  condition : CohenForcing.Condition I κ
  mem : condition ∈ F
  supported : condition.support ⊆ diagram.range
  represents : (system hμ).atomic.EqF ((condition,diagram) : Poset M I κ)
    τ.name (C (diagram labelIndex))

namespace LocalWitness
variable {hμ} {F : GenericFilter (CohenForcing.Condition I κ)} {r : Diagram M I}
variable {C : I → (system (M := M) hμ).Name}

def record {τ : LocalName hμ c r} (w : LocalWitness hμ F r C τ) :
    LocalRecord (M := M) (κ := κ) :=
  (w.rootIndex,w.labelIndex,w.condition.pullback w.diagram.toEmbedding)

/-- Equal records identify the *actual* local quotient values. This proof
uses only name symmetry and reflection to the root, not an action on an
already evaluated extension. -/
theorem equal_of_record_eq [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (hC : ∀ π ∈ SupportFilter.Fix r.range, ∀ j, π • C j = C (π j))
    {τ σ : LocalName hμ c r} (w : LocalWitness hμ F r C τ) (z : LocalWitness hμ F r C σ)
    (hrecord : w.record = z.record) : LocalQuotient.ofName F τ = LocalQuotient.ofName F σ := by
  have hb : w.rootIndex = z.rootIndex := congrArg Prod.fst hrecord
  have hx : w.labelIndex = z.labelIndex := congrArg (fun t => t.2.1) hrecord
  have hd : w.condition.pullback w.diagram.toEmbedding =
      z.condition.pullback z.diagram.toEmbedding := congrArg (fun t => t.2.2) hrecord
  obtain ⟨π,hπ,hfix⟩ := Diagram.permutation_over_root hsize w.diagram z.diagram r w.rootIndex
    w.root (by rw [hb]; exact z.root)
  have hπval : ∀ x, π (w.diagram x) = z.diagram x := fun x =>
    congrArg (fun t : Diagram M I => t x) hπ
  have hdπ : w.condition.permute π = z.condition :=
    CohenForcing.Condition.permute_eq_of_pullback_eq _ _ π hπval
      w.condition z.condition w.supported z.supported hd
  have hπfix : π ∈ SupportFilter.Fix r.range := (SupportFilter.mem_Fix _ _).mpr hfix
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hm := (S.eq_symmetry π ((w.condition,w.diagram) : Poset M I κ)
    τ.name (C (w.diagram w.labelIndex))).mp w.represents
  have hplaced : S.atomic.EqF ((z.condition,z.diagram) : Poset M I κ)
      τ.name (C (z.diagram z.labelIndex)) := by
    dsimp only [S] at hm
    rw [move_coe] at hm
    simpa only [permute,hdπ,hπ,τ.fixed π hπfix,hC π hπfix,hπval,hx] using hm
  have heq := S.atomic.eq_trans hplaced (S.atomic.eq_symm z.represents)
  apply (LocalQuotient.ofName_eq F τ σ).mpr
  refine ⟨z.condition.restrict r.range,F.lower (z.condition.le_restrict _) z.mem,?_⟩
  have hsup : ∀ π ∈ SupportFilter.Fix r.range, ∀ i : Fin 2,
      π • (![τ.name,σ.name] : Fin 2 → S.Name) i = ![τ.name,σ.name] i := by
    intro π hπ i
    fin_cases i
    · exact τ.fixed π hπ
    · exact σ.fixed π hπ
  exact forces_at_supporting_root hμ hsize hmerger (.equal 0 1) ![τ.name,σ.name]
    r z.diagram ⟨z.rootIndex,z.root⟩ hsup z.condition (by
      simpa only [Forces,AtomicData.forceFormula_equal,Matrix.cons_val_zero,
        Matrix.cons_val_one] using heq)

end LocalWitness

/-- Local quotient values actually represented by a member of the specified
family at a stronger diagram. This is a subcollection of the unrestricted
local quotient, not a replacement definition for eligible E-classes. -/
def LocallyRepresented (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (C : I → (system (M := M) hμ).Name) :=
  {a : LocalQuotient (c := c) hμ F r // ∃ τ : LocalName hμ c r,
    LocalQuotient.ofName F τ = a ∧ Nonempty (LocalWitness hμ F r C τ)}

instance (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (C : I → (system (M := M) hμ).Name) :
    Small.{u} (LocallyRepresented (c := c) hμ F r C) := inferInstanceAs
  (Small.{u} {a : LocalQuotient (c := c) hμ F r // ∃ τ : LocalName hμ c r,
    LocalQuotient.ofName F τ = a ∧ Nonempty (LocalWitness hμ F r C τ)})

/-- The record argument bounds the entire represented collection, not
merely a preselected list of representatives. No genericity of F is used
in this coding bound. To apply it to D_F(r), eligibility still has to be
shown to give one of these witnesses. -/
theorem locallyRepresented_cardinal_le [Infinite M] [Infinite I]
    (hpower : μ ^ Cardinal.aleph0 = μ) (hcard : Cardinal.mk M ≤ μ)
    (hκ : Cardinal.mk κ ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (C : I → (system (M := M) hμ).Name)
    (hC : ∀ π ∈ SupportFilter.Fix r.range, ∀ j, π • C j = C (π j)) :
    Cardinal.mk (Shrink.{u} (LocallyRepresented (c := c) hμ F r C)) ≤ μ := by
  let A := LocallyRepresented (c := c) hμ F r C
  let repr (a : A) : LocalName hμ c r := a.property.choose
  have heq (a : A) : LocalQuotient.ofName F (repr a) = a.val := a.property.choose_spec.1
  let witness (a : A) : LocalWitness hμ F r C (repr a) :=
    a.property.choose_spec.2.some
  let code (a : A) : LocalRecord (M := M) (κ := κ) := (witness a).record
  have hinj : Function.Injective code := by
    intro a b h
    apply Subtype.ext
    rw [← heq a,← heq b]
    exact LocalWitness.equal_of_record_eq hsize hmerger hC (witness a) (witness b) h
  have hsmall : Cardinal.mk (Shrink.{u} A) ≤ Cardinal.mk (LocalRecord (M := M) (κ := κ)) :=
    Cardinal.mk_le_of_injective (hinj.comp (equivShrink A).symm.injective)
  apply hsmall.trans
  change Cardinal.mk (M × M × CohenForcing.Condition M κ) ≤ μ
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  have hcondition := CohenForcing.Condition.cardinal_le hμ hpower hcard hκ
  exact (mul_le_mul' hcard
    ((mul_le_mul' hcard hcondition).trans_eq (Cardinal.mul_eq_self hμ))).trans_eq
      (Cardinal.mul_eq_self hμ)

end
end PartitionConsistency.ProductForcing


/-! ## Class -/


namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Every separation name is a normalization over the bounding name. -/
theorem separate_bounded {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+1)) :
    (S.separate σ v φ).raw ⊆ S.subsetBound σ := by
  intro z hz
  change z ∈ S.collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (S.separationTest σ v φ) at hz
  obtain ⟨i,p,_,he⟩ := (S.mem_collectRaw _ _ _).mp hz
  exact (S.mem_collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (fun _ _ => True) _).mpr ⟨i,p,True.intro,he⟩

private theorem separate_move_le {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (g : Γ) :
    (g • S.separate σ v φ).raw ⊆ (S.separate (g • σ) (fun i => g • v i) φ).raw := by
  intro z hz
  obtain ⟨ν,a,he,rfl⟩ := mem_mapConditions_iff.mp hz
  change ZFSet.pair ν a ∈ S.collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (S.separationTest σ v φ) at he
  obtain ⟨i,p,hi,rfl,rfl⟩ := (S.edge_collectRaw _ _ _ _).mp he
  obtain ⟨j,hj⟩ := S.entry_permute g σ i
  change ZFSet.pair (mapConditions (S.action.actCode g) (σ.child i.property).raw)
    (S.action.actCode g (S.code p)) ∈ S.collectRaw
      (fun j : Edges (g • σ).raw => (g • σ).child j.property)
      (S.separationTest (g • σ) (fun i => g • v i) φ)
  apply (S.mem_collectRaw _ _ _).mpr
  refine ⟨j,S.move g p,⟨?_,?_⟩,?_⟩
  · change S.atomic.MemF (S.move g p) ((g • σ).child j.property) (g • σ)
    rw [hj]
    exact (S.mem_symmetry g p _ σ).mp hi.1
  · change S.Forces (Fin.snoc (fun i => g • v i) ((g • σ).child j.property)) (S.move g p) φ
    rw [hj]
    have hv : (fun k => g • Fin.snoc v (σ.child i.property) k) =
        Fin.snoc (fun i => g • v i) (g • σ.child i.property) := by
      ext i
      refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp
    simpa only [hv] using (S.forces_symmetry g φ _ p).mp hi.2
  · rw [hj,Name.smul_val,S.actCode_code]

/-- Literal covariance, not only fixedness, of the canonical Separation
name. The very same formula is used at the moved parameter tuple. -/
theorem separate_move {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (g : Γ) :
    g • S.separate σ v φ = S.separate (g • σ) (fun i => g • v i) φ := by
  apply Name.ext
  apply le_antisymm (S.separate_move_le σ v φ g)
  have hi := S.separate_move_le (g • σ) (fun i => g • v i) φ g⁻¹
  have hv : (fun i => g⁻¹ • g • v i) = v := by ext; simp
  rw [hv] at hi
  simp only [inv_smul_smul] at hi
  have hh := mapConditions_mono (S.action.actCode g) hi
  change (g • (g⁻¹ • S.separate (g • σ) (fun i => g • v i) φ)).raw ⊆
    (g • S.separate σ v φ).raw at hh
  simpa only [smul_inv_smul] using hh

/-- The canonical name for {y ∈ A | (x,y) ∈ E}.  No equivalence-relation
axiom is needed to construct this set. -/
def relationClass (A E x : S.Name) : S.Name :=
  S.separate A ![E,x] (SetLanguage.edge 0 1 2)

theorem mem_relationClass (A E x y : S.Name) (p : P) :
    S.atomic.MemF p y (S.relationClass A E x) ↔
      S.atomic.MemF p y A ∧ S.App p E x y := by
  rw [relationClass,S.mem_separate,S.forces_edge]
  rfl

theorem relationClass_bounded (A E x : S.Name) :
    (S.relationClass A E x).raw ⊆ S.subsetBound A :=
  S.separate_bounded A ![E,x] (SetLanguage.edge 0 1 2)

theorem relationClass_move (A E x : S.Name) (g : Γ) :
    g • S.relationClass A E x = S.relationClass (g • A) (g • E) (g • x) := by
  rw [relationClass,S.separate_move,relationClass]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem relationClass_congr {p : P} {A A' E E' x x' : S.Name}
    (hA : S.atomic.EqF p A A') (hE : S.atomic.EqF p E E')
    (hx : S.atomic.EqF p x x') :
    S.atomic.EqF p (S.relationClass A E x) (S.relationClass A' E' x') := by
  apply S.eq_of_same_members
  intro y q hqp
  rw [S.mem_relationClass,S.mem_relationClass]
  exact and_congr (S.atomic.mem_congr (S.atomic.eq_refl q y) (S.atomic.eq_mono hqp hA))
    (S.app_congr (S.atomic.eq_mono hqp hE) (S.atomic.eq_mono hqp hx) (S.atomic.eq_refl q y))

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetLanguage

/-- τ is precisely the E-class of x relative to A, expanded in pure
first-order membership syntax. Slots are τ,A,E,x. -/
def classOfFormula : Formula 4 :=
  .all ((Formula.mem 4 0).iff ((Formula.mem 4 1).conj (edge 2 3 4)))

def classOf {n} (τ A E x : Fin n) : Formula n :=
  Formula.rename ![τ,A,E,x] classOfFormula

/-- τ is the E-class of *some element of A*. Slots are τ,A,E. -/
def isClassFormula : Formula 3 :=
  .ex ((Formula.mem 3 1).conj (classOf 0 1 2 3))

def isClass {n} (τ A E : Fin n) : Formula n :=
  Formula.rename ![τ,A,E] isClassFormula

end PartitionConsistency.SetLanguage

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_classOf {n} (v : Fin n → S.Name) (p : P) (τ A E x : Fin n) :
    S.Forces v p (SetLanguage.classOf τ A E x) ↔
      S.atomic.EqF p (v τ) (S.relationClass (v A) (v E) (v x)) := by
  simp only [Forces,SetLanguage.classOf,SetLanguage.classOfFormula,Formula.iff,
    S.atomic.forceFormula_rename S.atomic_regular,S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_edge]
  constructor
  · intro h
    apply S.eq_of_same_members
    intro y q hqp
    rw [S.mem_relationClass]
    exact ⟨(h y).1 q hqp,(h y).2 q hqp⟩
  · intro he y
    constructor
    · intro q hqp hy
      exact (S.mem_relationClass _ _ _ y q).mp
        ((S.atomic.mem_congr (S.atomic.eq_refl q y) (S.atomic.eq_mono hqp he)).mp hy)
    · intro q hqp hy
      exact (S.atomic.mem_congr (S.atomic.eq_refl q y) (S.atomic.eq_mono hqp he)).mpr
        ((S.mem_relationClass _ _ _ y q).mpr hy)

theorem forces_isClass {n} (v : Fin n → S.Name) (p : P) (τ A E : Fin n) :
    S.Forces v p (SetLanguage.isClass τ A E) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name,
        S.atomic.MemF r x (v A) ∧
        S.atomic.EqF r (v τ) (S.relationClass (v A) (v E) x) := by
  change S.atomic.ForceFormula v p _ ↔ _
  rw [SetLanguage.isClass,S.atomic.forceFormula_rename S.atomic_regular,
    SetLanguage.isClassFormula,ForcingQuotient.AtomicData.forceFormula_ex]
  simp only [ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,forces_classOf,Fin.snoc]
  rfl

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The actual canonical class of a label, supported by any diagram
supporting E and containing that label's index. -/
def labelClass (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (j : I) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system hμ).relationClass (labelSet hμ c) E (label hμ c j)

theorem labelClass_move (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (π : Equiv.Perm I) (j : I) :
    π • labelClass hμ c E j = labelClass hμ c (π • E) (π j) := by
  simp only [labelClass,SymmetricSystem.relationClass_move,smul_labelSet,smul_label]

def localLabelClass (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (j : I) (hj : j ∈ r.range) :
    LocalName hμ c r :=
  ⟨⟨labelClass hμ c E j,(system hμ).relationClass_bounded _ _ _⟩,by
    intro π hπ
    rw [labelClass_move,hE π hπ,(SupportFilter.mem_Fix _ _).mp hπ j hj]⟩

theorem forces_localLabelClass_isClass (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (j : I) (hj : j ∈ r.range)
    (p : Poset M I κ) :
    (system hμ).Forces ![(localLabelClass hμ c r E hE j hj).name,labelSet hμ c,E] p
      (SetLanguage.isClass 0 1 2) := by
  apply ((system hμ).forces_isClass _ _ _ _ _).mpr
  intro q hqp
  exact ⟨q,le_rfl,label hμ c j,label_mem_labelSet hμ c j q,(system hμ).atomic.eq_refl _ _⟩

end
end PartitionConsistency.ProductForcing


/-! ## Availability -/

namespace PartitionConsistency.DiagramOrder.LeftDivOrder
universe u
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

/-- Left multiplication, unlike right multiplication, preserves and reflects
left divisibility in a left-cancellative monoid. -/
theorem mul_le_mul_left_iff (n x y : LeftDivOrder M) :
    n * x ≤ n * y ↔ x ≤ y := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,mul_left_cancel (by simpa only [mul_assoc] using hz)⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z,mul_assoc n x z⟩

theorem le_mul_right (x y : LeftDivOrder M) : x ≤ x * y := ⟨y,rfl⟩

/-- Conditional joins commute with left multiplication. This uses the
least-upper-bound property, not a global lattice structure. -/
theorem isLUB_mul_left (n : LeftDivOrder M) {x y j : LeftDivOrder M}
    (h : IsLUB {x,y} j) : IsLUB {n*x,n*y} (n*j) := by
  have hx : x ≤ j := h.1 (by simp)
  have hy : y ≤ j := h.1 (by simp)
  constructor
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (mul_le_mul_left_iff n x j).mpr hx
    · have he : z = n*y := Set.mem_singleton_iff.mp hz
      subst z
      exact (mul_le_mul_left_iff n y j).mpr hy
  · intro z hz
    have hnx : n*x ≤ z := hz (by simp)
    have hny : n*y ≤ z := hz (by simp)
    obtain ⟨w,rfl⟩ := (le_mul_right n x).trans hnx
    exact (mul_le_mul_left_iff n j w).mpr (h.2 (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [hz]
        exact (mul_le_mul_left_iff n x w).mp hnx
      · rw [Set.mem_singleton_iff.mp hz]
        exact (mul_le_mul_left_iff n y w).mp hny))

/-- The right-cone formulation of a conditional join. -/
theorem isLUB_cones {x y j : LeftDivOrder M} (h : IsLUB {x,y} j)
    (z : LeftDivOrder M) : x ≤ z ∧ y ≤ z ↔ j ≤ z := by
  constructor
  · rintro ⟨hx,hy⟩
    apply h.2
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact hx
    · rwa [Set.mem_singleton_iff.mp hw]
  · intro hz
    exact ⟨(h.1 (by simp)).trans hz,(h.1 (by simp)).trans hz⟩

end PartitionConsistency.DiagramOrder.LeftDivOrder

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
open DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- Strengthening reverses containment of ranges but preserves the monoid
left-divisibility order of subdiagram indices. -/
theorem sub_mono (r : Diagram M I) {n m : LeftDivOrder M} (h : n ≤ m) :
    r.sub n ≤ r.sub m := by
  obtain ⟨z,hz⟩ := h
  exact ⟨z,(sub_sub r n z).trans (congrArg r.sub hz)⟩

theorem self_le_sub (r : Diagram M I) (n : M) : r ≤ r.sub n := ⟨n,rfl⟩

theorem range_inter_of_isLUB (r : Diagram M I) {n m k : LeftDivOrder M}
    (h : IsLUB {n,m} k) :
    (r.sub n).range ∩ (r.sub m).range = (r.sub k).range := by
  apply range_inter_sub
  intro z
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    obtain ⟨w,hw⟩ := (LeftDivOrder.isLUB_cones h z).mp ⟨⟨x,hx.symm⟩,⟨y,hy.symm⟩⟩
    exact ⟨w,hw.symm⟩
  · rintro ⟨w,hw⟩
    obtain ⟨hx,hy⟩ := (LeftDivOrder.isLUB_cones h z).mpr ⟨w,hw.symm⟩
    obtain ⟨x,hx⟩ := hx
    obtain ⟨y,hy⟩ := hy
    exact ⟨⟨x,hx.symm⟩,⟨y,hy.symm⟩⟩

end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.LocalDiagramSystem
universe u v
open DiagramForcing DiagramOrder
variable (M I : Type u) [LeftCancelMonoid M] [IsConical M]

/-- A covariant diagram system with injective restriction and the actual
support-intersection property. This is purely diagrammatic infrastructure;
no counting, choice or partition principle is part of this definition. -/
structure System where
  Obj : Diagram M I → Type v
  restrict {r s : Diagram M I} : s ≤ r → Obj r → Obj s
  restrict_refl {r : Diagram M I} (x : Obj r) : restrict le_rfl x = x
  restrict_comp {r s t : Diagram M I} (hsr : s ≤ r) (hts : t ≤ s) (x : Obj r) :
    restrict hts (restrict hsr x) = restrict (hts.trans hsr) x
  injective {r s : Diagram M I} (hsr : s ≤ r) : Function.Injective (restrict hsr)
  intersection (p s₀ s₁ t : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (ht₀ : t ≤ s₀) (ht₁ : t ≤ s₁)
    (x₀ : Obj s₀) (x₁ : Obj s₁) (heq : restrict ht₀ x₀ = restrict ht₁ x₁) :
    ∃ x : Obj p, restrict hs₀ x = x₀ ∧ restrict hs₁ x = x₁

variable {M I}
namespace System
variable (D : System.{u,v} M I)

/-- Availability is existence of the same symbolic element at the specified
subdiagram. It is not an independently assigned ideal. -/
def Available (r : Diagram M I) (x : D.Obj r) (n : M) : Prop :=
  ∃ y : D.Obj (r.sub n), D.restrict (r.self_le_sub n) y = x

@[simp] theorem available_one (r : Diagram M I) (x : D.Obj r) : D.Available r x 1 := by
  have h : ∀ (s : Diagram M I) (hs : r ≤ s), s = r →
      ∃ y : D.Obj s, D.restrict hs y = x := by
    intro s hs he
    subst s
    exact ⟨x,D.restrict_refl x⟩
  exact h (r.sub 1) (r.self_le_sub 1) (r.sub_one)

/-- Retention of representatives under two successive inclusions. -/
theorem available_lower {r : Diagram M I} {x : D.Obj r}
    {n m : LeftDivOrder M} (hnm : n ≤ m) (hm : D.Available r x m) :
    D.Available r x n := by
  obtain ⟨y,hy⟩ := hm
  refine ⟨D.restrict (r.sub_mono hnm) y,?_⟩
  rw [D.restrict_comp]
  exact hy

/-- Availability at two roots descends to their exact intersection. -/
theorem available_join {r : Diagram M I} {x : D.Obj r}
    {n m k : LeftDivOrder M} (hn : D.Available r x n) (hm : D.Available r x m)
    (hjoin : IsLUB {n,m} k) : D.Available r x k := by
  obtain ⟨y,hy⟩ := hn
  obtain ⟨z,hz⟩ := hm
  have hn : n ≤ k := hjoin.1 (by simp)
  have hm : m ≤ k := hjoin.1 (by simp)
  obtain ⟨w,hw,_⟩ := D.intersection (r.sub k) (r.sub n) (r.sub m) r
    (r.sub_mono hn) (r.sub_mono hm) (r.range_inter_of_isLUB hjoin)
    (r.self_le_sub n) (r.self_le_sub m) y z (hy.trans hz.symm)
  refine ⟨w,?_⟩
  rw [← D.restrict_comp (r.sub_mono hn) (r.self_le_sub n),hw,hy]

/-- Source availability-ideal lemma, common to symbolic elements and labels.
The proof uses the already specified inclusion and intersection maps. -/
def availability (r : Diagram M I) (a : M) (x : D.Obj r) :
    ConeIdeal (show LeftDivOrder M from a) where
  carrier := {n | n ≤ a ∧ D.Available r x n}
  nonempty := ⟨1,bot_le,D.available_one r x⟩
  bounded := fun _ h => h.1
  lower := by
    intro n m hnm hm
    exact ⟨hnm.trans hm.1,D.available_lower hnm hm.2⟩
  join_closed := by
    intro n m k hn hm hk
    exact ⟨(LeftDivOrder.isLUB_cones hk a).mp ⟨hn.1,hm.1⟩,
      D.available_join hn.2 hm.2 hk⟩

@[simp] theorem mem_availability (r : Diagram M I) (a : M) (x : D.Obj r)
    (n : LeftDivOrder M) : n ∈ (D.availability r a x).carrier ↔ n ≤ a ∧ D.Available r x n :=
  Iff.rfl

end System

/-- Label ranges form the literal system underlying the label availability
ideals. Restriction is simply inclusion, not a choice of representatives. -/
def labelSystem : System.{u,u} M I where
  Obj r := r.range
  restrict hsr j := ⟨j.val,Diagram.range_antitone hsr j.property⟩
  restrict_refl _ := rfl
  restrict_comp _ _ _ := rfl
  injective := by
    intro r s hsr x y h
    exact Subtype.ext (congrArg (fun z : s.range => z.val) h)
  intersection p s₀ s₁ t hs₀ hs₁ hinter ht₀ ht₁ x₀ x₁ heq := by
    have hx : x₀.val = x₁.val := congrArg Subtype.val heq
    have hp : x₀.val ∈ p.range := by
      rw [← hinter]
      exact ⟨x₀.property,hx ▸ x₁.property⟩
    exact ⟨⟨x₀.val,hp⟩,rfl,Subtype.ext hx⟩

end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

/-- The normalized names and the proved support descent instantiate the
intersection calculus. Eligibility as an E-class is a later subcollection. -/
def allLocalSystem [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) :
    LocalDiagramSystem.System.{u,u+1} M I where
  Obj := LocalQuotient (c := c) hμ F
  restrict := LocalQuotient.restrict F
  restrict_refl := LocalQuotient.restrict_refl F
  restrict_comp := LocalQuotient.restrict_restrict F
  injective := LocalQuotient.restrict_injective F hsize hmerger
  intersection := LocalQuotient.intersection F hcard hsize hmerger

end
end PartitionConsistency.ProductForcing

end OAI
