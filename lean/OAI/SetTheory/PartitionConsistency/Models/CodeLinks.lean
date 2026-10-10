import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.OrdinalCodes

namespace OAI

/-! ## CodeOrdinal -/

/-! Actual ordinal names for the persistent least-code ordering on a single
component. All names have the initial diagram as a support. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
section IndexCoding
variable {q : Diagram M I} {v : Vertex q} (C : Vertex.Chain v)

/-- Small carrier for the prescribed ground wellordering; no rearrangement
of code order occurs when conditions or components move. -/
def Index := Shrink.{u} (ChainCode hμ c C)

def code : Index hμ c C ≃ ChainCode hμ c C := (equivShrink (ChainCode hμ c C)).symm

instance : LinearOrder (Index hμ c C) :=
  show LinearOrder (Shrink.{u} (ChainCode hμ c C)) from
  IsWellOrder.linearOrder (OrderAssignment.smallRel (@WellOrderingRel (ChainCode hμ c C)))

instance : IsWellOrder (Index hμ c C) (· < ·) :=
  inferInstanceAs (IsWellOrder (Shrink.{u} (ChainCode hμ c C))
    (OrderAssignment.smallRel (@WellOrderingRel (ChainCode hμ c C))))

end IndexCoding

variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

/-- The old tail fixer viewed faithfully as coordinate permutations. -/
def tailGroup : Subgroup (Equiv.Perm I) :=
  (C.tailFixer hj).map ((Vertex.RootGroup q).subtype.comp (Vertex.componentStabilizer hj v).subtype)

omit [Infinite M] [Infinite I] in
theorem tailGroup_mem (π : Equiv.Perm I) : π ∈ tailGroup hj C ↔
    ∃ k : C.tailFixer hj, k.val.val.val = π := by
  change (∃ k ∈ C.tailFixer hj, k.val.val = π) ↔ _
  constructor
  · rintro ⟨k,hk,he⟩; exact ⟨⟨k,hk⟩,he⟩
  · rintro ⟨k,he⟩; exact ⟨k.val,k.property,he⟩

omit [Infinite M] [Infinite I] in
theorem root_le_tailGroup : SupportFilter.Fix v.diagram.range ≤ tailGroup hj C := by
  intro π hπ
  have hr : v.diagram ≤ q := ⟨v.index,v.root⟩
  have hπq : π ∈ Vertex.RootGroup q := by
    apply (SupportFilter.mem_Fix _ _).mpr
    intro j hj
    exact (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hr hj)
  let g : Vertex.RootGroup q := ⟨π,hπq⟩
  have hg (j : I) (hj : j ∈ (C.vertex 0).diagram.range) : g.val j = j := by
    rw [C.first] at hj
    exact (SupportFilter.mem_Fix _ _).mp hπ j hj
  let k : Vertex.componentStabilizer hj v := ⟨g,C.fixes_mem_stabilizer hj g 0 hg⟩
  exact (tailGroup_mem hj C π).mpr ⟨⟨k,0,hg⟩,rfl⟩

include hcard in
omit [Infinite M] [Infinite I] in
theorem tailGroup_supported : tailGroup hj C ∈ (system (M := M) (I := I) (κ := κ) hμ).filter :=
  ⟨v.diagram.range,(Diagram.cardinal_range v.diagram).trans_le hcard,root_le_tailGroup hj C⟩

/-- A small index is selected precisely when its actual ground name code is
persistently least in its eventual-equality class. -/
def IsSelected (a : Index hμ c C) (d : CohenForcing.Condition I κ) : Prop :=
  Selected hμ c hcard hsize hmerger hj E hE C (code hμ c C a) d

theorem isSelected_mono {a : Index hμ c C} {d e : CohenForcing.Condition I κ}
    (hed : e ≤ d) (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d) :
    IsSelected hμ c hcard hsize hmerger hj E hE C a e :=
  selected_mono hμ c hcard hsize hmerger hj E hE C hed ha

theorem isSelected_covariance (π : Equiv.Perm I) (hπ : π ∈ tailGroup hj C)
    (a : Index hμ c C) (d : CohenForcing.Condition I κ)
    (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d) :
    IsSelected hμ c hcard hsize hmerger hj E hE C a (d.permute π) := by
  obtain ⟨k,rfl⟩ := (tailGroup_mem hj C π).mp hπ
  exact (selected_covariance hμ c hcard hsize hmerger hj E hE C k d (code hμ c C a)).mpr ha

/-- The von Neumann rank of a selected code, not a check-name for its
predetermined ground index. -/
def ordinalRank (a : Index hμ c C) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  CohenSelection.rank hμ (IsSelected hμ c hcard hsize hmerger hj E hE C)
    (tailGroup hj C) (tailGroup_supported hμ hcard hj C)
    (isSelected_covariance hμ c hcard hsize hmerger hj E hE C) a

/-- The similarly supported total order-type name. -/
def ordinalType : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  CohenSelection.orderType hμ (IsSelected hμ c hcard hsize hmerger hj E hE C)
    (tailGroup hj C) (tailGroup_supported hμ hcard hj C)
    (isSelected_covariance hμ c hcard hsize hmerger hj E hE C)

theorem ordinalType_decide (d : CohenForcing.Condition I κ) :
    ∃ e, e ≤ d ∧ ∃ θ : Ordinal.{u}, θ ≤ (ordinalType hμ c hcard hsize hmerger hj E hE C).raw.rank ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet) :=
  CohenSelection.orderType_decide hμ hsize hmerger _ _ _ _ v.diagram (root_le_tailGroup hj C) d

theorem ordinalRank_eq_iff (a b : Index hμ c C) (d : CohenForcing.Condition I κ)
    (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d)
    (hb : IsSelected hμ c hcard hsize hmerger hj E hE C b d) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalRank hμ c hcard hsize hmerger hj E hE C a)
      (ordinalRank hμ c hcard hsize hmerger hj E hE C b) ↔ a = b :=
  CohenSelection.rank_eq_iff hμ _ _ _ _ v.diagram a b d ha hb

theorem ordinalRank_decide (a : Index hμ c C) (d : CohenForcing.Condition I κ)
    (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet)) :
    ∃ e, e ≤ d ∧ ∃ β : Set.Iio θ,
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hj E hE C a) (Name.check β.val.toZFSet) :=
  CohenSelection.rank_decide hμ hsize hmerger _ _ _ _ v.diagram
    (root_le_tailGroup hj C) a d ha θ hθ

theorem member_ordinalRank (d : CohenForcing.Condition I κ) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet)) (β : Set.Iio θ) :
    ∃ e, e ≤ d ∧ ∃ a : Index hμ c C,
      IsSelected hμ c hcard hsize hmerger hj E hE C a e ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hj E hE C a) (Name.check β.val.toZFSet) :=
  CohenSelection.member_rank hμ hsize hmerger
    (IsSelected hμ c hcard hsize hmerger hj E hE C)
    (tailGroup hj C) (tailGroup_supported hμ hcard hj C)
    (isSelected_covariance hμ c hcard hsize hmerger hj E hE C) v.diagram
    (root_le_tailGroup hj C) (fun h ha => isSelected_mono hμ c hcard hsize hmerger hj E hE C h ha)
    d θ hθ β

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## CodeLink -/

/-! Eventual code links at arbitrary vertices, rather than only at the
chosen first vertex. This is the local forcing form of the canonical
identifications in one component. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- At every sufficiently late chain vertex a code entry equals the given
name at w, and that vertex actually is a successor of w. -/
def Links (d : CohenForcing.Condition I κ) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name) (a : ChainCode hμ c C) : Prop :=
  ∃ N, ∀ i, N ≤ i → Nonempty (w.Arrow (C.vertex i)) ∧
    (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) (a i).name τ

variable {hμ c C}

omit [Infinite M] [Infinite I] in
theorem links_mono {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a : ChainCode hμ c C}
    (hed : e ≤ d) (h : Links hμ c C d w τ a) : Links hμ c C e w τ a := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => ⟨(hN i hi).1,(system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (e,w.diagram) ≤ (d,w.diagram) from ⟨hed,le_rfl⟩))
    (hN i hi).2⟩⟩

omit [Infinite M] [Infinite I] in
theorem links_common {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a : ChainCode hμ c C}
    (h : Links hμ c C d w τ a) : Vertex.Common v w := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨f⟩ := (hN N le_rfl).1
  obtain ⟨g⟩ := C.increasing 0 N (Nat.zero_le _)
  exact ⟨C.vertex N,by simpa only [C.first] using (show Nonempty ((C.vertex 0).Arrow (C.vertex N)) from ⟨g⟩),⟨f⟩⟩

omit [Infinite M] [Infinite I] in
theorem links_congr {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a : ChainCode hμ c C}
    (h : Links hμ c C d w τ a)
    (he : (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ) :
    Links hμ c C d w σ a := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => ⟨(hN i hi).1,(system hμ).atomic.eq_trans (hN i hi).2 he⟩⟩

omit [Infinite M] [Infinite I] in
theorem links_same {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a b : ChainCode hμ c C}
    (h : Links hμ c C d w τ a) (hs : Same hμ c C d a b) : Links hμ c C d w τ b := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := hs
  refine ⟨max N L,fun i hi => ?_⟩
  obtain ⟨hf,he⟩ := hN i ((le_max_left _ _).trans hi)
  obtain ⟨f⟩ := hf
  refine ⟨⟨f⟩,(system hμ).atomic.eq_trans ?_ he⟩
  exact (system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (d,(C.vertex i).diagram) from
      ⟨le_rfl,⟨f.index,f.diagram⟩⟩))
    ((system hμ).atomic.eq_symm (hL i ((le_max_right _ _).trans hi)))

include hsize hmerger in
/-- The common code comparison is exactly forced equality, at any one
vertex at which both codes have linked representatives. -/
theorem links_eq_iff_same {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a b : ChainCode hμ c C}
    (ha : Links hμ c C d w τ a) (hb : Links hμ c C d w σ b) :
    (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ Same hμ c C d a b := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hb
  have he (i : ℕ) (hn : N ≤ i) (hl : L ≤ i) :
      (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔
        (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name := by
    obtain ⟨f⟩ := (hN i hn).1
    have hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
    constructor
    · intro h
      exact eq_at_root hμ hsize hmerger _ _ (C.vertex i).diagram w.diagram hf
        (a i).fixed (b i).fixed d
        ((system hμ).atomic.eq_trans (hN i hn).2 ((system hμ).atomic.eq_trans h
          ((system hμ).atomic.eq_symm (hL i hl).2)))
    · intro h
      have h' := (system hμ).atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (d,(C.vertex i).diagram) from ⟨le_rfl,hf⟩)) h
      exact (system hμ).atomic.eq_trans ((system hμ).atomic.eq_symm (hN i hn).2)
        ((system hμ).atomic.eq_trans h' (hL i hl).2)
  constructor
  · intro h
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)
      ((le_max_right _ _).trans hi)).mp h⟩
  · rintro ⟨K,hK⟩
    exact (he (max (max N L) K) ((le_max_left N L).trans (le_max_left _ _))
      ((le_max_right N L).trans (le_max_left _ _))).mpr (hK _ (le_max_right _ _))

variable (hμ c C)

/-- A representation in a principal quotient implies actual forced code
links. There is no genericity assumption on that principal quotient. -/
theorem links_of_represents_at (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (b : (D[principalFilter d]).Glued hj v)
    (ha : Represents hμ c hcard hsize hmerger hj E hE C (principalFilter d) a b)
    (w : Vertex q) (τ : LocalName hμ c w.diagram)
    (hτ : At hμ c hcard hsize hmerger hj E hE (principalFilter d) w τ.name b) :
    Links hμ c C d w τ.name a := by
  obtain ⟨hw,x,ρ,hρ,hx,hb⟩ := hτ
  have hρ' : ρ = τ := LocalName.ext hρ
  subst ρ
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := C.cofinal w hw
  refine ⟨max N L,fun i hi => ?_⟩
  let f : w.Arrow (C.vertex i) := hL.some.comp (C.increasing L i ((le_max_right _ _).trans hi)).some
  have hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  obtain ⟨hwi,y,σ,hσ,hy,hbi⟩ := hN i ((le_max_left _ _).trans hi)
  have hσ' : σ = a i := LocalName.ext hσ
  subst σ
  have hexy : (D[principalFilter d]).arrowMap hj f y = x := by
    apply (D[principalFilter d]).toGlued_injective hj v w hw
    rw [(D[principalFilter d]).toGlued_arrow hj v w (C.vertex i) hw hwi f y,hbi,hb]
  refine ⟨⟨f⟩,?_⟩
  apply ((localAtomic hμ w.diagram).eqG_principal d _ _).mp
  apply (LocalQuotient.ofName_eq (principalFilter d) ((a i).restrict hf) τ).mp
  calc
    LocalQuotient.ofName (principalFilter d) ((a i).restrict hf) =
        LocalQuotient.restrict (principalFilter d) hf y.val.val :=
      congrArg (LocalQuotient.restrict (principalFilter d) hf) hy
    _ = x.val.val := congrArg (fun z : (D[principalFilter d]).vertexFiber w => z.val.val) hexy
    _ = LocalQuotient.ofName (principalFilter d) τ := hx.symm

/-- A linked local name is in the exact fiber, not merely eligible. The
bijective contraction maps certify the exact ideal. -/
theorem at_of_represents_links (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (b : (D[principalFilter d]).Glued hj v)
    (ha : Represents hμ c hcard hsize hmerger hj E hE C (principalFilter d) a b)
    (w : Vertex q) (τ : LocalName hμ c w.diagram) (hτ : Links hμ c C d w τ.name a) :
    At hμ c hcard hsize hmerger hj E hE (principalFilter d) w τ.name b := by
  have hw := links_common hτ
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hτ
  let i := max N L
  obtain ⟨hwi,y,σ,hσ,hy,hbi⟩ := hN i (le_max_left _ _)
  have hσ' : σ = a i := LocalName.ext hσ
  subst σ
  obtain ⟨⟨f⟩,he⟩ := hL i (le_max_right _ _)
  have hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  refine ⟨hw,(D[principalFilter d]).arrowMap hj f y,τ,rfl,?_,?_⟩
  · have het : LocalQuotient.ofName (principalFilter d) ((a i).restrict hf) =
        LocalQuotient.ofName (principalFilter d) τ :=
      (LocalQuotient.ofName_eq (principalFilter d) _ _).mpr
        (((localAtomic hμ w.diagram).eqG_principal d _ _).mpr he)
    exact het.symm.trans (congrArg (LocalQuotient.restrict (principalFilter d) hf) hy)
  · exact ((D[principalFilter d]).toGlued_arrow hj v w (C.vertex i) hw hwi f y).trans hbi

/-- Extraction of the actual stable ideal from a persistent working code
and a literal name linked to it at w. -/
theorem links_stable (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a)
    (w : Vertex q) (τ : LocalName hμ c w.diagram) (hτ : Links hμ c C d w τ.name a) :
    (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)
        (SetLanguage.isClass 0 1 2) ∧
      ∀ e, e ≤ d → forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index τ = w.ideal := by
  have hat (e : CohenForcing.Condition I κ) (hed : e ≤ d) :
      ∃ x : (D[principalFilter e]).vertexFiber w,
        LocalQuotient.ofName (principalFilter e) τ = x.val.val := by
    obtain ⟨b,hb⟩ := ha e hed
    obtain ⟨_,x,σ,hσ,hx,_⟩ := at_of_represents_links hμ c hcard hsize hmerger hj E hE C
      e a b hb w τ (links_mono hed hτ)
    have he : σ = τ := LocalName.ext hσ
    exact ⟨x,he ▸ hx⟩
  constructor
  · obtain ⟨x,hx⟩ := hat d le_rfl
    have he : EligibleName hμ c (principalFilter d) w.diagram E τ := by
      apply (eligible_ofName hμ c (principalFilter d) w.diagram E τ).mp
      rw [hx]
      exact x.val.property.2
    obtain ⟨e,he,hel⟩ := he
    exact (system hμ).atomic.forceFormula_mono
      (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (e,w.diagram) from
        ⟨(mem_principalFilter d e).mp he,le_rfl⟩)) hel
  · intro e hed
    obtain ⟨x,hx⟩ := hat e hed
    have hi := x.property
    rw [eligibleSystem_availability_eq hμ c hcard hsize hmerger E hE
      (principalFilter e) w.diagram w.index w.root x.val] at hi
    change (allLocalSystem (c := c) hμ hcard hsize hmerger (principalFilter e)).availability
      w.diagram w.index (LocalQuotient.ofName (principalFilter e) τ) = w.ideal
    rw [hx]
    exact hi

/-- Stable exact membership at any vertex in the component gives a code
which works at every stronger Cohen condition and remains linked there. -/
theorem exists_linked_working_of_stable (d : CohenForcing.Condition I κ)
    (w : Vertex q) (hw : Vertex.Common v w) (τ : LocalName hμ c w.diagram)
    (hel : (system hμ).Forces ![τ.name,labelSet hμ c,E]
      ((d,w.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2))
    (hstable : ∀ e, e ≤ d →
      forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index τ = w.ideal) :
    ∃ a : ChainCode hμ c C, Works hμ c hcard hsize hmerger hj E hE C d a ∧
      Links hμ c C d w τ.name a := by
  have hex (e : CohenForcing.Condition I κ) (hed : e ≤ d) :
      ∃ x : (D[principalFilter e]).vertexFiber w,
        LocalQuotient.ofName (principalFilter e) τ = x.val.val :=
    exists_fiber_principal hμ c hcard hsize hmerger E hE e w τ
      ((system hμ).atomic.forceFormula_mono
        (WithTop.coe_le_coe.mpr (show (e,w.diagram) ≤ (d,w.diagram) from ⟨hed,le_rfl⟩)) hel)
      (hstable e hed)
  obtain ⟨x,hx⟩ := hex d le_rfl
  let b := (D[principalFilter d]).toGlued hj v w hw x
  obtain ⟨a,ha⟩ := exists_representing_code (C := C) (principalFilter d) b
  have hl := links_of_represents_at hμ c hcard hsize hmerger hj E hE C d a b ha w τ
    ⟨hw,x,τ,rfl,hx,rfl⟩
  refine ⟨a,?_,hl⟩
  intro e hed
  obtain ⟨x',hx'⟩ := hex e hed
  obtain ⟨N,hN⟩ := links_mono hed hl
  refine ⟨(D[principalFilter e]).toGlued hj v w hw x',N,fun i hi => ?_⟩
  obtain ⟨⟨f⟩,he⟩ := hN i hi
  let hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  obtain ⟨y,hy⟩ := (D[principalFilter e]).arrowMap_bijective hj f |>.2 x'
  have heq : LocalQuotient.ofName (principalFilter e) (a i) = y.val.val := by
    apply LocalQuotient.restrict_injective (principalFilter e) hsize hmerger hf
    have ht : LocalQuotient.ofName (principalFilter e) ((a i).restrict hf) =
        LocalQuotient.ofName (principalFilter e) τ :=
      (LocalQuotient.ofName_eq (principalFilter e) _ _).mpr
        (((localAtomic hμ w.diagram).eqG_principal e _ _).mpr he)
    exact ht.trans (hx'.trans
      (congrArg (fun z : (D[principalFilter e]).vertexFiber w => z.val.val) hy).symm)
  refine ⟨C.common i,y,a i,rfl,heq,?_⟩
  rw [← (D[principalFilter e]).toGlued_arrow hj v w (C.vertex i) hw (C.common i) f y,hy]

omit [Infinite M] [Infinite I] in
/-- Restriction along an actual contraction preserves the literal linked
representative. Both the condition and the code remain unchanged. -/
theorem links_restrict (d : CohenForcing.Condition I κ) {w z : Vertex q}
    (f : w.Arrow z) (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (a : ChainCode hμ c C) (h : Links hμ c C d z τ a) :
    Links hμ c C d w τ a := by
  obtain ⟨N,hN⟩ := h
  refine ⟨N,fun i hi => ?_⟩
  obtain ⟨⟨g⟩,he⟩ := hN i hi
  exact ⟨⟨f.comp g⟩,(system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (d,z.diagram) from
      ⟨le_rfl,⟨f.index,f.diagram⟩⟩)) he⟩

include hsize hmerger hj in
/-- Conversely a representative which is already supported on the smaller
successor diagram has the same link there, by local decision. -/
theorem links_descend (d : CohenForcing.Condition I κ) {w z : Vertex q}
    (f : w.Arrow z) (τ : LocalName hμ c z.diagram)
    (a : ChainCode hμ c C) (h : Links hμ c C d w τ.name a) :
    Links hμ c C d z τ.name a := by
  have hz := (links_common h).trans hj (Vertex.Common.of_arrow f)
  obtain ⟨L,⟨g⟩⟩ := C.cofinal z hz
  obtain ⟨N,hN⟩ := h
  refine ⟨max N L,fun i hi => ?_⟩
  let gi : z.Arrow (C.vertex i) := g.comp (C.increasing L i ((le_max_right _ _).trans hi)).some
  refine ⟨⟨gi⟩,?_⟩
  exact eq_at_root hμ hsize hmerger _ _ z.diagram w.diagram
    ⟨f.index,f.diagram⟩ (supported_mono hμ ⟨gi.index,gi.diagram⟩ _ (a i).fixed)
    τ.fixed d (hN i ((le_max_left _ _).trans hi)).2

/-- A working code has a normalized representative at EVERY vertex in its
component; this is not restricted to the first vertex of the chosen chain. -/
theorem working_linked (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a)
    (w : Vertex q) (hw : Vertex.Common v w) :
    ∃ τ : LocalName hμ c w.diagram, Links hμ c C d w τ.name a := by
  obtain ⟨b,hb⟩ := ha d le_rfl
  obtain ⟨x,hx⟩ := (D[principalFilter d]).toGlued_surjective hj v w hw b
  obtain ⟨τ,hτ⟩ := Quotient.mk'_surjective
    (s := localSetoid (c := c) hμ (principalFilter d) w.diagram) x.val.val
  exact ⟨τ,links_of_represents_at hμ c hcard hsize hmerger hj E hE C d a b hb w τ
    ⟨hw,x,τ,rfl,hτ,hx⟩⟩

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
