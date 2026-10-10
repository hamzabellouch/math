import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.QuotientTransport

namespace OAI

/-! ## TailCode -/

/-! Codes for actual symbolic classes along a component chain.  The
representing relation ignores a finite prefix and is covariant under each
eventual pointwise fixer, with the *same* code at the moved Cohen filter. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The ground code set in the paper: at position i a literal local
normalized name supported on the i-th chain diagram. -/
def ChainCode {q : Diagram M I} {v : Vertex q} (C : Vertex.Chain v) :=
  ∀ i, LocalName hμ c (C.vertex i).diagram

instance {q : Diagram M I} {v : Vertex q} (C : Vertex.Chain v) :
    Small.{u} (ChainCode hμ c C) := inferInstanceAs
  (Small.{u} (∀ i, LocalName hμ c (C.vertex i).diagram))

namespace ChainCode
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- A literal HS name represents a point of the glued component at w.  The
name, rather than its check-name code, is used in this predicate. -/
def At (F : GenericFilter (CohenForcing.Condition I κ)) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name) (b : (D[F]).Glued hj v) : Prop :=
  ∃ (hw : Vertex.Common v w) (x : (D[F]).vertexFiber w)
    (σ : LocalName hμ c w.diagram), σ.name = τ ∧
      LocalQuotient.ofName F σ = x.val.val ∧ (D[F]).toGlued hj v w hw x = b

/-- Eventual representation is explicitly insensitive to all entries in a
finite initial segment. -/
def Represents (F : GenericFilter (CohenForcing.Condition I κ))
    (a : ChainCode hμ c C) (b : (D[F]).Glued hj v) : Prop :=
  ∃ N, ∀ i, N ≤ i → At hμ c hcard hsize hmerger hj E hE F (C.vertex i) (a i).name b

variable {hμ c hcard hsize hmerger hj E hE C}

/-- A functioning name at one vertex has only one glued value. -/
theorem at_unique {F : GenericFilter (CohenForcing.Condition I κ)} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {b b' : (D[F]).Glued hj v}
    (h : At hμ c hcard hsize hmerger hj E hE F w τ b)
    (h' : At hμ c hcard hsize hmerger hj E hE F w τ b') : b = b' := by
  obtain ⟨hw,x,σ,hσ,hx,hb⟩ := h
  obtain ⟨hw',y,σ',hσ',hy,hb'⟩ := h'
  have hname : σ = σ' := LocalName.ext (hσ.trans hσ'.symm)
  have hxy : x = y := Subtype.ext (Subtype.ext (by rw [← hx,← hy,hname]))
  subst y
  exact hb.symm.trans hb'

/-- The same code cannot name different classes merely by choosing different
finite tails. -/
theorem represents_unique {F : GenericFilter (CohenForcing.Condition I κ)}
    {a : ChainCode hμ c C} {b b' : (D[F]).Glued hj v}
    (h : Represents hμ c hcard hsize hmerger hj E hE C F a b)
    (h' : Represents hμ c hcard hsize hmerger hj E hE C F a b') : b = b' := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := h'
  exact at_unique (hN (max N L) (le_max_left _ _)) (hL (max N L) (le_max_right _ _))

/-- Every glued class has a code of genuine local name representatives. This
is a set-sized countable choice in the ambient ordinary computation; it is
not yet a claim that an external filter is generic. -/
theorem exists_representing_code (F : GenericFilter (CohenForcing.Condition I κ))
    (b : (D[F]).Glued hj v) :
    ∃ a : ChainCode hμ c C, Represents hμ c hcard hsize hmerger hj E hE C F a b := by
  have hex (i : ℕ) : ∃ τ : LocalName hμ c (C.vertex i).diagram,
      At hμ c hcard hsize hmerger hj E hE F (C.vertex i) τ.name b := by
    obtain ⟨x,hx⟩ := (D[F]).toGlued_surjective hj v (C.vertex i) (C.common i) b
    obtain ⟨σ,hσ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ F (C.vertex i).diagram) x.val.val
    exact ⟨σ,C.common i,x,σ,rfl,hσ,hx⟩
  choose a ha using hex
  exact ⟨a,0,fun i _ => ha i⟩

variable (hμ c hcard hsize hmerger hj E hE)

/-- Transport of the glued component to the moved Cohen filter, retaining
its original chosen root. -/
def transport (F : GenericFilter (CohenForcing.Condition I κ))
    (g : Vertex.componentStabilizer hj v) :
    (D[F]).Glued hj v ≃
      (D[F.move (CohenForcing.Condition.permuteOrderIso g.val.val)]).Glued hj v :=
  (eligibleSystemTransport hμ c hcard hsize hmerger F q E hE g.val).componentEquiv
    g.val hj v g.property

/-- This equality is about the actual transported name. In particular it
does not identify movement of a check-name with movement of its code. -/
theorem at_transport_iff (F : GenericFilter (CohenForcing.Condition I κ))
    (g : Vertex.componentStabilizer hj v) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name) (b : (D[F]).Glued hj v) :
    At hμ c hcard hsize hmerger hj E hE
      (F.move (CohenForcing.Condition.permuteOrderIso g.val.val)) (g.val • w) (g.val.val • τ)
      (transport hμ c hcard hsize hmerger hj E hE F g b) ↔
    At hμ c hcard hsize hmerger hj E hE F w τ b := by
  let F' := F.move (CohenForcing.Condition.permuteOrderIso g.val.val)
  let T := eligibleSystemTransport hμ c hcard hsize hmerger F q E hE g.val
  have hnat {hw : Vertex.Common v w} (x : (D[F]).vertexFiber w) :
      transport hμ c hcard hsize hmerger hj E hE F g ((D[F]).toGlued hj v w hw x) =
        (D[F']).toGlued hj v (g.val • w) (g.property.trans hj (hw.move g.val))
          (T.fiberEquiv g.val w x) := T.componentEquiv_toGlued g.val hj v w g.property hw x
  constructor
  · rintro ⟨hw,y,σ,hσ,hy,hb⟩
    have hw' : Vertex.Common v w := by
      have h := (g.property.symm.trans hj hw).move g.val⁻¹
      simpa only [inv_smul_smul] using h
    obtain ⟨x,hx⟩ := (T.fiberEquiv g.val w).surjective y
    obtain ⟨ρ,hρ⟩ := (LocalName.transportEquiv hμ c g.val.val w.diagram).surjective σ
    have hname : ρ.name = τ := by
      have hh : g.val.val • ρ.name = g.val.val • τ := by
        calc
          g.val.val • ρ.name = (LocalName.transportEquiv hμ c g.val.val w.diagram ρ).name := rfl
          _ = σ.name := congrArg LocalName.name hρ
          _ = g.val.val • τ := hσ
      exact (MulAction.injective g.val.val) hh
    refine ⟨hw',x,ρ,hname,?_,?_⟩
    · apply LocalQuotient.transport_injective F g.val.val w.diagram
      change LocalQuotient.ofName F' (ρ.transport hμ g.val.val) =
        (T.fiberEquiv g.val w x).val.val
      rw [hx]
      exact (congrArg (LocalQuotient.ofName F') hρ).trans hy
    · apply (transport hμ c hcard hsize hmerger hj E hE F g).injective
      rw [hnat,hx]
      exact hb
  · rintro ⟨hw,x,σ,hσ,hx,hb⟩
    refine ⟨g.property.trans hj (hw.move g.val),T.fiberEquiv g.val w x,
      σ.transport hμ g.val.val,?_,?_,?_⟩
    · change g.val.val • σ.name = g.val.val • τ
      rw [hσ]
    · exact congrArg (LocalQuotient.transport hμ F g.val.val) hx
    · exact (hnat x).symm.trans (congrArg (transport hμ c hcard hsize hmerger hj E hE F g) hb)

variable (C)

omit [Infinite M] [Infinite I] in
/-- Eventual literal fixation of every entry of every individual code. The
bound concerns the chain, not an invariance of its ground code wellorder. -/
theorem tail_fixed (k : C.tailFixer hj) : ∃ N, ∀ i, N ≤ i →
    k.val.val • C.vertex i = C.vertex i ∧
      ∀ τ : LocalName hμ c (C.vertex i).diagram, k.val.val.val • τ.name = τ.name := by
  obtain ⟨N,hN⟩ := k.property
  refine ⟨N,fun i hi => ?_⟩
  have hfix : ∀ j ∈ (C.vertex i).diagram.range, k.val.val.val j = j :=
    fun j hj => hN j (C.ranges_antitone hi hj)
  have hdiag := Diagram.permute_eq_of_fixes_range k.val.val.val (C.vertex i).diagram hfix
  have hvert : k.val.val • C.vertex i = C.vertex i := by
    generalize C.vertex i = w at hdiag ⊢
    obtain ⟨r,a,hr,U⟩ := w
    change ({diagram := r.permute k.val.val.val,index := a,root := _,ideal := U} : Vertex q) = _
    simp only [hdiag]
  exact ⟨hvert,fun τ => τ.fixed k.val.val.val ((SupportFilter.mem_Fix _ _).mpr hfix)⟩

/-- Source lemma `least-code-covariance`, at the level of functioning codes:
the very same code represents the transported point at the moved filter.
Only a finite prefix may cease working. -/
theorem represents_same_code (F : GenericFilter (CohenForcing.Condition I κ))
    (k : C.tailFixer hj) (a : ChainCode hμ c C) (b : (D[F]).Glued hj v) :
    Represents hμ c hcard hsize hmerger hj E hE C
      (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) a
      (transport hμ c hcard hsize hmerger hj E hE F k.val b) ↔
    Represents hμ c hcard hsize hmerger hj E hE C F a b := by
  obtain ⟨N,hN⟩ := tail_fixed hμ c hj C k
  have htail (i : ℕ) (hi : N ≤ i) :
      At hμ c hcard hsize hmerger hj E hE
        (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) (C.vertex i) (a i).name
        (transport hμ c hcard hsize hmerger hj E hE F k.val b) ↔
      At hμ c hcard hsize hmerger hj E hE F (C.vertex i) (a i).name b := by
    have hh := at_transport_iff hμ c hcard hsize hmerger hj E hE F k.val (C.vertex i) (a i).name b
    simpa only [(hN i hi).1,(hN i hi).2 (a i)] using hh
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (htail i ((le_max_left _ _).trans hi)).mp
      (hL i ((le_max_right _ _).trans hi))⟩
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (htail i ((le_max_left _ _).trans hi)).mpr
      (hL i ((le_max_right _ _).trans hi))⟩

/-- The least code is chosen in a single fixed wellordering of the set of
all chain codes, not a fresh ordering at each filter. -/
def leastCode (F : GenericFilter (CohenForcing.Condition I κ)) (b : (D[F]).Glued hj v) :
    ChainCode hμ c C :=
  WellOrderingRel.isWellOrder.wf.min
    {a | Represents hμ c hcard hsize hmerger hj E hE C F a b}
    (exists_representing_code F b)

theorem leastCode_represents (F : GenericFilter (CohenForcing.Condition I κ))
    (b : (D[F]).Glued hj v) :
    Represents hμ c hcard hsize hmerger hj E hE C F
      (leastCode hμ c hcard hsize hmerger hj E hE C F b) b :=
  WellOrderingRel.isWellOrder.wf.min_mem _ (exists_representing_code F b)

theorem leastCode_injective (F : GenericFilter (CohenForcing.Condition I κ)) :
    Function.Injective (leastCode hμ c hcard hsize hmerger hj E hE C F) := by
  intro b b' he
  apply represents_unique (leastCode_represents hμ c hcard hsize hmerger hj E hE C F b)
  rw [he]
  exact leastCode_represents hμ c hcard hsize hmerger hj E hE C F b'

/-- Invariance of the actual minima follows from literal equality of the
sets of functioning codes. No invariance of the ground wellordering under
movement of all entries is asserted or needed. -/
theorem leastCode_covariance (F : GenericFilter (CohenForcing.Condition I κ))
    (k : C.tailFixer hj) (b : (D[F]).Glued hj v) :
    leastCode hμ c hcard hsize hmerger hj E hE C
      (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val))
      (transport hμ c hcard hsize hmerger hj E hE F k.val b) =
    leastCode hμ c hcard hsize hmerger hj E hE C F b := by
  have hset :
      {a | Represents hμ c hcard hsize hmerger hj E hE C
        (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) a
        (transport hμ c hcard hsize hmerger hj E hE F k.val b)} =
      {a | Represents hμ c hcard hsize hmerger hj E hE C F a b} := by
    ext a
    exact represents_same_code hμ c hcard hsize hmerger hj E hE C F k a b
  unfold leastCode
  congr 1

/-- The wellordering of the glued classes induced by their least codes. -/
def LT (F : GenericFilter (CohenForcing.Condition I κ))
    (b b' : (D[F]).Glued hj v) : Prop :=
  WellOrderingRel (leastCode hμ c hcard hsize hmerger hj E hE C F b)
    (leastCode hμ c hcard hsize hmerger hj E hE C F b')

instance leastCode_isWellOrder (F : GenericFilter (CohenForcing.Condition I κ)) :
    IsWellOrder ((D[F]).Glued hj v) (LT hμ c hcard hsize hmerger hj E hE C F) where
  wf := InvImage.wf (leastCode hμ c hcard hsize hmerger hj E hE C F)
    WellOrderingRel.isWellOrder.wf
  trichotomous := @Std.Trichotomous.trichotomous _
    (InvImage WellOrderingRel (leastCode hμ c hcard hsize hmerger hj E hE C F))
    (InvImage.trichotomous (r := WellOrderingRel)
      (leastCode_injective hμ c hcard hsize hmerger hj E hE C F))

/-- The order-isomorphism form of `least-code-covariance`. -/
def leastCodeOrderIso (F : GenericFilter (CohenForcing.Condition I κ)) (k : C.tailFixer hj) :
    LT hμ c hcard hsize hmerger hj E hE C F ≃r
      LT hμ c hcard hsize hmerger hj E hE C
        (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) where
  toEquiv := transport hμ c hcard hsize hmerger hj E hE F k.val
  map_rel_iff' := by
    intro b b'
    change WellOrderingRel _ _ ↔ WellOrderingRel _ _
    rw [leastCode_covariance,leastCode_covariance]

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## Graph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Literal children suffice to name the Cartesian product of two sets, at
arbitrary ranks. The activation test retains both membership values. -/
abbrev ProductEntries (X Y : S.Name) := Edges X.raw × Edges Y.raw

def productEntry (X Y : S.Name) (i : S.ProductEntries X Y) : S.Name :=
  (X.child i.1.property).opair (Y.child i.2.property)

def productTest (X Y : S.Name) (i : S.ProductEntries X Y) (p : P) : Prop :=
  S.atomic.MemF p (X.child i.1.property) X ∧ S.atomic.MemF p (Y.child i.2.property) Y

def productSupport (X Y : S.Name) : Subgroup Γ :=
  MulAction.stabilizer Γ X.val ⊓ MulAction.stabilizer Γ Y.val

omit [OrderTop P] in
theorem productSupport_mem (X Y : S.Name) : S.productSupport X Y ∈ S.filter :=
  S.normal.2.2.1 _ _ X.hs.symmetric Y.hs.symmetric

theorem product_permute (X Y : S.Name) :
    ∀ g ∈ S.productSupport X Y, ∀ i p, S.productTest X Y i p →
      ∃ j, S.productEntry X Y j = g • S.productEntry X Y i ∧
        S.productTest X Y j (S.move g p) := by
  intro g hg i p hp
  have hx : g • X = X := Subtype.ext hg.1
  have hy : g • Y = Y := Subtype.ext hg.2
  have hex := S.entry_permute g X i.1
  have hey := S.entry_permute g Y i.2
  rw [hx] at hex
  rw [hy] at hey
  obtain ⟨j,hj⟩ := hex
  obtain ⟨k,hk⟩ := hey
  refine ⟨(j,k),?_,?_,?_⟩
  · simp only [productEntry,Name.smul_opair,hj,hk]
  · change S.atomic.MemF (S.move g p) (X.child j.property) X
    rw [hj]
    simpa only [hx] using (S.mem_symmetry g p _ X).mp hp.1

  · change S.atomic.MemF (S.move g p) (Y.child k.property) Y
    rw [hk]
    simpa only [hy] using (S.mem_symmetry g p _ Y).mp hp.2


def cartesianName (X Y : S.Name) : S.Name :=
  S.collect (S.productEntry X Y) (S.productTest X Y) (S.productSupport X Y)
    (S.productSupport_mem X Y) (S.product_permute X Y)

theorem cartesianName_fixed (X Y : S.Name) (g : Γ) (hx : g • X = X) (hy : g • Y = Y) :
    g • S.cartesianName X Y = S.cartesianName X Y :=
  Subtype.ext (S.collectName_fixed _ _ (S.productSupport X Y) (S.product_permute X Y)
    g ⟨congrArg Subtype.val hx,congrArg Subtype.val hy⟩)

/-- Exact Cartesian membership, including the assertion that every member
is an actual ordered pair. All witnesses remain HS names. -/
theorem mem_cartesianName (X Y ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.cartesianName X Y) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x y : S.Name,
        S.atomic.MemF r x X ∧ S.atomic.MemF r y Y ∧ S.atomic.EqF r ν (x.opair y) := by
  rw [cartesianName,S.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,i,a,hi,hra,he⟩ := h q hqp
    exact ⟨r,hrq,X.child i.1.property,Y.child i.2.property,
      S.atomic.mem_mono hra hi.1,S.atomic.mem_mono hra hi.2,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,y,hx,hy,he⟩ := h q hqp
    obtain ⟨s,hsr,σ,a,ha,hsa,hxσ⟩ := S.mem_iff.mp hx r le_rfl
    obtain ⟨t,hts,τ,b,hb,htb,hyτ⟩ := S.mem_iff.mp hy s hsr
    let i : S.ProductEntries X Y := (⟨(σ.raw,S.code a),ha⟩,⟨(τ.raw,S.code b),hb⟩)
    have hσ : X.child i.1.property = σ := Name.ext rfl
    have hτ : Y.child i.2.property = τ := Name.ext rfl
    refine ⟨t,hts.trans (hsr.trans hrq),i,t,?_,le_rfl,?_⟩
    · change S.atomic.MemF t (X.child i.1.property) X ∧
        S.atomic.MemF t (Y.child i.2.property) Y
      rw [hσ,hτ]
      exact ⟨S.mem_of_edge ha (hts.trans hsa),S.mem_of_edge hb htb⟩
    · change S.atomic.EqF t ν ((X.child i.1.property).opair (Y.child i.2.property))
      rw [hσ,hτ]
      exact S.atomic.eq_trans (S.atomic.eq_mono (hts.trans hsr) he)
        (S.eq_opair_congr (S.atomic.eq_mono hts hxσ) hyτ)

/-- The Cartesian name has precisely the usual membership value on pairs. -/
theorem opair_mem_cartesianName (X Y x y : S.Name) (p : P) :
    S.atomic.MemF p (x.opair y) (S.cartesianName X Y) ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y := by
  rw [S.mem_cartesianName]
  constructor
  · intro h
    have hd q (hqp : q ≤ p) : ∃ r, r ≤ q ∧ S.atomic.MemF r x X ∧ S.atomic.MemF r y Y := by
      obtain ⟨r,hrq,a,b,ha,hb,he⟩ := h q hqp
      obtain ⟨hxa,hyb⟩ := S.eq_opair_iff.mp he
      exact ⟨r,hrq,(S.atomic.mem_congr hxa (S.atomic.eq_refl r X)).mpr ha,
        (S.atomic.mem_congr hyb (S.atomic.eq_refl r Y)).mpr hb⟩
    exact ⟨S.atomic_regular.2 _ _ _ (fun q hqp => (hd q hqp).imp (fun r hr => ⟨hr.1,hr.2.1⟩)),
      S.atomic_regular.2 _ _ _ (fun q hqp => (hd q hqp).imp (fun r hr => ⟨hr.1,hr.2.2⟩))⟩
  · rintro ⟨hx,hy⟩ q hqp
    exact ⟨q,le_rfl,x,y,S.atomic.mem_mono hqp hx,S.atomic.mem_mono hqp hy,S.atomic.eq_refl q _⟩

/-- A regular, equality-respecting binary forcing relation. This auxiliary
structure is used to construct an actual bounded set graph by collection;
it is not an assumed function or an assumed semantic model. -/
structure BinaryRelation where
  holds : P → S.Name → S.Name → Prop
  mono : ∀ {p q x y}, q ≤ p → holds p x y → holds q x y
  regular : ∀ {p x y}, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ holds r x y) → holds p x y
  congr : ∀ {p x x' y y'}, S.atomic.EqF p x x' → S.atomic.EqF p y y' →
    (holds p x y ↔ holds p x' y')

omit [OrderTop P] in
/-- Unpacking an internal map leaves its full set-function conjunct intact. -/
theorem forces_mapsTo {n} (v : Fin n → S.Name) (p : P) (f a b : Fin n) :
    S.Forces v p (SetLanguage.mapsTo f a b) ↔
      S.Forces ![v f,v a] p (SetLanguage.functionOn 0 1) ∧
      ∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v a) →
        ∀ r, r ≤ q → S.App r (v f) x y → S.atomic.MemF r y (v b) := by
  simp only [Forces,SetLanguage.mapsTo,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_edge]
  have hv : (v ∘ ![f,a,b]) ∘ ![0,1] = ![v f,v a] ∘ ![0,1] := by
    funext i
    fin_cases i <;> rfl
  simp only [SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,hv]
  rfl

omit [OrderTop P] in
/-- Unpacking the graph-surjection sentence keeps all witnesses internal. -/
theorem forces_surjection {n} (v : Fin n → S.Name) (p : P) (f a b : Fin n) :
    S.Forces v p (SetLanguage.surjection f a b) ↔
      S.Forces ![v f,v a,v b] p (SetLanguage.mapsTo 0 1 2) ∧
      ∀ y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q y (v b) →
        ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x : S.Name,
          S.atomic.MemF s x (v a) ∧ S.App s (v f) x y := by
  simp only [Forces,SetLanguage.surjection,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_edge]
  have hv : (v ∘ ![f,a,b]) ∘ ![0,1,2] = ![v f,v a,v b] ∘ ![0,1,2] := by
    funext i
    fin_cases i <;> rfl
  simp only [SetLanguage.mapsTo,S.atomic.forceFormula_rename S.atomic_regular,hv]
  rfl

namespace BinaryRelation
variable {S} (R : S.BinaryRelation)
variable (X Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hX : ∀ g ∈ H, g • X = X) (hY : ∀ g ∈ H, g • Y = Y)
variable (hR : ∀ g ∈ H, ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))

def test (i : S.ProductEntries X Y) (p : P) : Prop :=
  S.productTest X Y i p ∧ R.holds p (X.child i.1.property) (Y.child i.2.property)

include hX hY hR in
theorem test_permute : ∀ g ∈ H, ∀ i p, R.test X Y i p →
    ∃ j, S.productEntry X Y j = g • S.productEntry X Y i ∧
      R.test X Y j (S.move g p) := by
  intro g hg i p hi
  have hex := S.entry_permute g X i.1
  have hey := S.entry_permute g Y i.2
  rw [hX g hg] at hex
  rw [hY g hg] at hey
  obtain ⟨j,hj⟩ := hex
  obtain ⟨k,hk⟩ := hey
  refine ⟨(j,k),?_,⟨?_,?_⟩,?_⟩
  · simp only [productEntry,Name.smul_opair,hj,hk]
  · change S.atomic.MemF (S.move g p) (X.child j.property) X
    rw [hj]
    simpa only [hX g hg] using (S.mem_symmetry g p _ X).mp hi.1.1
  · change S.atomic.MemF (S.move g p) (Y.child k.property) Y
    rw [hk]
    simpa only [hY g hg] using (S.mem_symmetry g p _ Y).mp hi.1.2
  · change R.holds (S.move g p) (X.child j.property) (Y.child k.property)
    rw [hj,hk]
    exact hR g hg p _ _ hi.2

/-- The actual HS name for the bounded relation on `X × Y`. -/
def graph : S.Name :=
  S.collect (S.productEntry X Y) (R.test X Y) H hH (R.test_permute X Y H hX hY hR)

theorem graph_fixed (g : Γ) (hg : g ∈ H) :
    g • R.graph X Y H hH hX hY hR = R.graph X Y H hH hX hY hR :=
  Subtype.ext (S.collectName_fixed _ _ H (R.test_permute X Y H hX hY hR) g hg)

theorem mem_graph (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (R.graph X Y H hH hX hY hR) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x y : S.Name,
        S.atomic.MemF r x X ∧ S.atomic.MemF r y Y ∧ R.holds r x y ∧
          S.atomic.EqF r ν (x.opair y) := by
  rw [graph,S.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,i,a,hi,hra,he⟩ := h q hqp
    exact ⟨r,hrq,X.child i.1.property,Y.child i.2.property,
      S.atomic.mem_mono hra hi.1.1,S.atomic.mem_mono hra hi.1.2,R.mono hra hi.2,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,y,hx,hy,hRxy,he⟩ := h q hqp
    obtain ⟨s,hsr,σ,a,ha,hsa,hxσ⟩ := S.mem_iff.mp hx r le_rfl
    obtain ⟨t,hts,τ,b,hb,htb,hyτ⟩ := S.mem_iff.mp hy s hsr
    let i : S.ProductEntries X Y := (⟨(σ.raw,S.code a),ha⟩,⟨(τ.raw,S.code b),hb⟩)
    have hσ : X.child i.1.property = σ := Name.ext rfl
    have hτ : Y.child i.2.property = τ := Name.ext rfl
    refine ⟨t,hts.trans (hsr.trans hrq),i,t,?_,le_rfl,?_⟩
    · change (S.atomic.MemF t (X.child i.1.property) X ∧
        S.atomic.MemF t (Y.child i.2.property) Y) ∧
        R.holds t (X.child i.1.property) (Y.child i.2.property)
      rw [hσ,hτ]
      exact ⟨⟨S.mem_of_edge ha (hts.trans hsa),S.mem_of_edge hb htb⟩,
        (R.congr (S.atomic.eq_mono hts hxσ) hyτ).mp (R.mono (hts.trans hsr) hRxy)⟩
    · change S.atomic.EqF t ν ((X.child i.1.property).opair (Y.child i.2.property))
      rw [hσ,hτ]
      exact S.atomic.eq_trans (S.atomic.eq_mono (hts.trans hsr) he)
        (S.eq_opair_congr (S.atomic.eq_mono hts hxσ) hyτ)

/-- Every application of this internal graph is exactly a related bounded
pair. No external function is substituted for an internal set graph. -/
theorem app_graph (x y : S.Name) (p : P) :
    S.App p (R.graph X Y H hH hX hY hR) x y ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ R.holds p x y := by
  rw [S.app_iff_mem_opair,R.mem_graph X Y H hH hX hY hR]
  constructor
  · intro h
    have hd q (hqp : q ≤ p) : ∃ r, r ≤ q ∧
        S.atomic.MemF r x X ∧ S.atomic.MemF r y Y ∧ R.holds r x y := by
      obtain ⟨r,hrq,a,b,ha,hb,hRab,he⟩ := h q hqp
      obtain ⟨hxa,hyb⟩ := S.eq_opair_iff.mp he
      exact ⟨r,hrq,(S.atomic.mem_congr hxa (S.atomic.eq_refl r X)).mpr ha,
        (S.atomic.mem_congr hyb (S.atomic.eq_refl r Y)).mpr hb,(R.congr hxa hyb).mpr hRab⟩
    refine ⟨S.atomic_regular.2 _ _ _ ?_,S.atomic_regular.2 _ _ _ ?_,R.regular ?_⟩
    · intro q hqp
      obtain ⟨r,hrq,hx,_,_⟩ := hd q hqp
      exact ⟨r,hrq,hx⟩
    · intro q hqp
      obtain ⟨r,hrq,_,hy,_⟩ := hd q hqp
      exact ⟨r,hrq,hy⟩
    · intro q hqp
      obtain ⟨r,hrq,_,_,hRxy⟩ := hd q hqp
      exact ⟨r,hrq,hRxy⟩
  · rintro ⟨hx,hy,hRxy⟩ q hqp
    exact ⟨q,le_rfl,x,y,S.atomic.mem_mono hqp hx,S.atomic.mem_mono hqp hy,
      R.mono hqp hRxy,S.atomic.eq_refl q _⟩

/-- Totality and uniqueness produce the internal function formula, including
its prohibition of non-pairs and out-of-domain graph entries. -/
theorem graph_functionOn (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z) :
    S.Forces ![R.graph X Y H hH hX hY hR,X] p (SetLanguage.functionOn 0 1) := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_orderedPair,S.forces_edge]
  constructor
  · intro ν q hqp hm r hrq
    obtain ⟨s,hsr,x,y,hx,_,_,he⟩ := (R.mem_graph X Y H hH hX hY hR ν q).mp hm r hrq
    refine ⟨s,hsr,x,?_⟩
    intro t hts
    exact ⟨t,le_rfl,y,S.atomic.mem_mono hts hx,S.atomic.eq_mono hts he⟩
  · intro x q hqp hx r hrq
    obtain ⟨s,hsr,y,hy,hRxy⟩ := htotal x q hqp hx r hrq
    refine ⟨s,hsr,y,(R.app_graph X Y H hH hX hY hR x y s).mpr
      ⟨S.atomic.mem_mono (hsr.trans hrq) hx,hy,hRxy⟩,?_⟩
    intro z t hts ha
    exact hone t (hts.trans (hsr.trans (hrq.trans hqp))) x z y
      ((R.app_graph X Y H hH hX hY hR x z t).mp ha).2.2 (R.mono hts hRxy)

/-- The same actual graph takes all its values in the specified codomain. -/

theorem graph_mapsTo (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z) :
    S.Forces ![R.graph X Y H hH hX hY hR,X,Y] p (SetLanguage.mapsTo 0 1 2) := by
  rw [S.forces_mapsTo]
  constructor
  · exact R.graph_functionOn X Y H hH hX hY hR p htotal hone
  · intro x y q _ _ r _ ha
    exact ((R.app_graph X Y H hH hX hY hR x y r).mp ha).2.1

/-- Dense local inverse witnesses give an internal surjection, not an
externally indexed family of maps. -/

theorem graph_surjection (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z)
    (honto : ∀ y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q y Y →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x : S.Name, S.atomic.MemF s x X ∧ R.holds s x y) :
    S.Forces ![R.graph X Y H hH hX hY hR,X,Y] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  constructor
  · exact R.graph_mapsTo X Y H hH hX hY hR p htotal hone
  · intro y q hqp hy r hrq
    obtain ⟨s,hsr,x,hx,hRxy⟩ := honto y q hqp hy r hrq
    exact ⟨s,hsr,x,hx,(R.app_graph X Y H hH hX hY hR x y s).mpr
      ⟨hx,S.atomic.mem_mono (hsr.trans hrq) hy,hRxy⟩⟩

end BinaryRelation
end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
