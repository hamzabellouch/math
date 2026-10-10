import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.TailGraphs

namespace OAI

/-! ## IndexedGraph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The canonical internal graph of a small ground-indexed name family.
Uniform support is used only to prove that this actual set name is HS. -/
def indexedGraph (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) : S.Name :=
  S.collect (fun x : X => (Name.check x.val).opair (f x)) (fun _ _ => True) H hH (by
    intro g hg x p _
    exact ⟨x,by simp only [Name.smul_opair,Name.smul_check,hfix g hg],trivial⟩)

theorem indexedGraph_fixed (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (g : Γ) (hg : g ∈ H) :
    g • S.indexedGraph X f H hH hfix = S.indexedGraph X f H hH hfix :=
  Subtype.ext (S.collectName_fixed _ _ H (by
    intro π hπ x p _
    exact ⟨x,by simp only [Name.smul_opair,Name.smul_check,hfix π hπ],trivial⟩) g hg)

/-- The complete membership value of the graph. -/
theorem mem_indexedGraph (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.indexedGraph X f H hH hfix) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : X,
        S.atomic.EqF r ν ((Name.check x.val).opair (f x)) := by
  constructor
  · intro hm q hqp
    obtain ⟨r,hrq,τ,c,he,_,heq⟩ := S.mem_iff.mp hm q hqp
    obtain ⟨x,d,_,hτ,_⟩ := (S.edge_collectRaw
      (fun x : X => (Name.check x.val).opair (f x)) (fun _ _ => True) τ.raw (S.code c)).mp he
    exact ⟨r,hrq,x,(Name.ext hτ : (Name.check x.val).opair (f x) = τ) ▸ heq⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,x,heq⟩ := h q hqp
    refine ⟨r,hrq,(Name.check x.val).opair (f x),⊤,?_,le_top,heq⟩
    exact (S.edge_collectRaw (fun x : X => (Name.check x.val).opair (f x))
      (fun _ _ => True) _ _).mpr ⟨x,⊤,trivial,rfl,rfl⟩

/-- Every value asserted by the graph is one of its prescribed values, with
both the input and output transported by forced equality. -/
theorem app_indexedGraph (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (x y : S.Name) (p : P) :
    S.App p (S.indexedGraph X f H hH hfix) x y ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
        S.atomic.EqF r x (Name.check i.val) ∧ S.atomic.EqF r y (f i) := by
  rw [S.app_iff_mem_opair,S.mem_indexedGraph]
  simp only [S.eq_opair_iff]

theorem indexedGraph_app_at (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (i : X) (p : P) :
    S.App p (S.indexedGraph X f H hH hfix) (Name.check i.val) (f i) :=
  (S.app_indexedGraph X f H hH hfix _ _ p).mpr
    (fun q _ => ⟨q,le_rfl,i,S.atomic.eq_refl _ _,S.atomic.eq_refl _ _⟩)

/-- The ground-indexed name-family graph satisfies the unmodified internal
set-function formula. This includes the assertion that it has no junk entries. -/
theorem indexedGraph_functionOn (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (p : P) :
    S.Forces ![S.indexedGraph X f H hH hfix,Name.check X] p (SetLanguage.functionOn 0 1) := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_orderedPair,S.forces_edge]
  constructor
  · intro ν q hqp hm r hrq
    obtain ⟨s,hsr,i,heq⟩ := (S.mem_indexedGraph X f H hH hfix ν q).mp hm r hrq
    refine ⟨s,hsr,Name.check i.val,?_⟩
    intro t hts
    exact ⟨t,le_rfl,f i,S.check_mem_of_mem i.property t,S.atomic.eq_mono hts heq⟩
  · intro ν q hqp hm r hrq
    obtain ⟨s,hsr,x,hx,heq⟩ := (S.mem_check X ν q).mp hm r hrq
    let i : X := ⟨x,hx⟩
    refine ⟨s,hsr,f i,?_,?_⟩
    · exact (S.app_congr (S.atomic.eq_refl s _) heq (S.atomic.eq_refl s (f i))).mpr
        (S.indexedGraph_app_at X f H hH hfix i s)
    · intro z t hts ha
      apply S.atomic_regular.1
      intro a hat
      obtain ⟨b,hba,j,hj,hz⟩ := (S.app_indexedGraph X f H hH hfix ν z t).mp ha a hat
      have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val b).mp
        (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hba.trans (hat.trans hts)) heq)) hj))
      exact ⟨b,hba,hij.symm ▸ hz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CheckGraph -/

/-! Literal ground graphs and their check names.  These lemmas keep the
internal set-function formula, including its no-junk-entries conjunct. -/
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Check names commute, up to forced equality, with unordered pairs. -/
theorem check_unorderedPair (x y : ZFSet.{u}) (p : P) :
    S.atomic.EqF p (Name.check {x,y}) ((Name.check x).pair (Name.check y)) := by
  apply S.eq_of_same_members
  intro ν q hqp
  rw [S.mem_check,S.mem_pair]
  constructor
  · intro h r hrq
    obtain ⟨s,hsr,z,hz,he⟩ := h r hrq
    rcases ZFSet.mem_pair.mp hz with rfl | rfl
    · exact ⟨s,hsr,Or.inl he⟩
    · exact ⟨s,hsr,Or.inr he⟩
  · intro h r hrq
    obtain ⟨s,hsr,hx | hy⟩ := h r hrq
    · exact ⟨s,hsr,x,ZFSet.mem_pair.mpr (Or.inl rfl),hx⟩
    · exact ⟨s,hsr,y,ZFSet.mem_pair.mpr (Or.inr rfl),hy⟩

/-- `ZFSet.pair` is the actual Kuratowski pair. -/
theorem check_opair (x y : ZFSet.{u}) (p : P) :
    S.atomic.EqF p (Name.check (ZFSet.pair x y)) ((Name.check x).opair (Name.check y)) := by
  have hs : ({x} : ZFSet.{u}) = {x,x} := by ext z; simp
  change S.atomic.EqF p (Name.check {{x},{x,y}}) _
  refine S.atomic.eq_trans (S.check_unorderedPair {x} {x,y} p) ?_
  apply S.eq_pair_congr
  · rw [hs]
    exact S.check_unorderedPair x x p
  · exact S.check_unorderedPair x y p

/-- A ground function is represented by a literal set of ordered pairs. -/
def groundGraph (X : ZFSet.{u}) (g : X → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun x : X => ZFSet.pair x.val (g x))

theorem mem_groundGraph (X : ZFSet.{u}) (g : X → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ groundGraph X g ↔ ∃ x : X, ZFSet.pair x.val (g x) = z :=
  ZFSet.mem_range

theorem mem_check_groundGraph (X : ZFSet.{u}) (g : X → ZFSet.{u}) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (Name.check (groundGraph X g)) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : X,
        S.atomic.EqF r ν ((Name.check x.val).opair (Name.check (g x))) := by
  rw [S.mem_check]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,z,hz,he⟩ := h q hqp
    obtain ⟨x,rfl⟩ := (mem_groundGraph X g z).mp hz
    exact ⟨r,hrq,x,S.atomic.eq_trans he (S.check_opair x.val (g x) r)⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,he⟩ := h q hqp
    exact ⟨r,hrq,ZFSet.pair x.val (g x),(mem_groundGraph X g _).mpr ⟨x,rfl⟩,
      S.atomic.eq_trans he (S.atomic.eq_symm (S.check_opair x.val (g x) r))⟩

theorem check_groundGraph_app (X : ZFSet.{u}) (g : X → ZFSet.{u}) (i : X) (p : P) :
    S.App p (Name.check (groundGraph X g)) (Name.check i.val) (Name.check (g i)) := by
  rw [S.app_iff_mem_opair,S.mem_check_groundGraph]
  exact fun q _ => ⟨q,le_rfl,i,S.atomic.eq_refl _ _⟩

/-- Membership in an internal function graph can only come from its actual
ordered pairs, whose first coordinates lie in its domain. -/
theorem functionOn_entries {n} (v : Fin n → S.Name) (p : P) (f d : Fin n)
    (hf : S.Forces v p (SetLanguage.functionOn f d))
    (ν : S.Name) {q : P} (hqp : q ≤ p) (hν : S.atomic.MemF q ν (v f)) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x y : S.Name,
      S.atomic.MemF s x (v d) ∧ S.atomic.EqF s ν (x.opair y) := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_edge,S.forces_orderedPair] at hf
  intro r hrq
  obtain ⟨s,hsr,x,hx⟩ := hf.1 ν q hqp hν r hrq
  obtain ⟨t,hts,y,hxd,he⟩ := hx s le_rfl
  exact ⟨t,hts.trans hsr,x,y,hxd,he⟩

/-- A forced function on a ground domain with all values prescribed by one
ground function is equal to the check name of that function's set graph. -/
theorem functionOn_eq_check_groundGraph (X : ZFSet.{u}) (g : X → ZFSet.{u})
    (f : S.Name) (p : P)
    (hf : S.Forces ![f,Name.check X] p (SetLanguage.functionOn 0 1))
    (hg : ∀ i : X, S.App p f (Name.check i.val) (Name.check (g i))) :
    S.atomic.EqF p f (Name.check (groundGraph X g)) := by
  apply S.eq_of_same_members
  intro ν q hqp
  constructor
  · intro hm
    apply (S.mem_check_groundGraph X g ν q).mpr
    intro r hrq
    obtain ⟨s,hsr,x,y,hx,he⟩ := S.functionOn_entries ![f,Name.check X] p 0 1 hf ν hqp hm r hrq
    obtain ⟨t,hts,a,ha,hxa⟩ := (S.mem_check X x s).mp hx s le_rfl
    let i : X := ⟨a,ha⟩
    have htf : t ≤ p := hts.trans (hsr.trans (hrq.trans hqp))
    have hxy : S.App t f x y := by
      apply (S.app_iff_mem_opair t f x y).mpr
      exact (S.atomic.mem_congr (S.atomic.eq_mono hts he) (S.atomic.eq_refl t f)).mp
        (S.atomic.mem_mono (hts.trans (hsr.trans hrq)) hm)
    have hay : S.App t f (Name.check a) y :=
      (S.app_congr (S.atomic.eq_refl t f) hxa (S.atomic.eq_refl t y)).mp hxy
    have hy : S.atomic.EqF t y (Name.check (g i)) :=
      S.functionOn_unique ![f,Name.check X] t 0 1
        (S.atomic.forceFormula_mono htf hf) (Name.check a) y (Name.check (g i))
        (S.check_mem_of_mem ha t) hay (S.app_mono htf (hg i))
    exact ⟨t,hts.trans hsr,i,S.atomic.eq_trans (S.atomic.eq_mono hts he)
      (S.eq_opair_congr hxa hy)⟩
  · intro hm
    apply S.atomic_regular.2
    intro r hrq
    obtain ⟨s,hsr,i,he⟩ := (S.mem_check_groundGraph X g ν q).mp hm r hrq
    have hi := (S.app_iff_mem_opair s f (Name.check i.val) (Name.check (g i))).mp
      (S.app_mono (hsr.trans (hrq.trans hqp)) (hg i))
    exact ⟨s,hsr,(S.atomic.mem_congr he (S.atomic.eq_refl s f)).mpr hi⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Fusion -/

/-! Countable ground-sequence preservation by fusion at a fixed supporting
root. The diagram forcing is not asserted to be countably closed. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u v
noncomputable section
open scoped Classical
variable {I κ : Type u}

/-- Every countable family of downward-persistent dense requirements below
a Cohen condition can be met by one condition, by actual countable closure. -/
theorem countable_fusion {A : Type v} [Countable A]
    (d : Condition I κ) (R : A → Condition I κ → Prop)
    (hmono : ∀ i q r, r ≤ q → R i q → R i r)
    (hdense : ∀ i q, q ≤ d → ∃ r, r ≤ q ∧ R i r) :
    ∃ r, r ≤ d ∧ ∀ i, R i r := by
  let : Encodable A := Encodable.ofCountable A
  let step (n : ℕ) (q : Set.Iic d) : Set.Iic d :=
    match Encodable.decode (α := A) n with
    | none => q
    | some i => ⟨(hdense i q.val q.property).choose,
        (hdense i q.val q.property).choose_spec.1.trans q.property⟩
  have hstep (n : ℕ) (q : Set.Iic d) : (step n q).val ≤ q.val := by
    dsimp only [step]
    cases Encodable.decode (α := A) n with
    | none => exact le_rfl
    | some i => exact (hdense i q.val q.property).choose_spec.1
  have hreq (i : A) (q : Set.Iic d) : R i (step (Encodable.encode i) q).val := by
    dsimp only [step]
    rw [Encodable.encodek]
    exact (hdense i q.val q.property).choose_spec.2
  let seq : ℕ → Set.Iic d := fun n => Nat.rec (⟨d,show d ≤ d from le_rfl⟩ : Set.Iic d) (fun n q => step n q) n
  have hseq : Antitone (fun n => (seq n).val) :=
    antitone_nat_of_succ_le (fun n => hstep n (seq n))
  obtain ⟨r,hr⟩ := countably_closed (fun n => (seq n).val) hseq
  refine ⟨r,hr 0,fun i => ?_⟩
  exact hmono i (seq (Encodable.encode i+1)).val r (hr (Encodable.encode i + 1)) (hreq i (seq (Encodable.encode i)))

end
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Each ground input of an internal ground-codomain map can be decided
without changing its supporting root; only the Cohen coordinate is changed. -/
theorem mapsTo_value_at_root [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (X Y : ZFSet.{u}) (f : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Diagram M I) (hfix : ∀ π ∈ SupportFilter.Fix p.range, π • f = f)
    (d : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces ![f,Name.check X,Name.check Y] ((d,p) : Poset M I κ)
      (SetLanguage.mapsTo 0 1 2)) (i : X) :
    ∃ e : CohenForcing.Condition I κ, e ≤ d ∧ ∃ y : Y,
      (system hμ).App ((e,p) : Poset M I κ) f (Name.check i.val) (Name.check y.val) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  have hf' := (S.forces_mapsTo ![f,Name.check X,Name.check Y] ((d,p) : Poset M I κ) 0 1 2).mp hf
  obtain ⟨q,hqd,ν,ha,_⟩ := S.functionOn_total ![f,Name.check X] ((d,p) : Poset M I κ)
    0 1 hf'.1 (Name.check i.val) le_rfl (S.check_mem_of_mem i.property _)
    ((d,p) : Poset M I κ) le_rfl
  have hν := hf'.2 (Name.check i.val) ν ((d,p) : Poset M I κ) le_rfl
    (S.check_mem_of_mem i.property _) q hqd ha
  obtain ⟨r,hrq,y,hy,he⟩ := (S.mem_check Y ν q).mp hν q le_rfl
  obtain ⟨ep,hep⟩ := exists_condition_below r
  have hepd : ep ≤ (d,p) := WithTop.coe_le_coe.mp (hep.trans (hrq.trans hqd))
  have hap : S.App ((ep.1,ep.2) : Poset M I κ) f (Name.check i.val) (Name.check y) :=
    (S.app_congr (S.atomic.eq_refl _ f) (S.atomic.eq_refl _ (Name.check i.val))
      (S.atomic.eq_mono hep he)).mp (S.app_mono (hep.trans hrq) ha)
  have hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ j : Fin 3,
      π • (![f,Name.check i.val,Name.check y] : Fin 3 → S.Name) j =
        ![f,Name.check i.val,Name.check y] j := by
    intro π hπ j
    fin_cases j
    · exact hfix π hπ
    · exact Name.smul_check S π _
    · exact Name.smul_check S π _
  have hroot := forces_at_supporting_root hμ hsize hmerger (SetLanguage.edge 0 1 2)
    ![f,Name.check i.val,Name.check y] p ep.2 hepd.2 hv ep.1 hap
  refine ⟨ep.1,hepd.1,⟨y,hy⟩,?_⟩
  exact S.atomic.forceFormula_mono
    (WithTop.coe_le_coe.mpr (show (ep.1,p) ≤ (ep.1.restrict p.range,p) from
      ⟨ep.1.le_restrict _,le_rfl⟩)) hroot

/-- Countably many prescribed ground inputs of a root-supported function
can all be decided by a single extension. In particular no countable ground
sequence is added by the symmetric product system. -/
theorem countable_ground_map_at_root [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (X Y : ZFSet.{u}) [Countable X]
    (f : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Diagram M I) (hfix : ∀ π ∈ SupportFilter.Fix p.range, π • f = f)
    (d : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces ![f,Name.check X,Name.check Y] ((d,p) : Poset M I κ)
      (SetLanguage.mapsTo 0 1 2)) :
    ∃ e : CohenForcing.Condition I κ, e ≤ d ∧ ∃ g : X → Y,
      (system hμ).atomic.EqF ((e,p) : Poset M I κ) f
        (Name.check (groundGraph X (fun i => (g i).val))) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let R (i : X) (e : CohenForcing.Condition I κ) : Prop :=
    ∃ y : Y, S.App ((e,p) : Poset M I κ) f (Name.check i.val) (Name.check y.val)
  have hmono : ∀ i q r, r ≤ q → R i q → R i r := by
    rintro i q r hrq ⟨y,hy⟩
    exact ⟨y,S.app_mono (p := ((q,p) : Poset M I κ)) (q := ((r,p) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨hrq,le_rfl⟩) hy⟩
  have hdense : ∀ i q, q ≤ d → ∃ r, r ≤ q ∧ R i r := by
    intro i q hqd
    exact mapsTo_value_at_root hμ hsize hmerger X Y f p hfix q
      (S.atomic.forceFormula_mono (p := ((d,p) : Poset M I κ)) (q := ((q,p) : Poset M I κ))
        (WithTop.coe_le_coe.mpr ⟨hqd,le_rfl⟩) hf) i
  obtain ⟨e,hed,he⟩ := CohenForcing.Condition.countable_fusion d R hmono hdense
  choose g hg using he
  refine ⟨e,hed,g,?_⟩
  apply S.functionOn_eq_check_groundGraph X (fun i => (g i).val) f ((e,p) : Poset M I κ)
  · exact S.atomic.forceFormula_mono (p := ((d,p) : Poset M I κ)) (q := ((e,p) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩)
      ((S.forces_mapsTo ![f,Name.check X,Name.check Y] ((d,p) : Poset M I κ) 0 1 2).mp hf).1
  · exact hg

/-- Dense ground-map decision for an arbitrary starting condition. The
support of the map and the coordinates of the condition are absorbed by
one actual extension of the diagram; closure is used only in the Cohen
coordinate after making that extension. -/
theorem countable_ground_map_dense [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (X Y : ZFSet.{u}) [Countable X]
    (f : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hf : (system hμ).Forces ![f,Name.check X,Name.check Y] t
      (SetLanguage.mapsTo 0 1 2)) :
    ∃ s, s ≤ t ∧ ∃ g : X → Y,
      (system hμ).atomic.EqF s f
        (Name.check (groundGraph X (fun i => (g i).val))) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨emb⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨emb⟩⟩
  obtain ⟨d,hdt⟩ := exists_condition_below t
  obtain ⟨J,hJ,hfix⟩ := name_support hμ f
  have hU : Cardinal.mk ↥(J ∪ d.1.support) ≤ Cardinal.mk M := by
    rw [hcard]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (d.1.cardinal_support.trans hμ)).trans_eq (Cardinal.add_eq_self hμ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through hsize e he d.2 hU
  have hpd : ((d.1,p) : Poset M I κ) ≤ t :=
    (WithTop.coe_le_coe.mpr (show (d.1,p) ≤ d from ⟨le_rfl,⟨e,hp⟩⟩)).trans hdt
  obtain ⟨a,had,g,hg⟩ := countable_ground_map_at_root hμ hsize hmerger X Y f p
    (fun π hπ => hfix π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (hcover (Or.inl hj)))))
    d.1 (S.atomic.forceFormula_mono hpd hf)
  exact ⟨(a,p),(WithTop.coe_le_coe.mpr (show (a,p) ≤ (d.1,p) from ⟨had,le_rfl⟩)).trans hpd,g,hg⟩

end
end PartitionConsistency.ProductForcing

namespace PartitionConsistency.ConcreteSystem
open CardinalParameters DiagramForcing SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section

/-- The concrete ground-independent system adds no maps from a countable
ground set to a ground set: every such forced map is densely a ground graph.
This does not assert the as-yet-unproved Partition Principle. -/
theorem countable_ground_map_dense (X Y : ZFSet) [Countable X]
    (f : S.Name) (t : P)
    (hf : S.Forces ![f,Name.check X,Name.check Y] t (SetLanguage.mapsTo 0 1 2)) :
    ∃ s, s ≤ t ∧ ∃ g : X → Y,
      S.atomic.EqF s f (Name.check (groundGraph X (fun i => (g i).val))) :=
  ProductForcing.countable_ground_map_dense aleph0_le_μ cardinal_T size_lt
    finiteMergers T.e complement_cardinal X Y f t hf

end
end PartitionConsistency.ConcreteSystem


/-! ## StableIdeal -/

/-! Dense stabilization of the actual availability ideals. This is a
condition-by-condition form of the countable-closure argument: it involves
no filter asserted to meet an unbounded collection of ambient dense sets. -/
namespace PartitionConsistency.DiagramOrder.HeightCost
universe u v
noncomputable section
open scoped Classical
variable {α : Type u} [PartialOrder α] (H : HeightCost α)
variable {P : Type v} [Preorder P]

include H in
/-- A monotone system of directed bounded ideals in a height-and-cost order
is locally constant on a dense set in any countably closed forcing. The
heights of possible future elements are approximated during a descending
construction. Positive costs exclude every still-missing element at its
countable lower bound. -/
theorem dense_stable_ideal (hclosed : ∀ f : ℕ → P, Antitone f → ∃ p, ∀ n, p ≤ f n)
    (hj : HasConditionalJoins α) {a : α} (U : P → ConeIdeal a)
    (hmono : ∀ {p q : P}, q ≤ p → (U p).carrier ⊆ (U q).carrier) (p : P) :
    ∃ q, q ≤ p ∧ ∀ r, r ≤ q → U r = U q := by
  let V (q : P) : Set α := {x | ∃ r, r ≤ q ∧ x ∈ (U r).carrier}
  let s (q : P) : ℝ := sSup (H.height '' V q)
  have hv (q : P) : (V q).Nonempty := by
    obtain ⟨x,hx⟩ := (U q).nonempty
    exact ⟨x,q,le_rfl,hx⟩
  have hb (q : P) : BddAbove (H.height '' V q) := by
    refine ⟨1,?_⟩
    rintro _ ⟨x,_,rfl⟩
    exact (H.height_lt_one x).le
  have hstep (n : ℕ) (q : P) :
      ∃ r, r ≤ q ∧ ∃ x ∈ (U r).carrier, s q - 1 / (n+1 : ℝ) < H.height x := by
    have hpos : (0 : ℝ) < 1 / (n+1 : ℝ) := by positivity
    have hs : s q - 1 / (n+1 : ℝ) < s q := by linarith
    obtain ⟨_,⟨x,⟨r,hr,hx⟩,rfl⟩,h⟩ :=
      (lt_csSup_iff (hb q) ((hv q).image H.height)).mp hs
    exact ⟨r,hr,x,hx,h⟩
  choose next hnext x hx happrox using hstep
  let f : ℕ → P := Nat.rec p (fun n q => next n q)
  have hf : Antitone f := antitone_nat_of_succ_le (fun n => hnext n (f n))
  obtain ⟨q,hq⟩ := hclosed f hf
  refine ⟨q,hq 0,fun r hr => ?_⟩
  apply ConeIdeal.ext
  apply Set.Subset.antisymm _ (hmono hr)
  intro d hd
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (H.cost_pos d)
  let z := x n (f n)
  have hzq : z ∈ (U q).carrier := hmono (hq (n+1)) (hx n (f n))
  have hzr : z ∈ (U r).carrier := hmono hr hzq
  by_contra hbad
  have hdz : ¬ d ≤ z := fun h => hbad ((U q).lower h hzq)
  obtain ⟨w,hw,hzw,hdw⟩ := (U r).directed hj z hzr d hd
  have hzw' : z < w := lt_of_le_not_ge hzw (fun h => hdz (hdw.trans h))
  have hcost := H.point_margin hzw' hdw hdz
  have hupper : H.height w ≤ s (f n) :=
    le_csSup (hb (f n)) ⟨w,⟨r,hr.trans (hq n),hw⟩,rfl⟩
  have happ : s (f n) - 1 / (n+1 : ℝ) < H.height z := happrox n (f n)
  linarith

end
end PartitionConsistency.DiagramOrder.HeightCost

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

/-- The directed filter generated by one condition; it is NOT called generic
and no meeting property is attributed to it. -/
def principalFilter (p : P) : GenericFilter P where
  carrier := {q | p ≤ q}
  lower' := fun _ _ h hp => hp.trans h
  nonempty' := ⟨p,le_rfl⟩
  directed' := fun _ hq _ hr => ⟨p,le_rfl,hq,hr⟩

@[simp] theorem mem_principalFilter (p q : P) : q ∈ principalFilter p ↔ p ≤ q := Iff.rfl

theorem AtomicData.eqG_principal {N : Type*} (A : AtomicData P N) (p : P) (σ τ : N) :
    A.EqG (principalFilter p) σ τ ↔ A.EqF p σ τ := by
  constructor
  · rintro ⟨q,hq,heq⟩
    exact A.eq_mono hq heq
  · intro h
    exact ⟨p,le_rfl,h⟩

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.CohenForcing.Condition
universe u
variable {I κ : Type u}

/-- Passing to a cone preserves countable closure. -/
theorem countably_closed_below (d : Condition I κ) (f : ℕ → Set.Iic d) (hf : Antitone f) :
    ∃ p : Set.Iic d, ∀ n, p ≤ f n := by
  obtain ⟨p,hp⟩ := countably_closed (fun n => (f n).val) (fun i j hij => hf hij)
  exact ⟨⟨p,(hp 0).trans (f 0).property⟩,hp⟩

end PartitionConsistency.CohenForcing.Condition


/-! ## StableAvailability -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ)
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)

/-- Availability when only equality forced by d is used. Each witness is an
actual normalized name on the required subdiagram. -/
def ForcedAvailable (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (τ : LocalName hμ c r) (n : M) : Prop :=
  ∃ σ : LocalName hμ c (r.sub n),
    (system hμ).atomic.EqF ((d,r) : Poset M I κ) σ.name τ.name

/-- The availability ideal of a specified local name with respect to any
directed filter. No dense-set meeting assumptions are required for this
purely algebraic ideal assertion. -/
def localAvailability (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) : ConeIdeal (show LeftDivOrder M from a) :=
  (allLocalSystem (c := c) hμ hcard hsize hmerger F).availability r a
    (LocalQuotient.ofName F τ)

theorem mem_localAvailability (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) (n : LeftDivOrder M) :
    n ∈ (localAvailability hμ c hcard hsize hmerger F r a τ).carrier ↔
      n ≤ a ∧ ∃ d : CohenForcing.Condition I κ, d ∈ F ∧ ForcedAvailable hμ c d r τ n := by
  change (n ≤ a ∧ ∃ x : LocalQuotient (c := c) hμ F (r.sub n),
    LocalQuotient.restrict F (r.self_le_sub n) x = LocalQuotient.ofName F τ) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨σ,rfl⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ F (r.sub n)) x
    obtain ⟨d,hd,he⟩ := (LocalQuotient.ofName_eq F (σ.restrict (r.self_le_sub n)) τ).mp hx
    exact ⟨d,hd,σ,he⟩
  · rintro ⟨d,hd,σ,he⟩
    refine ⟨LocalQuotient.ofName F σ,?_⟩
    exact (LocalQuotient.ofName_eq F (σ.restrict (r.self_le_sub n)) τ).mpr ⟨d,hd,he⟩

/-- The principal-filter availability ideal, built from the already proved
intersection/descent calculus. Its definition assumes no stability. -/
def forcedAvailability (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (a : M) (τ : LocalName hμ c r) : ConeIdeal (show LeftDivOrder M from a) :=
  localAvailability hμ c hcard hsize hmerger (principalFilter d) r a τ

theorem mem_forcedAvailability (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (a : M) (τ : LocalName hμ c r) (n : LeftDivOrder M) :
    n ∈ (forcedAvailability hμ c hcard hsize hmerger d r a τ).carrier ↔
      n ≤ a ∧ ForcedAvailable hμ c d r τ n := by
  rw [forcedAvailability,mem_localAvailability]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨s,hs,σ,he⟩
    exact ⟨σ,(system hμ).atomic.eq_mono
      (p := ((s,r) : Poset M I κ)) (q := ((d,r) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨hs,le_rfl⟩) he⟩
  · intro h
    exact ⟨d,show d ≤ d from le_rfl,h⟩

omit [Infinite M] [Infinite I] in
theorem ForcedAvailable.mono {d e : CohenForcing.Condition I κ} (hed : e ≤ d)
    {r : Diagram M I} {τ : LocalName hμ c r} {n : M}
    (h : ForcedAvailable hμ c d r τ n) : ForcedAvailable hμ c e r τ n := by
  obtain ⟨σ,hσ⟩ := h
  exact ⟨σ,(system hμ).atomic.eq_mono
    (p := ((d,r) : Poset M I κ)) (q := ((e,r) : Poset M I κ))
    (WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩) hσ⟩

theorem forcedAvailability_mono {d e : CohenForcing.Condition I κ} (hed : e ≤ d)
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) :
    (forcedAvailability hμ c hcard hsize hmerger d r a τ).carrier ⊆
      (forcedAvailability hμ c hcard hsize hmerger e r a τ).carrier := by
  intro n hn
  rw [mem_forcedAvailability] at hn ⊢
  exact ⟨hn.1,ForcedAvailable.mono hμ c hed hn.2⟩

/-- Forced equality identifies the two actual ideals, not just their
cardinalities. -/
theorem forcedAvailability_congr (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (a : M) (τ σ : LocalName hμ c r)
    (heq : (system hμ).atomic.EqF ((d,r) : Poset M I κ) τ.name σ.name) :
    forcedAvailability hμ c hcard hsize hmerger d r a τ =
      forcedAvailability hμ c hcard hsize hmerger d r a σ := by
  apply ConeIdeal.ext
  ext n
  rw [mem_forcedAvailability,mem_forcedAvailability]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨ν,hν⟩
    exact ⟨ν,(system hμ).atomic.eq_trans hν heq⟩
  · rintro ⟨ν,hν⟩
    exact ⟨ν,(system hμ).atomic.eq_trans hν ((system hμ).atomic.eq_symm heq)⟩

/-- The set of available subdiagrams of every local name can be made
permanently constant by strengthening only its Cohen coordinate. -/
theorem forcedAvailability_dense_stable (H : HeightCost (LeftDivOrder M))
    (hj : HasConditionalJoins (LeftDivOrder M)) (d : CohenForcing.Condition I κ)
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) :
    ∃ e, e ≤ d ∧ ∀ f, f ≤ e →
      forcedAvailability hμ c hcard hsize hmerger f r a τ =
        forcedAvailability hμ c hcard hsize hmerger e r a τ :=
  H.dense_stable_ideal CohenForcing.Condition.countably_closed hj
    (fun s => forcedAvailability hμ c hcard hsize hmerger s r a τ)
    (fun h => forcedAvailability_mono hμ c hcard hsize hmerger h r a τ) d

/-- Once availability is stable below d, its value in EVERY directed filter
containing d is the same ground ideal. This does not posit an ambient fully
generic filter or identify distinct forcing extensions. -/
theorem localAvailability_eq_of_stable
    (d : CohenForcing.Condition I κ) (r : Diagram M I) (a : M) (τ : LocalName hμ c r)
    (hstable : ∀ f, f ≤ d →
      forcedAvailability hμ c hcard hsize hmerger f r a τ =
        forcedAvailability hμ c hcard hsize hmerger d r a τ)
    (F : GenericFilter (CohenForcing.Condition I κ)) (hd : d ∈ F) :
    localAvailability hμ c hcard hsize hmerger F r a τ =
      forcedAvailability hμ c hcard hsize hmerger d r a τ := by
  apply ConeIdeal.ext
  ext n
  rw [mem_localAvailability,mem_forcedAvailability]
  apply and_congr_right
  intro hn
  constructor
  · rintro ⟨s,hs,hsa⟩
    obtain ⟨t,_,hts,htd⟩ := F.directed _ hs _ hd
    have ht : n ∈ (forcedAvailability hμ c hcard hsize hmerger t r a τ).carrier :=
      (mem_forcedAvailability hμ c hcard hsize hmerger t r a τ n).mpr
        ⟨hn,ForcedAvailable.mono hμ c hts hsa⟩
    rw [hstable t htd] at ht
    exact ((mem_forcedAvailability hμ c hcard hsize hmerger d r a τ n).mp ht).2
  · intro h
    exact ⟨d,hd,h⟩

end
end PartitionConsistency.ProductForcing

end OAI
