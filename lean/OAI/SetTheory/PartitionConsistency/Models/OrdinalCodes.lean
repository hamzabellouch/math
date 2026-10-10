import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.PersistentCodes

namespace OAI

/-! ## OrdinalSelection -/

/-! A wellordered subset selected by forcing conditions has an actual
ordinal name for its order type and names for the ranks of its elements.
This construction uses ordinary set names, not evaluated ambient generics.
The pointwise invariance of each selection predicate gives literal fixation
of every rank name. -/
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hR : ∀ g ∈ H, ∀ x p, R x p → R x (S.move g p))

/-- Names literally fixed by one specified subgroup. -/
def FixedName (H : Subgroup Γ) := {σ : S.Name // ∀ g ∈ H, g • σ = σ}

namespace FixedName
variable {S H}

def collect {A : Type u} (f : A → S.FixedName H) (Q : A → P → Prop)
    (hQ : ∀ g ∈ H, ∀ a p, Q a p → Q a (S.move g p)) : S.FixedName H :=
  ⟨S.collect (fun a => (f a).val) Q H hH
      (fun g hg a p ha => ⟨a,((f a).property g hg).symm,hQ g hg a p ha⟩),
    fun g hg => Subtype.ext
      (S.collectName_fixed (fun a => (f a).val) Q H
        (fun g hg a p ha => ⟨a,((f a).property g hg).symm,hQ g hg a p ha⟩) g hg)⟩

omit [OrderTop P] in
theorem mem_collect {A : Type u} (f : A → S.FixedName H) (Q : A → P → Prop)
    (hQ : ∀ g ∈ H, ∀ a p, Q a p → Q a (S.move g p)) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (collect hH f Q hQ).val ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a c, Q a c ∧ r ≤ c ∧
        S.atomic.EqF r ν (f a).val :=
  S.mem_collect (fun a => (f a).val) Q H hH
    (fun g hg a p ha => ⟨a,((f a).property g hg).symm,hQ g hg a p ha⟩) ν p

end FixedName

/-- Rank in the selected suborder: recurse only along the fixed ground
wellordering. The predecessor set is small, with no bound on name ranks. -/
def selectedRankFixed (a : X) : S.FixedName H :=
  (IsWellOrder.wf (r := (· < ·))).fix
    (fun a f => FixedName.collect hH (fun b : {b : X // b < a} => f b.val b.property)
      (fun b p => R b.val p) (fun g hg b p => hR g hg b.val p)) a

def selectedRank (a : X) : S.Name := (S.selectedRankFixed R H hH hR a).val

/-- The ordinal consisting of the ranks of all selected elements. -/
def selectionType : S.Name :=
  (FixedName.collect hH (fun a => S.selectedRankFixed R H hH hR a) R hR).val

omit [OrderTop P] in
theorem selectedRank_fixed (a : X) (g : Γ) (hg : g ∈ H) :
    g • S.selectedRank R H hH hR a = S.selectedRank R H hH hR a :=
  (S.selectedRankFixed R H hH hR a).property g hg

omit [OrderTop P] in
theorem selectionType_fixed (g : Γ) (hg : g ∈ H) :
    g • S.selectionType R H hH hR = S.selectionType R H hH hR :=
  (FixedName.collect hH (fun a => S.selectedRankFixed R H hH hR a) R hR).property g hg

omit [OrderTop P] in
theorem selectedRankFixed_eq (a : X) : S.selectedRankFixed R H hH hR a =
    FixedName.collect hH (fun b : {b : X // b < a} => S.selectedRankFixed R H hH hR b.val)
      (fun b p => R b.val p) (fun g hg b p => hR g hg b.val p) := by
  unfold selectedRankFixed
  rw [WellFounded.fix_eq]

omit [OrderTop P] in
/-- Membership is densely witnessed by a selected smaller ground code. -/
theorem mem_selectedRank (a : X) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.selectedRank R H hH hR a) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ b, b < a ∧ ∃ c,
        R b c ∧ r ≤ c ∧ S.atomic.EqF r ν (S.selectedRank R H hH hR b) := by
  change S.atomic.MemF p ν (S.selectedRankFixed R H hH hR a).val ↔ _
  rw [S.selectedRankFixed_eq,FixedName.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,b,c,hb,hrc,he⟩ := h q hqp
    exact ⟨r,hrq,b.val,b.property,c,hb,hrc,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,b,hba,c,hb,hrc,he⟩ := h q hqp
    exact ⟨r,hrq,⟨b,hba⟩,c,hb,hrc,he⟩

omit [OrderTop P] in
theorem mem_selectionType (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.selectionType R H hH hR) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a c,
        R a c ∧ r ≤ c ∧ S.atomic.EqF r ν (S.selectedRank R H hH hR a) :=
  FixedName.mem_collect hH _ _ _ _ _

omit [OrderTop P] in
/-- Ranks of selected elements belong to the selected order type. -/
theorem selectedRank_mem_selectionType (a : X) (p : P) (ha : R a p) :
    S.atomic.MemF p (S.selectedRank R H hH hR a) (S.selectionType R H hH hR) := by
  apply (S.mem_selectionType R H hH hR _ p).mpr
  exact fun q hqp => ⟨q,le_rfl,a,p,ha,hqp,S.atomic.eq_refl q _⟩

omit [OrderTop P] in
theorem selectedRank_mem_selectedRank {a b : X} (hab : a < b) (p : P) (ha : R a p) :
    S.atomic.MemF p (S.selectedRank R H hH hR a) (S.selectedRank R H hH hR b) := by
  apply (S.mem_selectedRank R H hH hR b _ p).mpr
  exact fun q hqp => ⟨q,le_rfl,a,hab,p,ha,hqp,S.atomic.eq_refl q _⟩

omit [OrderTop P] in
/-- Taking a longer initial segment can only add members. -/
theorem selectedRank_subset {a b : X} (hab : a ≤ b) (p : P) :
    S.SubsetF p (S.selectedRank R H hH hR a) (S.selectedRank R H hH hR b) := by
  intro ν q _ hm
  apply (S.mem_selectedRank R H hH hR b ν q).mpr
  intro r hrq
  obtain ⟨s,hsr,c,hca,d,hc,hsd,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hm r hrq
  exact ⟨s,hsr,c,hca.trans_le hab,d,hc,hsd,he⟩

omit [OrderTop P] in
theorem selectedRank_subset_selectionType (a : X) (p : P) :
    S.SubsetF p (S.selectedRank R H hH hR a) (S.selectionType R H hH hR) := by
  intro ν q _ hm
  apply (S.mem_selectionType R H hH hR ν q).mpr
  intro r hrq
  obtain ⟨s,hsr,b,_,d,hb,hsd,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hm r hrq
  exact ⟨s,hsr,b,d,hb,hsd,he⟩

omit [OrderTop P] in
/-- The recursively defined ranks really are transitive sets. -/
theorem transF_selectedRank (a : X) (p : P) :
    S.TransF p (S.selectedRank R H hH hR a) := by
  intro ν χ q _ hν hχ
  apply S.atomic_regular.2
  intro r hrq
  obtain ⟨s,hsr,b,hba,d,_,_,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hν r hrq
  have hm := (S.atomic.mem_congr (S.atomic.eq_refl s χ) he).mp
    (S.atomic.mem_mono (hsr.trans hrq) hχ)
  exact ⟨s,hsr,S.selectedRank_subset R H hH hR hba.le s χ s le_rfl hm⟩

omit [OrderTop P] in
theorem transF_selectionType (p : P) : S.TransF p (S.selectionType R H hH hR) := by
  intro ν χ q _ hν hχ
  apply S.atomic_regular.2
  intro r hrq
  obtain ⟨s,hsr,b,d,_,_,he⟩ := (S.mem_selectionType R H hH hR ν q).mp hν r hrq
  have hm := (S.atomic.mem_congr (S.atomic.eq_refl s χ) he).mp
    (S.atomic.mem_mono (hsr.trans hrq) hχ)
  exact ⟨s,hsr,S.selectedRank_subset_selectionType R H hH hR b s χ s le_rfl hm⟩

omit [OrderTop P] in
/-- A member of any selected rank is itself transitive. -/
theorem ordF_selectedRank (a : X) (p : P) :
    S.OrdF p (S.selectedRank R H hH hR a) := by
  refine ⟨S.transF_selectedRank R H hH hR a p,?_⟩
  intro ν q _ hν χ ψ r hrq hχ hψ
  apply S.atomic_regular.2
  intro s hsr
  obtain ⟨t,hts,b,_,d,_,_,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hν s (hsr.trans hrq)
  have ht := (S.transF_congr he).mpr (S.transF_selectedRank R H hH hR b t)
  exact ⟨t,hts,ht χ ψ t le_rfl (S.atomic.mem_mono (hts.trans hsr) hχ)
    (S.atomic.mem_mono (hts.trans hsr) hψ)⟩

omit [OrderTop P] in
theorem ordF_selectionType (p : P) : S.OrdF p (S.selectionType R H hH hR) := by
  refine ⟨S.transF_selectionType R H hH hR p,?_⟩
  intro ν q _ hν χ ψ r hrq hχ hψ
  apply S.atomic_regular.2
  intro s hsr
  obtain ⟨t,hts,b,d,_,_,he⟩ := (S.mem_selectionType R H hH hR ν q).mp hν s (hsr.trans hrq)
  have ht := (S.transF_congr he).mpr (S.transF_selectedRank R H hH hR b t)
  exact ⟨t,hts,ht χ ψ t le_rfl (S.atomic.mem_mono (hts.trans hsr) hχ)
    (S.atomic.mem_mono (hts.trans hsr) hψ)⟩

/-- Ordinary ordinal decision applies to this actual, literally invariant
name; no cardinal assertion about an external-filter quotient is used. -/
theorem selectionType_decide (p : P) :
    ∃ q, q ≤ p ∧ ∃ θ : Ordinal.{u}, θ ≤ (S.selectionType R H hH hR).raw.rank ∧
      S.atomic.EqF q (S.selectionType R H hH hR) (Name.check θ.toZFSet) :=
  S.ordF_eq_check_le _ p (S.ordF_selectionType R H hH hR p)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SelectedRank -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hR : ∀ g ∈ H, ∀ x p, R x p → R x (S.move g p))

/-- No ordinal name can be forced to belong to itself. Ordinal decision
reduces this to irreflexivity in the genuine von Neumann ordinals. -/
theorem ordF_not_mem_self (σ : S.Name) (p : P) (ho : S.OrdF p σ) :
    ¬ S.atomic.MemF p σ σ := by
  intro hm
  obtain ⟨q,hqp,β,_,he⟩ := S.ordF_eq_check_le σ p ho
  have hh := (S.atomic.mem_congr he he).mp (S.atomic.mem_mono hqp hm)
  exact ZFSet.mem_irrefl _ ((S.mem_check_check _ _ q).mp hh)

/-- Distinct selected codes have distinct ordinal ranks, at every condition
where both are selected. This is an internal forcing assertion about the
actual ordinal names, not an assertion about an evaluated proxy order. -/
theorem selectedRank_eq_iff (a b : X) (p : P) (ha : R a p) (hb : R b p) :
    S.atomic.EqF p (S.selectedRank R H hH hR a) (S.selectedRank R H hH hR b) ↔ a = b := by
  constructor
  · intro he
    rcases lt_trichotomy a b with hab | hab | hab
    · have hm := S.selectedRank_mem_selectedRank R H hH hR hab p ha
      exact False.elim (S.ordF_not_mem_self _ p (S.ordF_selectedRank R H hH hR a p)
        ((S.atomic.mem_congr (S.atomic.eq_refl p _) (S.atomic.eq_symm he)).mp hm))
    · exact hab
    · have hm := S.selectedRank_mem_selectedRank R H hH hR hab p hb
      exact False.elim (S.ordF_not_mem_self _ p (S.ordF_selectedRank R H hH hR b p)
        ((S.atomic.mem_congr (S.atomic.eq_refl p _) he).mp hm))
  · rintro rfl
    exact S.atomic.eq_refl p _

/-- Deciding a selected rank under a decision of the total order type gives
an actual member of that ordinal. -/
theorem selectedRank_decide (a : X) (p : P) (ha : R a p) (θ : Ordinal.{u})
    (hθ : S.atomic.EqF p (S.selectionType R H hH hR) (Name.check θ.toZFSet)) :
    ∃ q, q ≤ p ∧ ∃ β : Set.Iio θ,
      S.atomic.EqF q (S.selectedRank R H hH hR a) (Name.check β.val.toZFSet) := by
  obtain ⟨q,hqp,β,_,hβ⟩ := S.ordF_eq_check_le _ p (S.ordF_selectedRank R H hH hR a p)
  have hm := S.atomic.mem_mono hqp (S.selectedRank_mem_selectionType R H hH hR a p ha)
  have ht := (S.atomic.mem_congr hβ (S.atomic.eq_mono hqp hθ)).mp hm
  exact ⟨q,hqp,⟨β,Ordinal.toZFSet_mem_toZFSet_iff.mp
    ((S.mem_check_check _ _ q).mp ht)⟩,hβ⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CohenSelection -/

/-! The ordinal coding of a condition-defined wellorder can be carried out
inside the product symmetric system itself. Its rank names have the given
tail support. Reflection to a supporting diagram permits all ordinal
decisions to be made by strengthening just the Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable [Infinite M] [Infinite I]
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
include hsize hmerger

/-- Reflection to the root, retaining the full Cohen condition. -/
theorem forces_at_root {n} (φ : Formula n)
    (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (r t : Diagram M I) (htr : t ≤ r)
    (hsup : ∀ π ∈ SupportFilter.Fix r.range, ∀ i, π • v i = v i)
    (d : CohenForcing.Condition I κ)
    (h : (system (M := M) (I := I) (κ := κ) hμ).Forces v ((d,t) : Poset M I κ) φ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces v ((d,r) : Poset M I κ) φ :=
  (system (M := M) (I := I) (κ := κ) hμ).atomic.forceFormula_mono
    (WithTop.coe_le_coe.mpr (show (d,r) ≤ (d.restrict r.range,r) from ⟨d.le_restrict _,le_rfl⟩))
    (forces_at_supporting_root hμ hsize hmerger φ v r t htr hsup d h)

theorem eq_at_root (τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (r t : Diagram M I) (htr : t ≤ r)
    (hτ : ∀ π ∈ SupportFilter.Fix r.range, π • τ = τ)
    (hσ : ∀ π ∈ SupportFilter.Fix r.range, π • σ = σ)
    (d : CohenForcing.Condition I κ)
    (h : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,t) : Poset M I κ) τ σ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ) τ σ := by
  have hh := forces_at_root hμ hsize hmerger (.equal 0 1) ![τ,σ] r t htr
    (by intro π hπ i; fin_cases i; exact hτ π hπ; exact hσ π hπ) d (by
      simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
        Matrix.cons_val_one] using h)
  simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
    Matrix.cons_val_one] using hh

/-- Every supported ordinal name can be decided by the Cohen coordinate
alone while the supporting root stays fixed. -/
theorem ordinal_decide_at_root (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (r : Diagram M I) (hτ : ∀ π ∈ SupportFilter.Fix r.range, π • τ = τ)
    (d : CohenForcing.Condition I κ)
    (ho : (system (M := M) (I := I) (κ := κ) hμ).OrdF ((d,r) : Poset M I κ) τ) :
    ∃ e, e ≤ d ∧ ∃ β : Ordinal.{u}, β ≤ τ.raw.rank ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) τ (Name.check β.toZFSet) := by
  let : Nonempty (Diagram M I) := ⟨r⟩
  obtain ⟨s,hs,β,hβ,he⟩ := (system (M := M) (I := I) (κ := κ) hμ).ordF_eq_check_le τ ((d,r) : Poset M I κ) ho
  obtain ⟨t,ht⟩ := exists_condition_below s
  have htd : t ≤ (d,r) := WithTop.coe_le_coe.mp (ht.trans hs)
  exact ⟨t.1,htd.1,β,hβ,eq_at_root hμ hsize hmerger τ (Name.check β.toZFSet) r t.2 htd.2
    hτ (fun π _ => Name.smul_check (system (M := M) (I := I) (κ := κ) hμ) π _) t.1 ((system (M := M) (I := I) (κ := κ) hμ).atomic.eq_mono ht he)⟩

omit hsize hmerger

namespace CohenSelection
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → CohenForcing.Condition I κ → Prop)
variable (H : Subgroup (Equiv.Perm I)) (hH : H ∈ (system (M := M) (I := I) (κ := κ) hμ).filter)
variable (hR : ∀ π ∈ H, ∀ a d, R a d → R a (d.permute π))

/-- Only the Cohen coordinate is examined. No diagram-generic or ambient
fully generic filter occurs in this predicate. -/
def lift (a : X) (p : Poset M I κ) : Prop :=
  ∃ (d : CohenForcing.Condition I κ) (r : Diagram M I), p = ((d,r) : Poset M I κ) ∧ R a d

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] [Infinite M] [Infinite I]
  [IsWellOrder X (· < ·)] [LinearOrder X] in
@[simp] theorem lift_coe (a : X) (d : CohenForcing.Condition I κ) (r : Diagram M I) :
    lift (M := M) R a ((d,r) : Poset M I κ) ↔ R a d := by
  constructor
  · rintro ⟨e,s,he,ha⟩
    have hh : (d,r) = (e,s) := WithTop.coe_injective he
    have hde : d = e := congrArg Prod.fst hh
    exact hde.symm ▸ ha
  · exact fun h => ⟨d,r,rfl,h⟩

include hR in
omit [Infinite M] [Infinite I] [IsWellOrder X (· < ·)] [LinearOrder X] in
theorem lift_covariance (π : Equiv.Perm I) (hπ : π ∈ H) (a : X) (p : Poset M I κ)
    (ha : lift (M := M) R a p) : lift (M := M) R a ((system (M := M) (I := I) (κ := κ) hμ).move π p) := by
  obtain ⟨d,r,rfl,ha⟩ := ha
  rw [move_coe]
  exact ⟨d.permute π,r.permute π,rfl,hR π hπ a d ha⟩

/-- The literal names used for the ordinal ranks and order type. -/
def rank (a : X) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank (lift (M := M) R) H hH (lift_covariance (M := M) hμ R H hR) a

def orderType : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).selectionType (lift (M := M) R) H hH (lift_covariance (M := M) hμ R H hR)

omit [Infinite M] [Infinite I] in
theorem rank_fixed (a : X) (π : Equiv.Perm I) (hπ : π ∈ H) :
    π • rank hμ R H hH hR a = rank hμ R H hH hR a :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank_fixed _ _ _ _ a π hπ

omit [Infinite M] [Infinite I] in
theorem orderType_fixed (π : Equiv.Perm I) (hπ : π ∈ H) :
    π • orderType hμ R H hH hR = orderType hμ R H hH hR :=
  (system (M := M) (I := I) (κ := κ) hμ).selectionType_fixed _ _ _ _ π hπ

variable (r : Diagram M I) (hroot : SupportFilter.Fix r.range ≤ H)

include hsize hmerger hroot in
theorem orderType_decide (d : CohenForcing.Condition I κ) :
    ∃ e, e ≤ d ∧ ∃ θ : Ordinal.{u}, θ ≤ (orderType hμ R H hH hR).raw.rank ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) (orderType hμ R H hH hR) (Name.check θ.toZFSet) :=
  ordinal_decide_at_root hμ hsize hmerger _ r
    (fun π hπ => orderType_fixed hμ R H hH hR π (hroot hπ)) d
    ((system (M := M) (I := I) (κ := κ) hμ).ordF_selectionType _ _ _ _ _)

omit [Infinite M] [Infinite I] in
theorem rank_eq_iff (a b : X) (d : CohenForcing.Condition I κ) (ha : R a d) (hb : R b d) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ)
      (rank hμ R H hH hR a) (rank hμ R H hH hR b) ↔ a = b :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank_eq_iff _ _ _ _ a b _
    ((lift_coe R a d r).mpr ha) ((lift_coe R b d r).mpr hb)

omit [Infinite M] [Infinite I] in
theorem rank_mem (a : X) (d : CohenForcing.Condition I κ) (ha : R a d) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF ((d,r) : Poset M I κ)
      (rank hμ R H hH hR a) (orderType hμ R H hH hR) :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank_mem_selectionType _ _ _ _ a _ ((lift_coe R a d r).mpr ha)

include hsize hmerger hroot in
/-- Ranks are decided without changing the chosen root diagram. -/
theorem rank_decide (a : X) (d : CohenForcing.Condition I κ) (ha : R a d) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ)
      (orderType hμ R H hH hR) (Name.check θ.toZFSet)) :
    ∃ e, e ≤ d ∧ ∃ β : Set.Iio θ,
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) (rank hμ R H hH hR a) (Name.check β.val.toZFSet) := by
  obtain ⟨e,hed,β,_,hb⟩ := ordinal_decide_at_root hμ hsize hmerger (rank hμ R H hH hR a) r
    (fun π hπ => rank_fixed hμ R H hH hR a π (hroot hπ)) d
    ((system (M := M) (I := I) (κ := κ) hμ).ordF_selectedRank _ _ _ _ a _)
  have hle : ((e,r) : Poset M I κ) ≤ ((d,r) : Poset M I κ) := WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩
  have hm := (system (M := M) (I := I) (κ := κ) hμ).atomic.mem_mono hle (rank_mem hμ R H hH hR r a d ha)
  have hm' := ((system (M := M) (I := I) (κ := κ) hμ).atomic.mem_congr hb ((system (M := M) (I := I) (κ := κ) hμ).atomic.eq_mono hle hθ)).mp hm
  exact ⟨e,hed,⟨β,Ordinal.toZFSet_mem_toZFSet_iff.mp
    (((system (M := M) (I := I) (κ := κ) hμ).mem_check_check _ _ ((e,r) : Poset M I κ)).mp hm')⟩,hb⟩

include hsize hmerger hroot in
/-- Every member of a decided order type is densely the rank of a selected
code. Extraction uses actual collection-name entries. -/
theorem member_rank (hmono : ∀ {a d e}, e ≤ d → R a d → R a e)
    (d : CohenForcing.Condition I κ) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ)
      (orderType hμ R H hH hR) (Name.check θ.toZFSet)) (β : Set.Iio θ) :
    ∃ e, e ≤ d ∧ ∃ a, R a e ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) (rank hμ R H hH hR a) (Name.check β.val.toZFSet) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨r⟩
  have hm : S.atomic.MemF ((d,r) : Poset M I κ) (Name.check β.val.toZFSet)
      (orderType hμ R H hH hR) :=
    (S.atomic.mem_congr (S.atomic.eq_refl _ _) (S.atomic.eq_symm hθ)).mp
      (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr β.property) _)
  obtain ⟨s,hs,a,c,ha,hsc,hea⟩ :=
    (S.mem_selectionType _ _ _ _ _ ((d,r) : Poset M I κ)).mp hm ((d,r) : Poset M I κ) le_rfl
  obtain ⟨f,t,hc,ha⟩ := ha
  obtain ⟨u,hu⟩ := exists_condition_below s
  have hud : u ≤ (d,r) := WithTop.coe_le_coe.mp (hu.trans hs)
  have huf : u ≤ (f,t) := WithTop.coe_le_coe.mp (hc ▸ hu.trans hsc)
  refine ⟨u.1,hud.1,a,hmono huf.1 ha,?_⟩
  exact eq_at_root hμ hsize hmerger _ _ r u.2 hud.2
    (fun π hπ => rank_fixed hμ R H hH hR a π (hroot hπ))
    (fun π _ => Name.smul_check (system (M := M) (I := I) (κ := κ) hμ) π _) u.1
    (S.atomic.eq_symm (S.atomic.eq_mono hu hea))

end CohenSelection
end
end PartitionConsistency.ProductForcing


/-! ## CodeRoot -/

/-! Connecting the persistent ground codes to literal root-supported names.
The comparison of two codes is equivalent to forced equality of any of their
root representatives. No generic evaluator is presumed in this step. -/
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

/-- A code represents a particular root name from some index onward. -/
def Rooted (a : ChainCode hμ c C) (d : CohenForcing.Condition I κ)
    (τ : LocalName hμ c v.diagram) : Prop :=
  ∃ N, ∀ i, N ≤ i → (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) (a i).name τ.name

variable {hμ c C}

omit [Infinite M] [Infinite I] in
theorem rooted_mono {a : ChainCode hμ c C} {d e : CohenForcing.Condition I κ}
    {τ : LocalName hμ c v.diagram} (hed : e ≤ d) (h : Rooted hμ c C a d τ) :
    Rooted hμ c C a e τ := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => (system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (e,v.diagram) ≤ (d,v.diagram) from ⟨hed,le_rfl⟩)) (hN i hi)⟩

include hsize hmerger in
/-- All root representatives induce exactly the same code equivalence. -/
theorem rooted_eq_iff_same {a b : ChainCode hμ c C} {d : CohenForcing.Condition I κ}
    {τ σ : LocalName hμ c v.diagram} (ha : Rooted hμ c C a d τ) (hb : Rooted hμ c C b d σ) :
    (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) τ.name σ.name ↔ Same hμ c C d a b := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hb
  have hr (i : ℕ) : v.diagram ≤ (C.vertex i).diagram := by
    obtain ⟨f⟩ := C.increasing 0 i (Nat.zero_le i)
    have h : (C.vertex 0).diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
    simpa only [C.first] using h
  have he (i : ℕ) (hn : N ≤ i) (hl : L ≤ i) :
      (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) τ.name σ.name ↔
        (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name := by
    constructor
    · intro h
      exact eq_at_root hμ hsize hmerger _ _ (C.vertex i).diagram v.diagram (hr i)
        (a i).fixed (b i).fixed d
        ((system hμ).atomic.eq_trans (hN i hn) ((system hμ).atomic.eq_trans h
          ((system hμ).atomic.eq_symm (hL i hl))))
    · intro h
      have h' := (system hμ).atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (d,v.diagram) ≤ (d,(C.vertex i).diagram) from ⟨le_rfl,hr i⟩)) h
      exact (system hμ).atomic.eq_trans ((system hμ).atomic.eq_symm (hN i hn))
        ((system hμ).atomic.eq_trans h' (hL i hl))
  constructor
  · intro h
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)
      ((le_max_right _ _).trans hi)).mp h⟩
  · rintro ⟨K,hK⟩
    exact (he (max (max N L) K) ((le_max_left N L).trans (le_max_left _ _))
      ((le_max_right N L).trans (le_max_left _ _))).mpr (hK _ (le_max_right _ _))

variable (hμ c C)

/-- Every persistent code has an eligible normalized name at its root.
The proof uses the genuine bijective local restriction maps. -/
theorem working_rooted (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a) :
    ∃ τ : LocalName hμ c v.diagram,
      (system hμ).Forces ![τ.name,labelSet hμ c,E]
        ((d,v.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2) ∧
      Rooted hμ c C a d τ := by
  obtain ⟨b,N,hN⟩ := ha d le_rfl
  obtain ⟨x,hx⟩ := (D[principalFilter d]).toGlued_surjective hj v v (Vertex.Common.refl v) b
  obtain ⟨τ,hτ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ
    (principalFilter d) v.diagram) x.val.val
  change LocalQuotient.ofName (principalFilter d) τ = x.val.val at hτ
  have hel : EligibleName hμ c (principalFilter d) v.diagram E τ := by
    apply (eligible_ofName hμ c (principalFilter d) v.diagram E τ).mp
    rw [hτ]
    exact x.val.property.2
  obtain ⟨e,he,hel⟩ := hel
  refine ⟨τ,(system hμ).atomic.forceFormula_mono
    (WithTop.coe_le_coe.mpr (show (d,v.diagram) ≤ (e,v.diagram) from
      ⟨(mem_principalFilter d e).mp he,le_rfl⟩)) hel,N,?_⟩
  intro i hi
  obtain ⟨hw,y,σ,hσ,hy,hb⟩ := hN i hi
  have hσ' : σ = a i := LocalName.ext hσ
  subst σ
  have harr : Nonempty (v.Arrow (C.vertex i)) := by
    simpa only [C.first] using C.increasing 0 i (Nat.zero_le i)
  let f := harr.some
  have hf : v.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  have hexy : (D[principalFilter d]).arrowMap hj f y = x := by
    apply (D[principalFilter d]).toGlued_injective hj v v (Vertex.Common.refl v)
    rw [(D[principalFilter d]).toGlued_arrow hj v v (C.vertex i)
      (Vertex.Common.refl v) hw f y,hb,hx]
  apply ((localAtomic hμ v.diagram).eqG_principal d _ _).mp
  apply (LocalQuotient.ofName_eq (principalFilter d) ((a i).restrict hf) τ).mp
  calc
    LocalQuotient.ofName (principalFilter d) ((a i).restrict hf) =
        LocalQuotient.restrict (principalFilter d) hf y.val.val :=
      congrArg (LocalQuotient.restrict (principalFilter d) hf) hy
    _ = x.val.val := congrArg (fun z : (D[principalFilter d]).vertexFiber v => z.val.val) hexy
    _ = LocalQuotient.ofName (principalFilter d) τ := hτ.symm

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## OrderAssignment -/

/-! Enumeration using one fixed, bounded table of bijections with ordinals.
This is the order-theoretic part of the preliminary component assignment.
The table is chosen once and never depends on the wellordered set being
enumerated. -/
namespace PartitionConsistency.OrderAssignment
universe u v w
noncomputable section

/-- A set-indexed table, bounded by the order type of the ground code set. -/
def Table (L : Type u) (Λ : Ordinal.{u}) :=
  ∀ θ : Set.Iic Λ, θ.val.card = Cardinal.mk L → L ≃ θ.val.ToType

def chooseTable (L : Type u) (Λ : Ordinal.{u}) : Table L Λ :=
  fun θ h => Classical.choice (Cardinal.eq.mp (by rw [Cardinal.mk_toType,h]))

variable {L A B : Type u} {Λ : Ordinal.{u}}

/-- Transfer the fixed table's indices to ordinal initial segments. -/
def indices (e : Table L Λ) (θ : Ordinal.{u}) (hb : θ ≤ Λ)
    (hc : θ.card = Cardinal.mk L) : L ≃ Set.Iio θ :=
  (e ⟨θ,hb⟩ hc).trans Ordinal.ToType.mk.toEquiv.symm

theorem indices_val_congr (e : Table L Λ) {θ θ' : Ordinal.{u}} (he : θ = θ')
    (hb : θ ≤ Λ) (hb' : θ' ≤ Λ) (hc : θ.card = Cardinal.mk L)
    (hc' : θ'.card = Cardinal.mk L) (j : L) :
    (indices e θ hb hc j).val = (indices e θ' hb' hc' j).val := by
  subst θ'
  rfl

/-- Unique enumeration of a wellordered set after the single fixed choice
of its ordinal indexing bijection. -/
def assignment (e : Table L Λ) (r : A → A → Prop) [IsWellOrder A r]
    (hb : Ordinal.type r ≤ Λ) (hc : Cardinal.mk A = Cardinal.mk L) : L ≃ A :=
  (indices e (Ordinal.type r) hb ((Ordinal.card_type r).trans hc)).trans
    (Ordinal.enum r).toEquiv

/-- The same ordinal table entry is used under an arbitrary wellorder
isomorphism. This is the naturality needed for tail-fixed codes. -/
theorem assignment_natural (e : Table L Λ) {r : A → A → Prop} {s : B → B → Prop}
    [IsWellOrder A r] [IsWellOrder B s]
    (hb : Ordinal.type r ≤ Λ) (hc : Cardinal.mk A = Cardinal.mk L)
    (hb' : Ordinal.type s ≤ Λ) (hc' : Cardinal.mk B = Cardinal.mk L)
    (f : r ≃r s) (j : L) :
    f (assignment e r hb hc j) = assignment e s hb' hc' j := by
  have he := f.ordinalType_congr
  have hi : (indices e (Ordinal.type r) hb ((Ordinal.card_type r).trans hc) j).val =
      (indices e (Ordinal.type s) hb' ((Ordinal.card_type s).trans hc') j).val :=
    indices_val_congr e he _ _ _ _ j
  change f (Ordinal.enum r _) = Ordinal.enum s _
  let x := indices e (Ordinal.type r) hb ((Ordinal.card_type r).trans hc) j
  let y := indices e (Ordinal.type s) hb' ((Ordinal.card_type s).trans hc') j
  have hx : x.val < Ordinal.type s := x.property.trans_eq he
  exact (Ordinal.relIso_enum' f x.val x.property hx).trans
    (congrArg (Ordinal.enum s) (Subtype.ext hi))

variable {X : Type v} {Y : Type w} [Small.{u} X] [Small.{u} Y]

/-- Shrinking only changes the carrier; the selected relation is retained. -/
def smallRel (r : X → X → Prop) : Shrink.{u} X → Shrink.{u} X → Prop :=
  InvImage r (equivShrink X).symm

instance smallRel_isWellOrder (r : X → X → Prop) [IsWellOrder X r] :
    IsWellOrder (Shrink.{u} X) (smallRel r) where
  wf := InvImage.wf (equivShrink X).symm IsWellOrder.wf
  trichotomous := @Std.Trichotomous.trichotomous _
    (InvImage r (equivShrink X).symm)
    (InvImage.trichotomous (r := r) (equivShrink X).symm.injective)

/-- The shrinking isomorphism of wellorders uses no new ordering choice. -/
def smallIso {r : X → X → Prop} {s : Y → Y → Prop} (f : r ≃r s) :
    smallRel.{u} r ≃r smallRel.{u} s where
  toEquiv := (equivShrink X).symm.trans (f.toEquiv.trans (equivShrink Y))
  map_rel_iff' := by
    intro a b
    change s ((equivShrink Y).symm ((equivShrink Y) (f _)))
      ((equivShrink Y).symm ((equivShrink Y) (f _))) ↔ r _ _
    simp only [Equiv.symm_apply_apply,f.map_rel_iff]

/-- Only the small ordinal of the shrunk relation indexes the table. -/
def smallAssignment (e : Table L Λ) (r : X → X → Prop) [IsWellOrder X r]
    (hb : Ordinal.type (smallRel.{u} r) ≤ Λ)
    (hc : Cardinal.mk (Shrink.{u} X) = Cardinal.mk L) : L ≃ X :=
  (assignment e (smallRel r) hb hc).trans (equivShrink X).symm

theorem smallAssignment_natural (e : Table L Λ)
    {r : X → X → Prop} {s : Y → Y → Prop} [IsWellOrder X r] [IsWellOrder Y s]
    (hb : Ordinal.type (smallRel.{u} r) ≤ Λ)
    (hc : Cardinal.mk (Shrink.{u} X) = Cardinal.mk L)
    (hb' : Ordinal.type (smallRel.{u} s) ≤ Λ)
    (hc' : Cardinal.mk (Shrink.{u} Y) = Cardinal.mk L) (f : r ≃r s) (j : L) :
    f (smallAssignment e r hb hc j) = smallAssignment e s hb' hc' j := by
  have h := assignment_natural e hb hc hb' hc' (smallIso f) j
  have hh := congrArg (equivShrink Y).symm h
  simpa only [smallAssignment,smallIso,RelIso.coe_fn_mk,Equiv.trans_apply,Equiv.symm_apply_apply,RelIso.coe_fn_toEquiv] using hh

/-- An injection into the code set gives the stated ordinal bound when the
wellorder of objects is the pullback of the code wellorder. -/
theorem type_smallRel_le {r : X → X → Prop} {s : Y → Y → Prop}
    [IsWellOrder X r] [IsWellOrder Y s] (f : r ↪r s) :
    Ordinal.type (smallRel.{u} r) ≤ Ordinal.type (smallRel.{u} s) := by
  let g : smallRel.{u} r ↪r smallRel.{u} s := {
    toFun := fun a => equivShrink Y (f ((equivShrink X).symm a))
    inj' := (equivShrink Y).injective.comp (f.injective.comp (equivShrink X).symm.injective)
    map_rel_iff' := by
      intro a b
      change s ((equivShrink Y).symm ((equivShrink Y) (f _)))
        ((equivShrink Y).symm ((equivShrink Y) (f _))) ↔ r _ _
      simp only [Equiv.symm_apply_apply,f.map_rel_iff] }
  exact g.ordinal_type_le

end
end PartitionConsistency.OrderAssignment

end OAI
