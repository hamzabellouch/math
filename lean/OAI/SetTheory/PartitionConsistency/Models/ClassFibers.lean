import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.OrdinalPresentation

namespace OAI

/-! ## LocalList -/

namespace PartitionConsistency.SetLanguage

/-- A set is wellorderable exactly when it embeds in some ordinal. Both
quantified witnesses are internal sets; the injection is an internal graph. -/
def wellorderableFormula : Formula 1 :=
  .ex ((ordinal 1).conj (.ex (injection 2 0 1)))

def wellorderable {n} (a : Fin n) : Formula n :=
  Formula.rename ![a] wellorderableFormula

end PartitionConsistency.SetLanguage

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
theorem forces_wellorderable {n} (v : Fin n → S.Name) (p : P) (a : Fin n) :
    S.Forces v p (SetLanguage.wellorderable a) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ η : S.Name,
        S.Forces ![η] r (SetLanguage.ordinal 0) ∧
        (∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ J : S.Name,
          S.Forces ![J,v a,η] t (SetLanguage.injection 0 1 2)) := by
  simp only [Forces,SetLanguage.wellorderable,SetLanguage.wellorderableFormula,
    S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj]
  have hordinal (η : S.Name) (r : P) :
      S.Forces (Fin.snoc (v ∘ ![a]) η) r (SetLanguage.ordinal 1) ↔
      S.Forces ![η] r (SetLanguage.ordinal 0) := by
    simp only [Forces,SetLanguage.ordinal,SetLanguage.transitiveSet,
      SetLanguage.membershipLinear,SetLanguage.membershipWellFounded,
      S.atomic.forceFormula_rename S.atomic_regular,
      ForcingQuotient.AtomicData.forceFormula_conj]
    have hv : (Fin.snoc (v ∘ ![a]) η) ∘ ![1] = ![η] ∘ ![0] := by
      funext i
      fin_cases i
      rfl
    rw [hv]
  have hinjection (η J : S.Name) (t : P) :
      S.Forces (Fin.snoc (Fin.snoc (v ∘ ![a]) η) J) t (SetLanguage.injection 2 0 1) ↔
      S.Forces ![J,v a,η] t (SetLanguage.injection 0 1 2) := by
    simp only [Forces,SetLanguage.injection,S.atomic.forceFormula_rename S.atomic_regular]
    have hv : (Fin.snoc (Fin.snoc (v ∘ ![a]) η) J) ∘ ![2,0,1] =
        ![J,v a,η] ∘ ![0,1,2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  simpa only [Forces] using (show (∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ η : S.Name,
      S.Forces (Fin.snoc (v ∘ ![a]) η) r (SetLanguage.ordinal 1) ∧
      (∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ J : S.Name,
        S.Forces (Fin.snoc (Fin.snoc (v ∘ ![a]) η) J) t (SetLanguage.injection 2 0 1))) ↔ _ from by
    simp only [hordinal,hinjection])

/-- Injecting a set into a checked ordinal is enough for the genuine
wellorderability formula. No ordinal preservation assumption is used. -/
theorem wellorderable_of_check_injection (Y J : S.Name) (α : Ordinal.{u}) (p : P)
    (h : S.Forces ![J,Y,Name.check α.toZFSet] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![Y] p (SetLanguage.wellorderable 0) := by
  rw [S.forces_wellorderable]
  intro q hqp
  exact ⟨q,le_rfl,Name.check α.toZFSet,S.forces_checkOrdinal α q,
    fun r hrq => ⟨r,le_rfl,J,S.atomic.forceFormula_mono (hrq.trans hqp) h⟩⟩

theorem no_check_injection_of_not_wellorderable (Y : S.Name) (p : P)
    (h : S.Forces ![Y] p (SetLanguage.wellorderable 0).neg) (α : Ordinal.{u}) :
    ∀ q, q ≤ p → ∀ J : S.Name,
      ¬ S.Forces ![J,Y,Name.check α.toZFSet] q (SetLanguage.injection 0 1 2) := by
  intro q hqp J hj
  exact (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mp h q hqp
    (S.wellorderable_of_check_injection Y J α q hj)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The range of all canonical E-classes of labels. For an equivalence
relation this is A/E, with the actual classes as its members. -/
def quotientName (E : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system hμ).collect (labelClass hμ c E) (fun _ _ => True)
    ((system hμ).tupleStabilizer ![E]) ((system hμ).tupleStabilizer_mem ![E]) (by
      intro π hπ j p hp
      refine ⟨π j,?_,trivial⟩
      have he : π • E = E := ((system hμ).mem_tupleStabilizer ![E] π).mp hπ 0
      rw [labelClass_move,he])

theorem mem_quotientName (E y : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Poset M I κ) :
    (system hμ).atomic.MemF p y (quotientName hμ c E) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j : I,
        (system hμ).atomic.EqF r y (labelClass hμ c E j) := by
  rw [quotientName,(system hμ).mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,j,_,_,_,he⟩ := h q hqp
    exact ⟨r,hrq,j,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,j,he⟩ := h q hqp
    exact ⟨r,hrq,j,r,trivial,le_rfl,he⟩

/-- Membership is exactly the first-order class predicate, not a quotient
surrogate supplied with the desired comparison property. -/
theorem mem_quotientName_iff_isClass
    (E y : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system hμ).atomic.MemF p y (quotientName hμ c E) ↔
      (system hμ).Forces ![y,labelSet hμ c,E] p (SetLanguage.isClass 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  rw [mem_quotientName,S.forces_isClass]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,j,he⟩ := h q hqp
    exact ⟨r,hrq,label hμ c j,label_mem_labelSet hμ c j r,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,hx,he⟩ := h q hqp
    obtain ⟨s,hsr,j,hxj⟩ := (mem_labelSet hμ c x r).mp hx r le_rfl
    exact ⟨s,hsr.trans hrq,j,S.atomic.eq_trans (S.atomic.eq_mono hsr he)
      (S.relationClass_congr (S.atomic.eq_refl s _) (S.atomic.eq_refl s _) hxj)⟩

theorem quotientName_fixed (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (π : Equiv.Perm I) (he : π • E = E) :
    π • quotientName hμ c E = quotientName hμ c E := by
  apply Subtype.ext
  refine (system hμ).collectName_fixed _ _ ((system hμ).tupleStabilizer ![E]) ?_ π ?_
  · intro σ hσ j p hp
    refine ⟨σ j,?_,trivial⟩
    have hs : σ • E = E := ((system hμ).mem_tupleStabilizer ![E] σ).mp hσ 0
    rw [labelClass_move,hs]
  · apply ((system hμ).mem_tupleStabilizer ![E] π).mpr
    intro j
    fin_cases j
    exact he

/-- A ground ordinal enumerating the entire normalized local-name set. -/
def localListOrdinal (r : Diagram M I) : Ordinal.{u} :=
  (exists_ordinal_equiv (LocalName hμ c r)).choose

def localListEquiv (r : Diagram M I) :
    (localListOrdinal hμ c r).toZFSet ≃ LocalName hμ c r :=
  (exists_ordinal_equiv (LocalName hμ c r)).choose_spec.some

def localListEntry (r : Diagram M I) (i : (localListOrdinal hμ c r).toZFSet) :
    (system (M := M) (I := I) (κ := κ) hμ).Name := (localListEquiv hμ c r i).name

theorem localListEntry_fixed (r : Diagram M I) (π : Equiv.Perm I)
    (hπ : π ∈ SupportFilter.Fix r.range) (i : (localListOrdinal hμ c r).toZFSet) :
    π • localListEntry hμ c r i = localListEntry hμ c r i :=
  (localListEquiv hμ c r i).fixed π hπ

theorem localList_support (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I) :
    SupportFilter.Fix r.range ∈ (system (M := M) (I := I) (κ := κ) hμ).filter :=
  ⟨r.range,(Diagram.cardinal_range r).trans_le hcard,le_rfl⟩

/-- The canonical evaluation list range, formed as a genuine HS name
with support D_r; its domain has been enumerated by a ground ordinal. -/
def localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).uniformRange
    (ι := (localListOrdinal hμ c r).toZFSet) (localListEntry hμ c r)
    (SupportFilter.Fix r.range)
    (localList_support (κ := κ) hμ hcard r)
    (by
      intro π hπ i
      exact localListEntry_fixed hμ c r π hπ i)

theorem localList_fixed (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (π : Equiv.Perm I) (hπ : π ∈ SupportFilter.Fix r.range) :
    π • localList hμ c hcard r = localList hμ c hcard r := by
  unfold localList
  exact (system (M := M) (I := I) (κ := κ) hμ).uniformRange_fixed (ι := (localListOrdinal hμ c r).toZFSet)
    (localListEntry hμ c r) (SupportFilter.Fix r.range)
    (localList_support (κ := κ) hμ hcard r) (localListEntry_fixed hμ c r) π hπ

theorem mem_localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (y : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system hμ).atomic.MemF p y (localList hμ c hcard r) ↔
      ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ ν : LocalName hμ c r,
        (system hμ).atomic.EqF s y ν.name := by
  unfold localList
  rw [(system (M := M) (I := I) (κ := κ) hμ).mem_uniformRange]
  constructor
  · intro h q hqp
    obtain ⟨s,hsq,i,he⟩ := h q hqp
    exact ⟨s,hsq,localListEquiv hμ c r i,he⟩
  · intro h q hqp
    obtain ⟨s,hsq,ν,he⟩ := h q hqp
    obtain ⟨i,rfl⟩ := (localListEquiv hμ c r).surjective ν
    exact ⟨s,hsq,i,he⟩

theorem localName_mem_localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (ν : LocalName hμ c r) (p : Poset M I κ) :
    (system hμ).atomic.MemF p ν.name (localList hμ c hcard r) :=
  (mem_localList hμ c hcard r ν.name p).mpr
    (fun q _ => ⟨q,le_rfl,ν,(system hμ).atomic.eq_refl q ν.name⟩)

/-- The list is wellorderable *inside* the symmetric interpretation,
via its least-occurrence injection into its checked index ordinal. -/
theorem localList_wellorderable (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (p : Poset M I κ) :
    (system hμ).Forces ![localList hμ c hcard r] p (SetLanguage.wellorderable 0) :=
  (system (M := M) (I := I) (κ := κ) hμ).wellorderable_of_check_injection _ _
    (localListOrdinal hμ c r) p
    ((system (M := M) (I := I) (κ := κ) hμ).uniformRangeInverse_injection
      (localListOrdinal hμ c r).toZFSet (localListEntry hμ c r) (SupportFilter.Fix r.range)
      (localList_support (κ := κ) hμ hcard r) (localListEntry_fixed hμ c r) p)

/-- Nonwellorderability supplies densely an actual E-class outside every
value on the local evaluation list. Nonmembership persists below the chosen
condition; it is not just a failure to decide membership. -/
theorem outside_localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (p : Poset M I κ)
    (hno : (system hμ).Forces ![quotientName hμ c E] p (SetLanguage.wellorderable 0).neg) :
    ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ y : (system hμ).Name,
      (system hμ).atomic.MemF s y (quotientName hμ c E) ∧
      ∀ t, t ≤ s → ¬ (system hμ).atomic.MemF t y (localList hμ c hcard r) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).outside_uniformRange
    (localListOrdinal hμ c r).toZFSet (localListEntry hμ c r)
    (quotientName hμ c E) (SupportFilter.Fix r.range)
    (localList_support (κ := κ) hμ hcard r) (localListEntry_fixed hμ c r)
    (fun π hπ => quotientName_fixed hμ c E π (hE π hπ)) p
  exact (system (M := M) (I := I) (κ := κ) hμ).no_check_injection_of_not_wellorderable
    _ p hno (localListOrdinal hμ c r)

end
end PartitionConsistency.ProductForcing


/-! ## OutsideClass -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- A class outside the *entire* local-name evaluation list, decided in a
literal stronger diagram that also contains all the condition coordinates.
The right factor of the root is recorded and is necessarily nontrivial. -/
def outsideClassSet (hcard : Cardinal.mk M ≤ μ) (p : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    Set (CohenForcing.Condition I κ) :=
  {d | ∃ (t : Diagram M I) (b : M), t.sub b = p ∧ b ≠ 1 ∧
    d.support ⊆ t.range ∧ ∃ j ∈ t.range,
      ∀ s : Poset M I κ, s ≤ (d,t) →
        ¬ (system hμ).atomic.MemF s (labelClass hμ c E j) (localList hμ c hcard p)}

/-- This is a local dense-set theorem derived from nonwellorderability, not
an additional assumption that the unavailable class exists. -/
theorem outsideClassSet_denseBelow [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e*x))ᶜ : Set M) = Cardinal.mk M)
    (p : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix p.range, π • E = E)
    (d₀ : CohenForcing.Condition I κ)
    (hno : (system hμ).Forces ![quotientName hμ c E] ((d₀,p) : Poset M I κ)
      (SetLanguage.wellorderable 0).neg) :
    ∀ d, d ≤ d₀ → ∃ a, a ≤ d ∧ a ∈ outsideClassSet hμ c hcard p E := by
  intro d hdd
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨s,hs,y,hy,hout⟩ := outside_localList hμ c hcard p E hE _ hno
    ((d,p) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hdd,le_rfl⟩)
  obtain ⟨u,hus,j,hyj⟩ := (mem_quotientName hμ c E y s).mp hy s le_rfl
  let : Nonempty (Diagram M I) := ⟨p⟩
  obtain ⟨a,hau⟩ := exists_condition_below u
  have hap := WithTop.coe_le_coe.mp ((hau.trans hus).trans hs)
  have hU : Cardinal.mk ↥(a.1.support ∪ {j}) ≤ Cardinal.mk M := by
    apply (Cardinal.mk_union_le _ _).trans
    have hω := Cardinal.aleph0_le_mk M
    apply (add_le_add (a.1.cardinal_support.trans hω) ?_).trans_eq (Cardinal.add_eq_self hω)
    simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hω
  obtain ⟨t,hta,hcover⟩ := Diagram.extend_through hsize e he a.2 hU
  have hta' : t ≤ a.2 := ⟨e,hta⟩
  have htu : ((a.1,t) : Poset M I κ) ≤ u :=
    (WithTop.coe_le_coe.mpr (show (a.1,t) ≤ a from ⟨le_rfl,hta'⟩)).trans hau
  have hts := htu.trans hus
  have hjt : j ∈ t.range := hcover (Or.inr (Set.mem_singleton j))
  have hnot : ∀ z : Poset M I κ, z ≤ (a.1,t) →
      ¬ S.atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard p) := by
    intro z hzt hz
    apply hout z (hzt.trans hts)
    exact (S.atomic.mem_congr (S.atomic.eq_mono (hzt.trans htu) hyj)
      (S.atomic.eq_refl z _)).mpr hz
  obtain ⟨b,hb⟩ := hta'.trans hap.2
  have hbn : b ≠ 1 := by
    intro h
    have htp : t = p := by simpa only [h,Diagram.sub_one] using hb
    have hjp : j ∈ p.range := htp ▸ hjt
    exact hnot (a.1,t) le_rfl
      (localName_mem_localList hμ c hcard p (localLabelClass hμ c p E hE j hjp) (a.1,t))
  exact ⟨a.1,hap.1,t,b,hb,hbn,fun k hk => hcover (Or.inl hk),j,hjt,hnot⟩

/-- The standard incompatible padding gives a dense set in the whole Cohen
forcing. This is the precise requirement to be met by the intermediate
ordinary extension. -/
def outsideClassDenseSet (hcard : Cardinal.mk M ≤ μ) (p : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (d₀ : CohenForcing.Condition I κ) :
    Set (CohenForcing.Condition I κ) :=
  {d | d ∈ outsideClassSet hμ c hcard p E ∨ ¬ Compatible d d₀}

theorem outsideClassDenseSet_dense [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e*x))ᶜ : Set M) = Cardinal.mk M)
    (p : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix p.range, π • E = E)
    (d₀ : CohenForcing.Condition I κ)
    (hno : (system hμ).Forces ![quotientName hμ c E] ((d₀,p) : Poset M I κ)
      (SetLanguage.wellorderable 0).neg) :
    Dense (outsideClassDenseSet hμ c hcard p E d₀) :=
  dense_local_or_incompatible d₀ _
    (outsideClassSet_denseBelow hμ c hcard hsize e he p E hE d₀ hno)

/-- An actual hit supplies the nontrivial witness used in the probe argument.
Only the explicitly identified dense set is mentioned here; this lemma does
not posit existence of an ambient filter meeting every ambient dense set. -/
theorem outsideClass_of_meets (hcard : Cardinal.mk M ≤ μ)
    (F : GenericFilter (CohenForcing.Condition I κ)) (p : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀ ∈ F)
    (hmeets : ∃ d, d ∈ F ∧ d ∈ outsideClassDenseSet hμ c hcard p E d₀) :
    ∃ d, d ∈ F ∧ d ∈ outsideClassSet hμ c hcard p E := by
  obtain ⟨d,hd,hm | hn⟩ := hmeets
  · exact ⟨d,hd,hm⟩
  · exact (hn (compatible_of_mem F hd hd₀)).elim

end
end PartitionConsistency.ProductForcing


/-! ## ClassFiber -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Persistent exclusion from the evaluation list of *all* local names at
p. This statement is expressed in the actual symmetric forcing relation. -/
def OutsideLocal (hcard : Cardinal.mk M ≤ μ) (p s : Diagram M I)
    (d : CohenForcing.Condition I κ) (σ : LocalName hμ c s) : Prop :=
  ∀ z : Poset M I κ, z ≤ (d,s) →
    ¬ (system hμ).atomic.MemF z σ.name (localList hμ c hcard p)

/-- A class outside the full evaluation list cannot be the inclusion of
any local quotient element at that root. Only membership of its witnessing
condition in the filter is used here. -/
theorem outsideLocal_not_image (hcard : Cardinal.mk M ≤ μ)
    (F : GenericFilter (CohenForcing.Condition I κ)) (p s : Diagram M I)
    (hsp : s ≤ p) (d : CohenForcing.Condition I κ) (hd : d ∈ F)
    (σ : LocalName hμ c s) (hout : OutsideLocal hμ c hcard p s d σ)
    (x : LocalQuotient (c := c) hμ F p) :
    LocalQuotient.restrict F hsp x ≠ LocalQuotient.ofName F σ := by
  induction x using Quotient.inductionOn with
  | h τ =>
    intro he
    obtain ⟨a,ha,heq⟩ := (LocalQuotient.ofName_eq F (τ.restrict hsp) σ).mp he
    obtain ⟨b,hb,hbd,hba⟩ := F.directed _ hd _ ha
    have hσ : (system hμ).atomic.EqF ((OrderDual.ofDual b,s) : Poset M I κ)
        σ.name τ.name := (system hμ).atomic.eq_symm
      ((system hμ).atomic.eq_mono
        (p := ((OrderDual.ofDual a,s) : Poset M I κ))
        (q := ((OrderDual.ofDual b,s) : Poset M I κ))
        (WithTop.coe_le_coe.mpr ⟨hba,le_rfl⟩) heq)
    apply hout (OrderDual.ofDual b,s) (WithTop.coe_le_coe.mpr ⟨hbd,le_rfl⟩)
    exact ((system hμ).atomic.mem_congr hσ ((system hμ).atomic.eq_refl _ _)).mpr
      (localName_mem_localList hμ c hcard p τ (OrderDual.ofDual b,s))

/-- Support descent over an exact intersection prevents an outside class
from equaling any element supported by the other diagram. -/
theorem outsideLocal_not_equal [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (d : CohenForcing.Condition I κ) (hd : d ∈ F) (σ : LocalName hμ c s₀)
    (hout : OutsideLocal hμ c hcard p s₀ d σ)
    (y : LocalQuotient (c := c) hμ F s₁) :
    LocalQuotient.restrict F hv₀ (LocalQuotient.ofName F σ) ≠
      LocalQuotient.restrict F hv₁ y := by
  intro he
  obtain ⟨x,hx,_⟩ := LocalQuotient.intersection F hcard hsize hmerger
    p s₀ s₁ v hs₀ hs₁ hinter hv₀ hv₁ (LocalQuotient.ofName F σ) y he
  exact outsideLocal_not_image hμ c hcard F p s₀ hs₀ d hd σ hout x hx

/-- A supported eligible class at any subdiagram gives a genuine element
of D_F(r), even when that subdiagram is not itself below q. -/
def classFromLocal [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q r s : Diagram M I) (hrq : r ≤ q) (hrs : r ≤ s)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (σ : LocalName hμ c s) (hσ : EligibleName hμ c F s E σ) :
    (eligibleSystem hμ c hcard hsize hmerger F q E hE).Obj r :=
  ⟨LocalQuotient.restrict F hrs (LocalQuotient.ofName F σ),hrq,
    eligible_restrict hμ c F E hrs (LocalQuotient.ofName F σ) hσ⟩

/-- The exact profile for a class on one probe. The positive availability
comes from retaining the name on larger ranges; the negative test is the
actual support-descent contradiction, not a multiplicity assumption. -/
theorem classFromLocal_profile [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q r p : Diagram M I) (a e m b : M) (hqa : r.sub a = q)
    (hp : r.sub (a*e) = p) (hmb : m*b = a*e)
    (U : ConeIdeal (show LeftDivOrder M from a))
    (hm : ∀ n : M, n ∣ a ∧ n ∣ m ↔ n ∈ U.carrier)
    (hinter : ∀ n : M, n ∣ a → n ∉ U.carrier →
      ∀ z : M, n ∣ z ∧ m ∣ z ↔ a*e ∣ z)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (σ : LocalName hμ c (r.sub m)) (hσ : EligibleName hμ c F (r.sub m) E σ)
    (d : CohenForcing.Condition I κ) (hd : d ∈ F)
    (hout : OutsideLocal hμ c hcard p (r.sub m) d σ) :
    (eligibleSystem hμ c hcard hsize hmerger F q E hE).availability r a
      (classFromLocal hμ c hcard hsize hmerger F q r (r.sub m)
        ⟨a,hqa⟩ (r.self_le_sub m) E hE σ hσ) = U := by
  let D := eligibleSystem hμ c hcard hsize hmerger F q E hE
  let x := classFromLocal hμ c hcard hsize hmerger F q r (r.sub m)
    ⟨a,hqa⟩ (r.self_le_sub m) E hE σ hσ
  have hmp : r.sub m ≤ p := ⟨b,by rw [Diagram.sub_sub,hmb,hp]⟩
  apply ConeIdeal.ext
  ext n
  change (n ≤ a ∧ D.Available r x n) ↔ n ∈ U.carrier
  constructor
  · rintro ⟨hna,y,hy⟩
    by_contra hnu
    have hnp : r.sub n ≤ p := by
      rw [← hp]
      exact r.sub_mono (hna.trans (LeftDivOrder.le_mul_right a e))
    have hi : (r.sub m).range ∩ (r.sub n).range = p.range := by
      rw [Set.inter_comm,← hp]
      exact r.range_inter_sub n m (a*e) (hinter n ((LeftDivOrder.le_iff_dvd _ _).mp hna) hnu)
    apply outsideLocal_not_equal hμ c hcard hsize hmerger F p (r.sub m) (r.sub n) r
      hmp hnp hi (r.self_le_sub _) (r.self_le_sub _) d hd σ hout y.val
    exact (congrArg Subtype.val hy).symm
  · intro hnu
    have hh := (hm n).mpr hnu
    have hna : n ≤ (a : LeftDivOrder M) := (LeftDivOrder.le_iff_dvd _ _).mpr hh.1
    have hnm : n ≤ (m : LeftDivOrder M) := (LeftDivOrder.le_iff_dvd _ _).mpr hh.2
    have hnq : r.sub n ≤ q := hqa ▸ r.sub_mono hna
    let y := classFromLocal hμ c hcard hsize hmerger F q (r.sub n) (r.sub m)
      hnq (r.sub_mono hnm) E hE σ hσ
    refine ⟨hna,y,?_⟩
    apply Subtype.ext
    exact LocalQuotient.restrict_restrict F (r.sub_mono hnm) (r.self_le_sub n)
      (LocalQuotient.ofName F σ)

/-- Distinct hit probes yield distinct symbolic classes, all in the exact
specified fiber. This map uses actual names, actual forcing eligibility,
and the proved intersection theorem. -/
def classFiberEmbedding [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    {q : Diagram M I} (w : Vertex q) (p : Diagram M I) (e b : M)
    (hp : w.diagram.sub (w.index*e) = p) {K : Type u} (m : K → M)
    (hmb : ∀ i, m i*b = w.index*e)
    (hm : ∀ i (n : M), n ∣ w.index ∧ n ∣ m i ↔ n ∈ w.ideal.carrier)
    (hinter : ∀ i (n : M), n ∣ w.index → n ∉ w.ideal.carrier →
      ∀ z : M, n ∣ z ∧ m i ∣ z ↔ w.index*e ∣ z)
    (hind : ∀ i j, i ≠ j → ∀ z : M, m i ∣ z ∧ m j ∣ z ↔ w.index*e ∣ z)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (σ : ∀ i, LocalName hμ c (w.diagram.sub (m i)))
    (hσ : ∀ i, EligibleName hμ c F (w.diagram.sub (m i)) E (σ i))
    (d : K → CohenForcing.Condition I κ) (hd : ∀ i, d i ∈ F)
    (hout : ∀ i, OutsideLocal hμ c hcard p (w.diagram.sub (m i)) (d i) (σ i)) :
    K ↪ (eligibleSystem hμ c hcard hsize hmerger F q E hE).vertexFiber w where
  toFun i := ⟨classFromLocal hμ c hcard hsize hmerger F q w.diagram
    (w.diagram.sub (m i)) ⟨w.index,w.root⟩ (w.diagram.self_le_sub _) E hE (σ i) (hσ i),
    classFromLocal_profile hμ c hcard hsize hmerger F q w.diagram p w.index e (m i) b
      w.root hp (hmb i) w.ideal (hm i) (hinter i) E hE (σ i) (hσ i) (d i) (hd i) (hout i)⟩
  inj' := by
    intro i j he
    by_contra hij
    have hip (k : K) : w.diagram.sub (m k) ≤ p :=
      ⟨b,by rw [Diagram.sub_sub,hmb k,hp]⟩
    have hi : (w.diagram.sub (m i)).range ∩ (w.diagram.sub (m j)).range = p.range := by
      rw [← hp]
      exact w.diagram.range_inter_sub (m i) (m j) (w.index*e) (hind i j hij)
    exact outsideLocal_not_equal hμ c hcard hsize hmerger F p
      (w.diagram.sub (m i)) (w.diagram.sub (m j)) w.diagram (hip i) (hip j) hi
      (w.diagram.self_le_sub _) (w.diagram.self_le_sub _) (d i) (hd i)
      (σ i) (hout i) (LocalQuotient.ofName F (σ j))
      (congrArg (fun z => z.val.val) he)

/-- Transport the actual outside label-class witness to all copies of its
diagram over p. The names remain normalized names in the stated local sets,
and their exclusions are forced at the transported conditions. -/
theorem outsideClass_copies (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (p r : Diagram M I) (a e b : M)
    (hp : r.sub (a*e) = p) {K : Type u} (m : K → M) (hm : ∀ i, m i*b = a*e)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix p.range, π • E = E)
    (t : Diagram M I) (ht : t.sub b = p)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : Poset M I κ, z ≤ (d,t) →
      ¬ (system hμ).atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard p)) :
    ∃ (d' : K → CohenForcing.Condition I κ) (σ : ∀ i, LocalName hμ c (r.sub (m i))),
      (∀ i, (d' i).support ⊆ (r.sub (m i)).range) ∧
      (∀ i, (d' i).restrict p.range = d.restrict p.range) ∧
      (∀ i z, (system hμ).Forces ![(σ i).name,labelSet hμ c,E] z (SetLanguage.isClass 0 1 2)) ∧
      ∀ i, OutsideLocal hμ c hcard p (r.sub (m i)) (d' i) (σ i) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hroots (i : K) : (r.sub (m i)).sub b = p := by rw [Diagram.sub_sub,hm i,hp]
  choose π hπ hfix using fun i : K =>
    Diagram.permutation_over_root hsize t (r.sub (m i)) p b ht (hroots i)
  have hip (i : K) : r.sub (m i) ≤ p := ⟨b,hroots i⟩
  have jmem (i : K) : π i j ∈ (r.sub (m i)).range := by
    rw [← hπ i,Diagram.range_permute]
    exact Set.mem_image_of_mem (π i) hj
  let σ (i : K) := localLabelClass hμ c (r.sub (m i)) E
    (supported_mono hμ (hip i) E hE) (π i j) (jmem i)
  refine ⟨fun i => d.permute (π i),σ,?_,?_,?_,?_⟩
  · intro i
    rw [CohenForcing.Condition.support_permute,← hπ i,Diagram.range_permute]
    exact Set.image_mono hd
  · intro i
    exact CohenForcing.Condition.restrict_permute_of_fixes _ _ (hfix i)
  · intro i z
    exact forces_localLabelClass_isClass hμ c _ E _ _ _ z
  · intro i z hz hzmem
    have hπp : π i ∈ SupportFilter.Fix p.range := (SupportFilter.mem_Fix _ _).mpr (hfix i)
    have he : π i • E = E := hE _ hπp
    have hn : π i • labelClass hμ c E j = (σ i).name := by
      change π i • labelClass hμ c E j = labelClass hμ c E (π i j)
      rw [labelClass_move,he]
    have hl : π i • localList hμ c hcard p = localList hμ c hcard p :=
      localList_fixed hμ c hcard p (π i) hπp
    have hmove : S.move (π i) ((d,t) : Poset M I κ) = (d.permute (π i),r.sub (m i)) := by
      rw [move_coe]
      change ((d.permute (π i),t.permute (π i)) : Poset M I κ) = _
      rw [hπ i]
    apply hout ((S.move (π i)).symm z)
    · apply (S.move (π i)).le_iff_le.mp
      rw [OrderIso.apply_symm_apply,hmove]
      exact hz
    · apply (S.mem_symmetry (π i) ((S.move (π i)).symm z) _ _).mpr
      rw [OrderIso.apply_symm_apply,hn,hl]
      exact hzmem

/-- A uniform family of genuinely dense Cohen requirements which forces the
lower exact-fiber bound. The requirements are built from transported copies
of one outside witness. Every filter meeting them has the displayed
embedding; no ambient filter is presumed to meet all ambient dense sets. -/
theorem classFiber_dense_lower [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) {q : Diagram M I} (w : Vertex q) (e b : M)
    {K : Type u} [Uncountable K] (m : K × K → M)
    (hmb : ∀ i, m i*b = w.index*e)
    (hm : ∀ i (n : M), n ∣ w.index ∧ n ∣ m i ↔ n ∈ w.ideal.carrier)
    (hinter : ∀ i (n : M), n ∣ w.index → n ∉ w.ideal.carrier →
      ∀ z : M, n ∣ z ∧ m i ∣ z ↔ w.index*e ∣ z)
    (hind : ∀ i j, i ≠ j → ∀ z : M, m i ∣ z ∧ m j ∣ z ↔ w.index*e ∣ z)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub e).range, π • E = E)
    (t : Diagram M I) (ht : t.sub b = q.sub e)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : Poset M I κ, z ≤ (d,t) →
      ¬ (system hμ).atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard (q.sub e))) :
    ∃ D : K → Set (CohenForcing.Condition I κ), (∀ i, Dense (D i)) ∧
      ∀ F : GenericFilter (CohenForcing.Condition I κ), d ∈ F →
        (∀ i, ∃ a, a ∈ F ∧ a ∈ D i) →
        Nonempty (K ↪ (eligibleSystem hμ c hcard hsize hmerger F q E
          (supported_mono hμ (q.self_le_sub e) E hE)).vertexFiber w) := by
  have hp : w.diagram.sub (w.index*e) = q.sub e := by rw [← Diagram.sub_sub,w.root]
  obtain ⟨d',σ,hs,hroot,hσ,hout'⟩ := outsideClass_copies hμ c hcard hsize
    (q.sub e) w.diagram w.index e b hp m hmb E hE t ht d hd j hj hout
  have hdisj : Pairwise (fun i k : K × K => Disjoint
      ((d' i).support \ (q.sub e).range) ((d' k).support \ (q.sub e).range)) := by
    intro i k hik
    rw [Set.disjoint_left]
    rintro z ⟨hzi,hzp⟩ ⟨hzk,_⟩
    apply hzp
    have hi := w.diagram.range_inter_sub (m i) (m k) (w.index*e) (hind i k hik)
    rw [hp] at hi
    exact hi ▸ ⟨hs i hzi,hs k hzk⟩
  let D (i : K) := CohenForcing.Condition.probeDenseSet
    (d.restrict (q.sub e).range) (fun k : K => d' (i,k))
  refine ⟨D,?_,?_⟩
  · intro i
    apply CohenForcing.Condition.probeDenseSet_dense (q.sub e).range
      (d.restrict (q.sub e).range) (fun k : K => d' (i,k)) (fun k => hroot (i,k))
    intro x y hxy
    exact hdisj (fun h => hxy (congrArg Prod.snd h))
  · intro F hdF hmeets
    have hits (i : K) : ∃ k : K, d' (i,k) ∈ F := by
      obtain ⟨k,a,ha,hle⟩ := CohenForcing.Condition.meets_probe F
        (F.lower (d.le_restrict _) hdF) (hmeets i)
      exact ⟨k,F.lower hle ha⟩
    choose k hk using hits
    let hEq := supported_mono hμ (q.self_le_sub e) E hE
    refine ⟨classFiberEmbedding hμ c hcard hsize hmerger F w (q.sub e) e b hp
      (fun i : K => m (i,k i)) (fun i => hmb (i,k i))
      (fun i => hm (i,k i)) (fun i => hinter (i,k i)) ?_
      E hEq (fun i => σ (i,k i)) ?_ (fun i => d' (i,k i)) hk (fun i => hout' (i,k i))⟩
    · intro i j hij
      exact hind (i,k i) (j,k j) (fun h => hij (congrArg Prod.fst h))
    · intro i
      exact ⟨d' (i,k i),hk i,hσ (i,k i) (d' (i,k i),w.diagram.sub (m (i,k i)))⟩

end
end PartitionConsistency.ProductForcing

end OAI
