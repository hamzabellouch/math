import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.ProductNames
import OAI.SetTheory.PartitionConsistency.Forcing.SupportFilter

namespace OAI

/-! ## OutsideLabel -/

namespace PartitionConsistency.SupportFilter
universe u
variable {I : Type u} {J : Set I} {π : Equiv.Perm I}

theorem perm_mem_iff (hπ : π ∈ Fix J) (j : I) : π j ∈ J ↔ j ∈ J := by
  have hf := (mem_Fix J π).mp hπ
  constructor
  · intro hj
    have he : π j = j := π.injective (hf (π j) hj)
    rwa [he] at hj
  · intro hj
    rwa [hf j hj]

end PartitionConsistency.SupportFilter

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The set of labels outside a specified small set. Every entry remains a
literal Cohen label, and its support is the specified small set. -/
def labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect (label (M := M) hμ c)
    (fun j p => j ∉ J ∧ p = ⊤) (SupportFilter.Fix J) ⟨J,hJ,le_rfl⟩ (by
      intro π hπ j p hp
      refine ⟨π j,(smul_label (M := M) hμ c π j).symm,?_,?_⟩
      · exact fun h => hp.1 ((SupportFilter.perm_mem_iff hπ j).mp h)
      · simpa only [hp.2] using (move_top (M := M) (I := I) (κ := κ) hμ π))

@[simp] theorem labelOutside_raw (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ) :
    (labelOutside (M := M) hμ c J hJ).raw =
      (system (M := M) (I := I) (κ := κ) hμ).collectRaw (label (M := M) hμ c)
        (fun j p => j ∉ J ∧ p = ⊤) := rfl

theorem smul_labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (π : Equiv.Perm I) (hπ : π ∈ SupportFilter.Fix J) :
    π • labelOutside (M := M) hμ c J hJ = labelOutside (M := M) hμ c J hJ := by
  apply Name.ext
  rw [Name.smul_val,labelOutside_raw]
  apply (system (M := M) (I := I) (κ := κ) hμ).collectRaw_move _ _ _ _ π π
  · exact smul_label (M := M) hμ c π
  · intro j p
    apply and_congr (not_congr (SupportFilter.perm_mem_iff hπ j).symm)
    constructor
    · rintro rfl; exact move_top hμ π
    · intro hp
      apply ((system (M := M) (I := I) (κ := κ) hμ).move π).injective
      rw [hp,move_top]

theorem label_mem_labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    {j : I} (hj : j ∉ J) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (label (M := M) hμ c j)
      (labelOutside (M := M) hμ c J hJ) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).mem_of_edge (c := ⊤) ?_ le_top
  rw [labelOutside_raw]
  exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr
    ⟨j,⊤,⟨hj,rfl⟩,rfl,rfl⟩

theorem mem_labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (labelOutside (M := M) hμ c J hJ) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j : I, j ∉ J ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν (label (M := M) hμ c j) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,d,he,_,heq⟩ := (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mp h q hqp
    rw [labelOutside_raw] at he
    obtain ⟨j,_,hj,hτ,_⟩ := ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mp he
    have hh : label (M := M) hμ c j = τ := Name.ext hτ
    exact ⟨r,hrq,j,hj.1,hh ▸ heq⟩
  · intro h
    apply (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,j,hj,heq⟩ := h q hqp
    refine ⟨r,hrq,label (M := M) hμ c j,⊤,?_,le_top,heq⟩
    rw [labelOutside_raw]
    exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr
      ⟨j,⊤,⟨hj,rfl⟩,rfl,rfl⟩

theorem labelOutside_subset (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (p : Poset M I κ) : (system (M := M) (I := I) (κ := κ) hμ).SubsetF p
      (labelOutside (M := M) hμ c J hJ) (labelSet (M := M) (I := I) hμ c) := by
  intro ν q hqp hν
  apply (mem_labelSet hμ c ν q).mpr
  intro r hrq
  obtain ⟨s,hsr,j,_,heq⟩ := (mem_labelOutside hμ c J hJ ν q).mp hν r hrq
  exact ⟨s,hsr,j,heq⟩

/-- The internal family P(A) minus the empty set, formed by the actual
Power Set and Separation constructions. Quantified subsets have no rank bound. -/
def choiceFailureFamily (c : κ → ZFSet.{u}) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).separate
    ((system (M := M) (I := I) (κ := κ) hμ).power (labelSet (M := M) (I := I) hμ c))
    Fin.elim0 (SetLanguage.nonempty 0)

theorem mem_choiceFailureFamily (c : κ → ZFSet.{u})
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (choiceFailureFamily (M := M) (I := I) hμ c) ↔
      (system (M := M) (I := I) (κ := κ) hμ).SubsetF p ν (labelSet (M := M) (I := I) hμ c) ∧
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ τ, (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF r τ ν := by
  rw [choiceFailureFamily,(system (M := M) (I := I) (κ := κ) hμ).mem_separate,
    (system (M := M) (I := I) (κ := κ) hμ).mem_power,
    (system (M := M) (I := I) (κ := κ) hμ).forces_nonempty]
  rfl

theorem labelOutside_mem_family (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (hj : ∃ j : I, j ∉ J) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (labelOutside (M := M) hμ c J hJ)
      (choiceFailureFamily (M := M) (I := I) hμ c) := by
  apply (mem_choiceFailureFamily hμ c _ p).mpr
  refine ⟨labelOutside_subset hμ c J hJ p,?_⟩
  obtain ⟨j,hj⟩ := hj
  intro q hqp
  exact ⟨q,le_rfl,label (M := M) hμ c j,label_mem_labelOutside hμ c J hJ hj q⟩

end
end PartitionConsistency.ProductForcing


/-! ## Failure -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The adjoined largest condition never prevents passing to a genuine
Cohen/diagram condition. -/
theorem exists_condition_below [Nonempty (Diagram M I)] (p : Poset M I κ) :
    ∃ q : Condition M I κ, (q : Poset M I κ) ≤ p := by
  induction p using WithTop.recTopCoe with
  | top => exact ⟨(⊤,Classical.choice inferInstance),le_top⟩
  | coe p => exact ⟨p,le_rfl⟩

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
theorem Diagram.exists_outside (r : Diagram M I) (hsize : Cardinal.mk M < Cardinal.mk I) :
    ∃ j : I, j ∉ r.range := by
  apply (Set.ne_univ_iff_exists_notMem _).mp
  intro h
  have hc : Cardinal.mk r.range = Cardinal.mk I := by rw [h,Cardinal.mk_univ]
  have hr : Cardinal.mk r.range = Cardinal.mk M := Diagram.cardinal_range r
  exact (ne_of_lt hsize) (hr.symm.trans hc)

/-- No HS graph can choose from all nonempty subsets of the label set.
The proof moves an actual selected label, preserving both the graph's support
and its particular argument, and then amalgamates compatible conditions. -/
theorem not_choiceOn [Infinite M] [Infinite I] [Uncountable κ]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u}) (hc : Function.Injective c)
    (f : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    ¬ (system (M := M) (I := I) (κ := κ) hμ).Forces
      ![f,choiceFailureFamily (M := M) (I := I) hμ c] p (SetLanguage.choiceOn 0 1) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨em⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨em⟩⟩
  intro hchoice
  obtain ⟨hfun,hs⟩ := (S.forces_choiceOn _ _ _ _).mp hchoice
  obtain ⟨J,hJ,hfix⟩ := name_support hμ f
  obtain ⟨p₀,hp₀⟩ := exists_condition_below p
  obtain ⟨r,hr,hcover⟩ := Diagram.extend_through hsize e he p₀.2 (hcard ▸ hJ)
  have hrp : r ≤ p₀.2 := ⟨e,hr⟩
  let q : Condition M I κ := (p₀.1,r)
  have hqp₀ : (q : Poset M I κ) ≤ p₀ := WithTop.coe_le_coe.mpr ⟨le_rfl,hrp⟩
  have hqp : (q : Poset M I κ) ≤ p := hqp₀.trans hp₀
  have hrsize : Cardinal.mk r.range ≤ μ := by rw [Diagram.cardinal_range,hcard]
  let B := labelOutside (M := M) hμ c r.range hrsize
  have hB : ∀ t, S.atomic.MemF t B (choiceFailureFamily (M := M) (I := I) hμ c) :=
    labelOutside_mem_family hμ c r.range hrsize (Diagram.exists_outside r hsize)
  obtain ⟨s,hsq,y,hy,hym⟩ := hs B q hqp (hB q) q le_rfl
  obtain ⟨s',hs's,j,hjr,hyj⟩ := (mem_labelOutside hμ c r.range hrsize y s).mp hym s le_rfl
  have hys' : S.App s' f B (label (M := M) hμ c j) :=
    (S.app_congr (S.atomic.eq_refl s' f) (S.atomic.eq_refl s' B) hyj).mp (S.app_mono hs's hy)
  obtain ⟨t₀,ht₀⟩ := exists_condition_below s'
  obtain ⟨t,ht,htcover⟩ := Diagram.extend_through hsize e he t₀.2
    (J := {j}) (by simpa using (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk M)))
  let d : Condition M I κ := (t₀.1,t)
  have hdt : (d : Poset M I κ) ≤ t₀ := WithTop.coe_le_coe.mpr ⟨le_rfl,⟨e,ht⟩⟩
  have hdq : (d : Poset M I κ) ≤ q := hdt.trans (ht₀.trans (hs's.trans hsq))
  have htr : t ≤ r := (WithTop.coe_le_coe.mp hdq).2
  have hjt : j ∈ t.range := htcover (Set.mem_singleton j)
  have hdapp : S.App (d : Poset M I κ) f B (label (M := M) hμ c j) :=
    S.app_mono (hdt.trans ht₀) hys'
  obtain ⟨π,hπ,hi,v,hvd,hvπd⟩ := compatible_placement hsize hmerger r t t htr htr t₀.1 t₀.1
    (CohenForcing.Condition.compatible_iff.mpr ⟨_,le_rfl,le_rfl⟩)
  have hπr : π ∈ SupportFilter.Fix r.range := (SupportFilter.mem_Fix _ _).mpr hπ
  have hπf : π • f = f := hfix π ((SupportFilter.mem_Fix _ _).mpr (fun j hj => hπ j (hcover hj)))
  have hπB : π • B = B := smul_labelOutside hμ c r.range hrsize π hπr
  have hπapp : S.App (permute π d : Poset M I κ) f B (label (M := M) hμ c (π j)) := by
    have hh := (S.app_symmetry π (d : Poset M I κ) f B (label (M := M) hμ c j)).mp hdapp
    simpa only [S,move_coe,hπf,hπB,smul_label] using hh
  have hvd' : (v : Poset M I κ) ≤ d := WithTop.coe_le_coe.mpr hvd
  have hvπd' : (v : Poset M I κ) ≤ permute π d := WithTop.coe_le_coe.mpr hvπd
  have hjπ : j ≠ π j := by
    intro hj
    apply hjr
    rw [← hi]
    refine ⟨hjt,?_⟩
    rw [Diagram.range_permute]
    exact ⟨j,hjt,hj.symm⟩
  apply label_not_equal hμ c hc hjπ (v : Poset M I κ)
  exact S.functionOn_unique ![f,choiceFailureFamily (M := M) (I := I) hμ c] v 0 1
    (S.atomic.forceFormula_mono (hvd'.trans (hdq.trans hqp)) hfun) B
    (label (M := M) hμ c j) (label (M := M) hμ c (π j)) (hB v)
    (S.app_mono hvd' hdapp) (S.app_mono hvπd' hπapp)

/-- The family in this counterexample consists of nonempty sets, at every
condition and with arbitrary HS names as potential elements. -/
theorem forces_members_nonempty (c : κ → ZFSet.{u}) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces
      ![choiceFailureFamily (M := M) (I := I) hμ c] p
      (.all ((Formula.mem 1 0).imp (SetLanguage.nonempty 1))) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  change S.atomic.ForceFormula _ p (.all _)
  rw [S.atomic.forceFormula_all S.atomic_regular]
  intro ν
  rw [S.atomic.forceFormula_imp S.atomic_regular]
  intro q hqp hm
  apply (S.forces_nonempty _ q 1).mpr
  exact ((mem_choiceFailureFamily hμ c ν q).mp hm).2

/-- The actual product symmetric system forces the negation of the encoded
first-order Axiom of Choice. No rank bound or countability restriction is
placed on the potential choosing graph. -/
theorem forces_not_AC [Infinite M] [Infinite I] [Uncountable κ]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u}) (hc : Function.Injective c) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces Fin.elim0 p SetLanguage.AC.neg := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  apply (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr
  intro q hqp hAC
  rw [SetLanguage.AC,S.atomic.forceFormula_all S.atomic_regular] at hAC
  have hh := hAC (choiceFailureFamily (M := M) (I := I) hμ c)
  rw [S.atomic.forceFormula_imp S.atomic_regular] at hh
  have hv : Fin.snoc Fin.elim0 (choiceFailureFamily (M := M) (I := I) hμ c) =
      ![choiceFailureFamily (M := M) (I := I) hμ c] := by ext i; fin_cases i; rfl
  rw [hv] at hh
  have hh' := hh q le_rfl (forces_members_nonempty hμ c q)
  obtain ⟨r,hrq,f,hf⟩ := hh' q le_rfl
  apply not_choiceOn hμ hcard hsize hmerger e he c hc f r
  apply (S.forces_choiceOn _ r 0 1).mpr
  exact (S.forces_choiceOn _ r 1 0).mp hf

end
end PartitionConsistency.ProductForcing


/-! ## LocalDecision -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The direct product-forcing version of decision over a supporting
root. Any assertion forced below the root is already forced at the root,
with only the witnessing Cohen condition's root restriction retained.
All parameters are arbitrary-rank HS names. -/
theorem forces_at_supporting_root [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n} (φ : Formula n) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p s : Diagram M I) (hsp : s ≤ p)
    (hsup : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d : CohenForcing.Condition I κ)
    (h : (system hμ).Forces v ((d,s) : Poset M I κ) φ) :
    (system hμ).Forces v (((d.restrict p.range),p) : Poset M I κ) φ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  apply S.atomic.forceFormula_of_dense S.atomic_regular
  intro q hqp
  obtain ⟨q₀,hq₀⟩ := exists_condition_below q
  have hq : q₀ ≤ (d.restrict p.range,p) := WithTop.coe_le_coe.mp (hq₀.trans hqp)
  have hroot : CohenForcing.Condition.Compatible (q₀.1.restrict p.range) (d.restrict p.range) :=
    CohenForcing.Condition.compatible_iff.mpr ⟨q₀.1,q₀.1.le_restrict _,hq.1⟩
  obtain ⟨π,hπ,_,t,htq,htπ⟩ := compatible_placement hsize hmerger p q₀.2 s hq.2 hsp q₀.1 d hroot
  have hv : (fun i => π • v i) = v := funext (hsup π ((SupportFilter.mem_Fix _ _).mpr hπ))
  have ht : S.Forces v ((permute π (d,s)) : Poset M I κ) φ := by
    have hh := (S.forces_symmetry π φ v ((d,s) : Poset M I κ)).mp h
    simpa only [hv,S,move_coe] using hh
  exact ⟨t,(WithTop.coe_le_coe.mpr htq).trans hq₀,
    S.atomic.forceFormula_mono (WithTop.coe_le_coe.mpr htπ) ht⟩

/-- In particular, irrelevant Cohen coordinates can be removed from a
condition whose diagram supports its entire parameter tuple. -/
theorem forces_iff_restrict [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n} (φ : Formula n) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Diagram M I)
    (hsup : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d : CohenForcing.Condition I κ) :
    (system hμ).Forces v ((d,p) : Poset M I κ) φ ↔
    (system hμ).Forces v (((d.restrict p.range),p) : Poset M I κ) φ :=
  ⟨forces_at_supporting_root hμ hsize hmerger φ v p p le_rfl hsup d,
    (system hμ).atomic.forceFormula_mono (WithTop.coe_le_coe.mpr ⟨d.le_restrict _,le_rfl⟩)⟩

/-- Opposite answers about a root-supported tuple cannot have compatible
Cohen restrictions to that root, regardless of their stronger diagrams. -/
theorem incompatible_root_of_opposite [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n} (φ : Formula n) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p s t : Diagram M I) (hsp : s ≤ p) (htp : t ≤ p)
    (hsup : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d c : CohenForcing.Condition I κ)
    (h : (system hμ).Forces v ((d,s) : Poset M I κ) φ)
    (hn : (system hμ).Forces v ((c,t) : Poset M I κ) φ.neg) :
    ¬ CohenForcing.Condition.Compatible (d.restrict p.range) (c.restrict p.range) := by
  intro hc
  obtain ⟨a,had,hac⟩ := CohenForcing.Condition.compatible_iff.mp hc
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hd := forces_at_supporting_root hμ hsize hmerger φ v p s hsp hsup d h
  have hc := forces_at_supporting_root hμ hsize hmerger φ.neg v p t htp hsup c hn
  have hneg := (S.atomic.forceFormula_neg S.atomic_regular v
    (((c.restrict p.range),p) : Poset M I κ) φ).mp hc
  exact hneg ((a,p) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hac,le_rfl⟩)
    (S.atomic.forceFormula_mono (p := (((d.restrict p.range),p) : Poset M I κ))
      (q := ((a,p) : Poset M I κ)) (WithTop.coe_le_coe.mpr ⟨had,le_rfl⟩) hd)

end
end PartitionConsistency.ProductForcing

end OAI
