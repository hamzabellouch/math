import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.ClassFibers
import OAI.SetTheory.PartitionConsistency.Forcing.ChoiceFailure

namespace OAI

/-! ## Antichain -/

namespace PartitionConsistency.ForcingQuotient
universe u
noncomputable section
variable {P : Type u} [Preorder P]

/-- Every set of forcing conditions has a maximal incompatible subfamily.
The conclusion is predensity in that set; no cardinal chain condition is used. -/
theorem maximal_antichain (D : Set P) :
    ∃ A : Set P, A ⊆ D ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r, r ≤ p → r ≤ q → p = q) ∧
      ∀ d ∈ D, ∃ a ∈ A, ∃ r, r ≤ d ∧ r ≤ a := by
  classical
  let C : Set (Set P) := {A | A ⊆ D ∧
    ∀ p ∈ A, ∀ q ∈ A, ∀ r, r ≤ p → r ≤ q → p = q}
  obtain ⟨A,hA,hmax⟩ := zorn_subset C (by
    intro c hc hchain
    refine ⟨⋃₀ c,⟨?_,?_⟩,fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro p ⟨B,hB,hpB⟩
      exact (hc hB).1 hpB
    · rintro p ⟨B,hB,hpB⟩ q ⟨C,hC,hqC⟩ r hrp hrq
      rcases hchain.total hB hC with hBC | hCB
      · exact (hc hC).2 p (hBC hpB) q hqC r hrp hrq
      · exact (hc hB).2 p hpB q (hCB hqC) r hrp hrq)
  refine ⟨A,hA.1,hA.2,?_⟩
  intro d hd
  by_contra hn
  have hdA : d ∉ A := by
    intro h
    exact hn ⟨d,h,d,le_rfl,le_rfl⟩
  have hi : insert d A ∈ C := by
    refine ⟨Set.insert_subset hd hA.1,?_⟩
    intro p hp q hq r hrp hrq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact False.elim (hn ⟨q,hq,r,hrp,hrq⟩)
    · exact False.elim (hn ⟨p,hp,r,hrq,hrp⟩)
    · exact hA.2 p hp q hq r hrp hrq
  exact hdA (hmax hi (Set.subset_insert _ _) (Set.mem_insert _ _))

end
end PartitionConsistency.ForcingQuotient


/-! ## Maximum -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ K : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The local maximum principle furnished by root probes. Unlike the ordinary
maximum principle, the conclusion has a specified literal supporting diagram,
chosen before the witness. The name is a mixture over a Cohen antichain. -/
theorem localized_maximum [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K)
    {n} (φ : Formula (n+1)) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q : Diagram M I) (hq : q.sub e = p)
    (hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ q.range)
    (hf : (system hμ).Forces v ((d₀,p) : Poset M I κ) φ.ex) :
    ∃ ν : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      (system hμ).Forces (Fin.snoc v ν) ((d₀,q) : Poset M I κ) φ := by
  classical
  let S := system (M := M) (I := I) (κ := κ) hμ
  have : Nonempty (Diagram M I) := ⟨p⟩
  let D : Set (CohenForcing.Condition I κ) := {a | a ≤ d₀ ∧ a.support ⊆ q.range ∧
    ∃ ν : S.Name, (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      S.Forces (Fin.snoc v ν) ((a,q) : Poset M I κ) φ}
  obtain ⟨A,hAD,hanti,hpred⟩ := ForcingQuotient.maximal_antichain D
  have hchoose : ∀ a : A, ∃ ν : S.Name,
      (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      S.Forces (Fin.snoc v ν) ((a.val,q) : Poset M I κ) φ :=
    fun a => (hAD a.property).2.2
  choose f hfix hforce using hchoose
  let act : A → Poset M I κ := fun a => ((a.val,q) : Condition M I κ)
  let H := SupportFilter.Fix q.range
  have hH : H ∈ S.filter := ⟨q.range,by rw [Diagram.cardinal_range,hcard],le_rfl⟩
  have hact : ∀ π ∈ H, ∀ a, S.move π (act a) = act a := by
    intro π hπ a
    have hfixπ := (SupportFilter.mem_Fix _ _).mp hπ
    change S.move π ((a.val,q) : Poset M I κ) = ((a.val,q) : Poset M I κ)
    rw [move_coe]
    apply congrArg WithTop.some
    apply Prod.ext
    · exact CohenForcing.Condition.permute_eq_of_fixes_support π a.val
        (fun j hj => hfixπ j ((hAD a.property).2.1 hj))
    · exact Diagram.permute_eq_of_fixes_range π q hfixπ
  have hcoh : ∀ i j r, r ≤ act i → r ≤ act j → S.atomic.EqF r (f i) (f j) := by
    intro i j r hri hrj
    obtain ⟨r₀,hr₀⟩ := exists_condition_below r
    have hij : i = j := Subtype.ext (hanti _ i.property _ j.property r₀.1
      (WithTop.coe_le_coe.mp (hr₀.trans hri)).1
      (WithTop.coe_le_coe.mp (hr₀.trans hrj)).1)
    subst j
    exact S.atomic.eq_refl _ _
  let ν := S.mix f act H hH (fun π hπ a => hfix a π hπ) hact
  refine ⟨ν,S.mix_fixed f act H hH _ hact,?_⟩
  apply S.atomic.forceFormula_of_dense S.atomic_regular
  intro t ht
  obtain ⟨t₀,ht₀⟩ := exists_condition_below t
  have htd : t₀.1 ≤ d₀ := (WithTop.coe_le_coe.mp (ht₀.trans ht)).1
  have htq : t₀.2 ≤ q := (WithTop.coe_le_coe.mp (ht₀.trans ht)).2
  let c := t₀.1.restrict q.range
  have hcd : c ≤ d₀ := by
    intro z hz
    exact ⟨htd hz,hd₀ ((CohenForcing.Condition.mem_support _ _).mpr ⟨z.1.2,z.2,hz⟩)⟩
  obtain ⟨d,hdc,hds,νd,hfixd,hforced⟩ := localized_existential hμ hcard hsize hmerger e he hprobes
    φ v p q hq hv d₀ hf c hcd (t₀.1.support_restrict_subset _)
  have hdD : d ∈ D := ⟨hdc.trans hcd,hds,νd,hfixd,hforced⟩
  obtain ⟨a,ha,b,hbd,hba⟩ := hpred d hdD
  let b' := b.restrict q.range
  have hbc : b' ≤ c := by
    intro z hz
    exact ⟨hbd (hdc hz),hz.2⟩
  have hba' : b' ≤ a := by
    intro z hz
    exact ⟨hba hz,(hAD ha).2.1 ((CohenForcing.Condition.mem_support _ _).mpr ⟨z.1.2,z.2,hz⟩)⟩
  have htcomp : CohenForcing.Condition.Compatible t₀.1 b' := by
    intro z x y hx hy
    exact b'.functional z x y (hbc ⟨hx,hy.2⟩) hy
  obtain ⟨s,hst,hsb⟩ := CohenForcing.Condition.compatible_iff.mp htcomp
  let a' : A := ⟨a,ha⟩
  have hsa : ((s,t₀.2) : Poset M I κ) ≤ act a' :=
    WithTop.coe_le_coe.mpr ⟨hsb.trans hba',htq⟩
  have heq := S.atomic.eq_mono hsa (S.eq_mix_at f act H hH (fun π hπ a => hfix a π hπ) hact hcoh a')
  refine ⟨((s,t₀.2) : Poset M I κ),
    (WithTop.coe_le_coe.mpr (show (s,t₀.2) ≤ t₀ from ⟨hst,le_rfl⟩)).trans ht₀,?_⟩
  exact (S.forces_snoc_congr φ v heq).mpr (S.atomic.forceFormula_mono hsa (hforce a'))

end
end PartitionConsistency.ProductForcing


/-! ## ChoiceFamily -/

namespace PartitionConsistency.SetLanguage

/-- Auxiliary formula for a value selected from the set `F(i)`.
Its variables are the family graph, the index, and the selected value. -/
def familyMember : Formula 3 :=
  .ex ((edge 0 1 3).conj (.mem 2 3))

end PartitionConsistency.SetLanguage

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_nonemptyFamily {n} (v : Fin n → S.Name) (p : P) (F d : Fin n) :
    S.Forces v p (SetLanguage.nonemptyFamily F d) ↔
      S.Forces ![v F,v d] p (SetLanguage.functionOn 0 1) ∧
      ∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v d) →
        ∀ r, r ≤ q → S.App r (v F) x y →
          ∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ z : S.Name, S.atomic.MemF t z y := by
  simp only [Forces,SetLanguage.nonemptyFamily,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_edge,S.forces_nonempty]
  have hv : v ∘ ![F,d] = ![v F,v d] := by
    ext i
    fin_cases i <;> rfl
  simp [hv,Fin.snoc]

theorem forces_choiceForFamily {n} (v : Fin n → S.Name) (p : P) (c d F : Fin n) :
    S.Forces v p (SetLanguage.choiceForFamily c d F) ↔
      S.Forces ![v c,v d] p (SetLanguage.functionOn 0 1) ∧
      ∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v d) →
        ∀ r, r ≤ q → S.App r (v F) x y →
          ∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ z : S.Name,
            S.App t (v c) x z ∧ S.atomic.MemF t z y := by
  simp only [Forces,SetLanguage.choiceForFamily,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    ForcingQuotient.AtomicData.forceFormula_ex,S.forces_edge]
  have hv : v ∘ ![c,d,F] = ![v c,v d,v F] := by
    ext i
    fin_cases i <;> rfl
  have hfun : S.atomic.ForceFormula ![v c,v d,v F] p (SetLanguage.functionOn 0 1) ↔
      S.atomic.ForceFormula ![v c,v d] p (SetLanguage.functionOn 0 1) := by
    simp only [SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular]
    have hc : ![v c,v d,v F] ∘ ![0,1] = ![v c,v d] ∘ ![0,1] := by
      ext i
      fin_cases i <;> rfl
    rw [hc]
  simpa [hv,Fin.snoc,Fin.castPred,Fin.castLT] using
    and_congr hfun (Iff.rfl :
      (∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v d) →
        ∀ r, r ≤ q → S.App r (v F) x y →
          ∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ z : S.Name,
            S.App t (v c) x z ∧ S.atomic.MemF t z y) ↔ _)

theorem forces_familyMember (F x z : S.Name) (p : P) :
    S.Forces ![F,x,z] p SetLanguage.familyMember ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name,
        S.App r F x y ∧ S.atomic.MemF r z y := by
  simp only [Forces,SetLanguage.familyMember,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_edge]
  rfl

/-- A member of the domain of a forced nonempty family has a possible
choice value. Both the family's set value and the member are internal names. -/
theorem nonemptyFamily_member {n} (v : Fin n → S.Name) (p : P) (F d : Fin n)
    (hf : S.Forces v p (SetLanguage.nonemptyFamily F d)) (x : S.Name)
    (hx : S.atomic.MemF p x (v d)) :
    S.Forces ![v F,x] p SetLanguage.familyMember.ex := by
  obtain ⟨hfun,hne⟩ := (S.forces_nonemptyFamily v p F d).mp hf
  intro q hqp
  obtain ⟨r,hrq,y,ha,_⟩ := S.functionOn_total ![v F,v d] p 0 1 hfun x le_rfl hx q hqp
  obtain ⟨s,hsr,z,hz⟩ := hne x y p le_rfl hx r (hrq.trans hqp) ha r le_rfl
  refine ⟨s,hsr.trans hrq,z,?_⟩
  have hvec : Fin.snoc ![v F,x] z = ![v F,x,z] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  exact (S.forces_familyMember _ _ _ _).mpr (fun t hts =>
    ⟨t,le_rfl,y,S.app_mono (hts.trans hsr) ha,S.atomic.mem_mono hts hz⟩)

/-- Once the family's value at an index is specified, a selected member
belongs to that value. This uses single-valuedness of the actual graph. -/
theorem familyMember_mem {n} (v : Fin n → S.Name) (p : P) (F d : Fin n)
    (hfun : S.Forces v p (SetLanguage.functionOn F d)) (x y z : S.Name)
    (hx : S.atomic.MemF p x (v d)) (ha : S.App p (v F) x y)
    (hz : S.Forces ![v F,x,z] p SetLanguage.familyMember) : S.atomic.MemF p z y := by
  apply S.atomic_regular.2
  intro q hqp
  obtain ⟨r,hrq,t,hat,hzt⟩ := (S.forces_familyMember _ _ _ _).mp hz q hqp
  have he := S.functionOn_unique v r F d (S.atomic.forceFormula_mono (hrq.trans hqp) hfun)
    x t y (S.atomic.mem_mono (hrq.trans hqp) hx) hat (S.app_mono (hrq.trans hqp) ha)
  exact ⟨r,hrq,(S.atomic.mem_congr (S.atomic.eq_refl r z) he).mp hzt⟩

/-- The ordinary first-order ACwo sentence follows from dense internal
choice graphs. This is only a logical unpacking, with the ordinal and all
family hypotheses unchanged. -/
theorem forces_ACwo_of_dense
    (h : ∀ (p : P) (η F : S.Name),
      S.Forces ![η] p (SetLanguage.ordinal 0) →
      S.Forces ![F,η] p (SetLanguage.nonemptyFamily 0 1) →
      ∃ q, q ≤ p ∧ ∃ c : S.Name,
        S.Forces ![c,η,F] q (SetLanguage.choiceForFamily 0 1 2)) (p : P) :
    S.Forces Fin.elim0 p SetLanguage.ACwo := by
  change S.atomic.ForceFormula Fin.elim0 p SetLanguage.ACwo
  rw [SetLanguage.ACwo,S.atomic.forceFormula_all S.atomic_regular]
  intro η
  have hη : Fin.snoc (Fin.elim0 : Fin 0 → S.Name) η = ![η] := by
    ext i
    fin_cases i
    rfl
  rw [hη]
  rw [S.atomic.forceFormula_imp S.atomic_regular]
  intro q hqp ho
  rw [S.atomic.forceFormula_all S.atomic_regular]
  intro F
  have hF : Fin.snoc ![η] F = ![η,F] := by
    ext i
    fin_cases i <;> rfl
  rw [hF]
  rw [S.atomic.forceFormula_imp S.atomic_regular]
  intro r hrq hf
  have hf' : S.Forces ![F,η] r (SetLanguage.nonemptyFamily 0 1) :=
    (S.forces_nonemptyFamily ![F,η] r 0 1).mpr
      ((S.forces_nonemptyFamily ![η,F] r 1 0).mp hf)
  intro s hsr
  obtain ⟨t,hts,c,hc⟩ := h s η F (S.atomic.forceFormula_mono (hsr.trans hrq) ho)
    (S.atomic.forceFormula_mono hsr hf')
  refine ⟨t,hts,c,?_⟩
  have hcvec : Fin.snoc ![η,F] c = ![η,F,c] := by
    ext i
    fin_cases i <;> rfl
  rw [hcvec]
  exact (S.forces_choiceForFamily ![η,F,c] t 2 0 1).mpr
    ((S.forces_choiceForFamily ![c,η,F] t 0 1 2).mp hc)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Uniformly supported local choices yield an actual internal set function,
not an external function substituted for the conclusion of ACwo. -/
theorem indexedGraph_choiceForFamily (X : ZFSet.{u}) (F : S.Name)
    (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (p : P)
    (hfun : S.Forces ![F,Name.check X] p (SetLanguage.functionOn 0 1))
    (hf : ∀ i : X, S.Forces ![F,Name.check i.val,f i] p SetLanguage.familyMember) :
    S.Forces ![S.indexedGraph X f H hH hfix,Name.check X,F] p
      (SetLanguage.choiceForFamily 0 1 2) := by
  apply (S.forces_choiceForFamily _ _ _ _ _).mpr
  refine ⟨S.indexedGraph_functionOn X f H hH hfix p,?_⟩
  intro x y q hqp hx r hrq ha s hsr
  obtain ⟨t,hts,i,hi,heq⟩ := (S.mem_check X x q).mp hx s (hsr.trans hrq)
  let j : X := ⟨i,hi⟩
  have hap : S.App t F (Name.check i) y :=
    (S.app_congr (S.atomic.eq_refl t F) heq (S.atomic.eq_refl t y)).mp
      (S.app_mono (hts.trans hsr) ha)
  have hm := S.familyMember_mem ![F,Name.check X] t 0 1
    (S.atomic.forceFormula_mono (hts.trans (hsr.trans (hrq.trans hqp))) hfun)
    (Name.check i) y (f j) (S.check_mem_of_mem hi t) hap
    (S.atomic.forceFormula_mono (hts.trans (hsr.trans (hrq.trans hqp))) (hf j))
  refine ⟨t,hts,f j,?_,hm⟩
  exact (S.app_congr (S.atomic.eq_refl t _) heq (S.atomic.eq_refl t _)).mpr
    (S.indexedGraph_app_at X f H hH hfix j t)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## ACwo -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ K : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- One previously chosen extension of the supporting diagram supports all
choices from a ground-indexed family, at arbitrary name ranks. The result is
an internal graph; the uniform maximum principle only constructs its name. -/
theorem ground_family_choice [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K) (X : ZFSet.{u})
    (F : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q : Diagram M I) (hq : q.sub e = p)
    (hF : ∀ π ∈ SupportFilter.Fix p.range, π • F = F)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ q.range)
    (hf : (system hμ).Forces ![F,Name.check X] ((d₀,p) : Poset M I κ)
      (SetLanguage.nonemptyFamily 0 1)) :
    ∃ c : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (system hμ).Forces ![c,Name.check X,F] ((d₀,q) : Poset M I κ)
        (SetLanguage.choiceForFamily 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hw (i : X) : ∃ ν : S.Name,
      (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      S.Forces ![F,Name.check i.val,ν] ((d₀,q) : Poset M I κ) SetLanguage.familyMember := by
    have hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ j : Fin 2,
        π • (![F,Name.check i.val] : Fin 2 → S.Name) j = ![F,Name.check i.val] j := by
      intro π hπ j
      fin_cases j
      · exact hF π hπ
      · exact Name.smul_check S π _
    have hm := S.nonemptyFamily_member ![F,Name.check X] ((d₀,p) : Poset M I κ) 0 1 hf
      (Name.check i.val) (S.check_mem_of_mem i.property _)
    obtain ⟨ν,hν,hforce⟩ := localized_maximum hμ hcard hsize hmerger e he hprobes
      SetLanguage.familyMember ![F,Name.check i.val] p q hq hv d₀ hd₀ hm
    refine ⟨ν,hν,?_⟩
    have hvec : Fin.snoc ![F,Name.check i.val] ν = ![F,Name.check i.val,ν] := by
      ext j
      fin_cases j <;> rfl
    rwa [hvec] at hforce
  choose f hfix hforce using hw
  let H := SupportFilter.Fix q.range
  have hH : H ∈ S.filter := ⟨q.range,by rw [Diagram.cardinal_range,hcard],le_rfl⟩
  have hf' := (S.forces_nonemptyFamily ![F,Name.check X] ((d₀,p) : Poset M I κ) 0 1).mp hf
  exact ⟨S.indexedGraph X f H hH (fun π hπ i => hfix i π hπ),
    S.indexedGraph_choiceForFamily X F f H hH (fun π hπ i => hfix i π hπ) _
      (S.atomic.forceFormula_mono (p := ((d₀,p) : Poset M I κ)) (q := ((d₀,q) : Poset M I κ))
        (WithTop.coe_le_coe.mpr ⟨le_rfl,⟨e,hq⟩⟩) hf'.1) hforce⟩

/-- An arbitrary starting condition for a ground-indexed nonempty family
can be strengthened to force a choice graph. The family's support and the
Cohen condition are both put in the root before using probes. -/
theorem ground_family_choice_dense [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K) (X : ZFSet.{u})
    (F : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hf : (system hμ).Forces ![F,Name.check X] t (SetLanguage.nonemptyFamily 0 1)) :
    ∃ s, s ≤ t ∧ ∃ c : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (system hμ).Forces ![c,Name.check X,F] s (SetLanguage.choiceForFamily 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨emb⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨emb⟩⟩
  obtain ⟨d,hdt⟩ := exists_condition_below t
  obtain ⟨J,hJ,hfix⟩ := name_support hμ F
  have hU : Cardinal.mk ↥(J ∪ d.1.support) ≤ Cardinal.mk M := by
    rw [hcard]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (d.1.cardinal_support.trans hμ)).trans_eq (Cardinal.add_eq_self hμ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through hsize e he d.2 hU
  have hpd : ((d.1,p) : Poset M I κ) ≤ t :=
    (WithTop.coe_le_coe.mpr (show (d.1,p) ≤ d from ⟨le_rfl,⟨e,hp⟩⟩)).trans hdt
  obtain ⟨q,hq,_⟩ := Diagram.extend_through hsize e he p (J := ∅) (by simp)
  have hqp : q ≤ p := ⟨e,hq⟩
  obtain ⟨c,hc⟩ := ground_family_choice hμ hcard hsize hmerger e he hprobes X F p q hq
    (fun π hπ => hfix π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (hcover (Or.inl hj)))))
    d.1 (fun j hj => Diagram.range_antitone hqp (hcover (Or.inr hj)))
    (S.atomic.forceFormula_mono hpd hf)
  exact ⟨(d.1,q),(WithTop.coe_le_coe.mpr (show (d.1,q) ≤ (d.1,p) from ⟨le_rfl,hqp⟩)).trans hpd,c,hc⟩

/-- Choice for every internal ordinal-indexed family, without a rank cutoff.
Ordinal preservation first decides the index set to a ground ordinal, after
which one uniformly supported internal choice graph is constructed. -/
theorem forces_ACwo [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces Fin.elim0 p SetLanguage.ACwo := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  apply S.forces_ACwo_of_dense
  intro s η F ho hf'
  obtain ⟨t,hts,β,hη⟩ := S.forces_ordinal_decide ![η] s 0 ho s le_rfl
  have hf' := S.atomic.forceFormula_mono hts hf'
  have hchange : S.Forces ![F,Name.check β.toZFSet] t (SetLanguage.nonemptyFamily 0 1) := by
    apply (S.atomic.forceFormula_tuple_congr (p := t) (φ := SetLanguage.nonemptyFamily 0 1)
      (v := ![F,η]) (w := ![F,Name.check β.toZFSet]) ?_).mp hf'
    intro i
    fin_cases i
    · exact S.atomic.eq_refl t F
    · exact hη
  obtain ⟨a,hat,c,hc⟩ := ground_family_choice_dense hμ hcard hsize hmerger e he hprobes
    β.toZFSet F t hchange
  have hc' : S.Forces ![c,η,F] a (SetLanguage.choiceForFamily 0 1 2) := by
    apply (S.atomic.forceFormula_tuple_congr (p := a) (φ := SetLanguage.choiceForFamily 0 1 2)
      (v := ![c,Name.check β.toZFSet,F]) (w := ![c,η,F]) ?_).mp hc
    intro i
    fin_cases i
    · exact S.atomic.eq_refl a c
    · exact S.atomic.eq_symm (S.atomic.eq_mono hat hη)
    · exact S.atomic.eq_refl a F
  exact ⟨a,hat.trans hts,c,hc'⟩

end
end PartitionConsistency.ProductForcing

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
noncomputable section

instance : Uncountable K := Cardinal.aleph0_lt_mk_iff.mp
  (by rw [cardinal_K]; exact Cardinal.aleph0_lt_aleph_one.trans_le aleph_one_le_μ)

/-- The probes used by ordinal choice are actually present in the saturated
monoid. This is an instance of the executed requests with `a=1`. -/
theorem rootProbes : ProductForcing.RootProbes T.e K := by
  intro b hb
  let d : ProbeData T :=
    ⟨1,b,hb,⟨fun _ => 1,rfl,fun _ => dvd_refl _,fun _ => dvd_refl _⟩⟩
  obtain ⟨m,_,hm,hi⟩ := Saturation.probes Base.object K d
  refine ⟨m,fun i => (hm i).exit.trans (one_mul _),?_⟩
  intro i j hij z
  have hh := hi i j hij z
  change m i ∣ z ∧ m j ∣ z ↔ (1 : T) * T.e ∣ z at hh
  simpa only [one_mul] using! hh

/-- No additional cardinal or support principle is assumed here. -/
theorem forces_ACwo (p : P) : S.Forces Fin.elim0 p SetLanguage.ACwo :=
  ProductForcing.forces_ACwo aleph0_le_μ cardinal_T size_lt finiteMergers T.e
    complement_cardinal rootProbes p

/-- Consistency of the ZF + ACwo + ¬AC subtheory. The full target with
PP is proved below in `consistent_target`. -/
theorem consistent_ZF_ACwo_not_AC :
    Consistent (SetLanguage.ZF ∪ {SetLanguage.ACwo,SetLanguage.AC.neg}) := by
  apply S.consistent_of_forces (⊤ : P)
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact forces_ZF ⊤ φ hφ
  · rcases hφ with rfl | rfl | hfalse
    · exact forces_ACwo ⊤
    · exact forces_not_AC ⊤

end
end PartitionConsistency.ConcreteSystem

end OAI
