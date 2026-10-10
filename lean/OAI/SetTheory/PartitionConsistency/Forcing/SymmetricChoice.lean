import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricSets

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

abbrev RelF {n} (v : Fin n → S.Name) (φ : Formula (n+2)) (p : P)
    (x y : S.Name) : Prop := S.Forces (Fin.snoc (Fin.snoc v x) y) p φ

theorem forces_relation {n m} (φ : Formula (n+2)) (r : Fin n → Fin m)
    (x y : Fin m) (v : Fin m → S.Name) (p : P) :
    S.Forces v p (SetLanguage.relation φ r x y) ↔ S.RelF (v ∘ r) φ p (v x) (v y) := by
  rw [SetLanguage.relation, Forces, S.atomic.forceFormula_rename S.atomic_regular]
  have h : v ∘ Fin.lastCases y (Fin.lastCases x r) =
      Fin.snoc (Fin.snoc (v ∘ r) (v x)) (v y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Function.comp_def]
  rw [h]

theorem rel_left_congr {n} (v : Fin n → S.Name) (φ : Formula (n+2))
    {p : P} {x x' : S.Name} (y : S.Name) (heq : S.atomic.EqF p x x') :
    S.RelF v φ p x y ↔ S.RelF v φ p x' y := by
  apply S.atomic.forceFormula_tuple_congr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using S.atomic.eq_refl p y
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using heq
    · simpa using S.atomic.eq_refl p (v k)

/-- A small index set of precisely the domain-entry/condition pairs for which
there is a local symmetric witness. -/
def WitnessIndex {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) :=
  {i : Edges σ.raw × P // ∃ η : S.Name, S.RelF v φ i.2 (σ.child i.1.property) η}

instance {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) :
    Small.{u} (S.WitnessIndex σ v φ) := by
  let := S.small_conditions
  unfold WitnessIndex
  infer_instance

noncomputable def chosenWitness {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : S.WitnessIndex σ v φ) : S.Name := Classical.choose i.property

theorem chosenWitness_spec {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : S.WitnessIndex σ v φ) :
    S.RelF v φ i.val.2 (σ.child i.val.1.property) (S.chosenWitness σ v φ i) :=
  Classical.choose_spec i.property

section SmallGroup
variable [Small.{u} Γ]

/-- An orbit-closed bound for one Replacement problem. Instead of a uniform
name-rank cutoff, take the whole set-group orbit of the ground-chosen local
witnesses. This set is invariant and is still small. No symmetric maximum
principle, global rank cutoff, or on-condition selection is used. -/
noncomputable def replacementBound {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) : S.Name :=
  S.collect (fun z : Γ × S.WitnessIndex σ v φ => z.1 • S.chosenWitness σ v φ z.2)
    (fun _ _ => True) ⊤ S.normal.1 (by
      intro h _ z p _
      exact ⟨(h*z.1,z.2),mul_smul h z.1 _,True.intro⟩)

theorem witness_in_bound {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : S.WitnessIndex σ v φ) (p : P) :
    S.atomic.MemF p (S.chosenWitness σ v φ i) (S.replacementBound σ v φ) := by
  apply S.mem_of_edge (c := p) ?_ le_rfl
  change ZFSet.pair (S.chosenWitness σ v φ i).raw (S.code p) ∈ S.collectRaw
    (fun z : Γ × S.WitnessIndex σ v φ => z.1 • S.chosenWitness σ v φ z.2) (fun _ _ => True)
  apply (S.edge_collectRaw _ _ _ _).mpr
  exact ⟨(1,i),p,True.intro,by simp,rfl⟩

theorem bounded_local_witness {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : Edges σ.raw) (p : P) (hi : ∃ η, S.RelF v φ p (σ.child i.property) η) :
    ∃ η : S.Name, S.RelF v φ p (σ.child i.property) η ∧
      S.atomic.MemF p η (S.replacementBound σ v φ) := by
  let j : S.WitnessIndex σ v φ := ⟨(i,p),hi⟩
  exact ⟨S.chosenWitness σ v φ j,S.chosenWitness_spec σ v φ j,S.witness_in_bound σ v φ j p⟩

/-- The dense local meaning of `∃x∈σ, φ(x,y)`. -/
def ImageF {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (p : P) (ν : S.Name) : Prop :=
  ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, S.atomic.MemF r x σ ∧ S.RelF v φ r x ν

/-- Ordinary internal single-valuedness, expressed via forcing at every
stronger condition. -/
def SingleValuedF {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) (p : P) : Prop :=
  ∀ x y z : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x σ →
    S.RelF v φ q x y → S.RelF v φ q x z → S.atomic.EqF q y z

theorem image_in_bound {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    {p : P} (hfunc : S.SingleValuedF σ v φ p) (ν : S.Name) (himage : S.ImageF σ v φ p ν) :
    S.atomic.MemF p ν (S.replacementBound σ v φ) := by
  apply S.atomic_regular.2
  intro q hqp
  obtain ⟨r,hrq,x,hx,hφ⟩ := himage q hqp
  obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := (S.mem_iff.mp hx) r le_rfl
  let i : Edges σ.raw := ⟨(τ.raw,S.code c),he⟩
  have hi : σ.child i.property = τ := Name.ext rfl
  have hφ' : S.RelF v φ s τ ν := (S.rel_left_congr v φ ν heq).mp
    (S.atomic.forceFormula_mono hsr hφ)
  obtain ⟨η,hηφ,hηB⟩ := S.bounded_local_witness σ v φ i s ⟨ν,by simpa only [hi] using hφ'⟩
  rw [hi] at hηφ
  have hνη := hfunc τ ν η s (hsr.trans (hrq.trans hqp)) (S.mem_of_edge he hsc) hφ' hηφ
  exact ⟨s,hsr.trans hrq,(S.atomic.mem_congr hνη
    (S.atomic.eq_refl s (S.replacementBound σ v φ))).mpr hηB⟩

/-- The image predicate, with the set-domain as one extra parameter, retaining
all quantifiers of the original formula. -/
def imageFormula {n} (φ : Formula (n+2)) : Formula (n+2) :=
  Formula.ex ((Formula.mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).conj
    (SetLanguage.relation φ (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last (n+2)) (Fin.last (n+1)).castSucc))

omit [Small.{u} Γ] in
theorem forces_imageFormula {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) (ν : S.Name) (p : P) :
    S.Forces (Fin.snoc (Fin.snoc v σ) ν) p (imageFormula φ) ↔ S.ImageF σ v φ p ν := by
  simp only [Forces, imageFormula, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_conj, ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_relation, Fin.snoc_last, Fin.snoc_castSucc]
  have h (x : S.Name) : Fin.snoc (Fin.snoc (Fin.snoc v σ) ν) x ∘
      (fun i => i.castSucc.castSucc.castSucc) = v := by funext i; simp
  simp only [h]
  rfl

noncomputable def replacementImage {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) : S.Name :=
  S.separate (S.replacementBound σ v φ) (Fin.snoc v σ) (imageFormula φ)

theorem mem_replacementImage {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) {p : P} (hfunc : S.SingleValuedF σ v φ p) (ν : S.Name) :
    S.atomic.MemF p ν (S.replacementImage σ v φ) ↔ S.ImageF σ v φ p ν := by
  rw [replacementImage, S.mem_separate, S.forces_imageFormula]
  exact ⟨And.right,fun h => ⟨S.image_in_bound σ v φ hfunc ν h,h⟩⟩

/-- The antecedent of a Replacement instance: totality with local unique
witnesses, exactly as supplied by the existential forcing clause. -/
def TotalFunctionalF {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) (p : P) : Prop :=
  ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x σ → ∀ r, r ≤ q →
    ∃ s, s ≤ r ∧ ∃ y : S.Name, S.RelF v φ s x y ∧
      ∀ z : S.Name, ∀ t, t ≤ s → S.RelF v φ t x z → S.atomic.EqF t z y

omit [Small.{u} Γ] in
theorem singleValued_of_totalFunctional {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) {p : P} (h : S.TotalFunctionalF σ v φ p) :
    S.SingleValuedF σ v φ p := by
  intro x y z q hqp hx hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,η,_,hη⟩ := h x q hqp hx r hrq
  exact ⟨s,hsr,S.atomic.eq_trans (hη y s le_rfl (S.atomic.forceFormula_mono (hsr.trans hrq) hy))
    (S.atomic.eq_symm (hη z s le_rfl (S.atomic.forceFormula_mono (hsr.trans hrq) hz)))⟩

/-- Every full Replacement instance is forced. The bound depends on the
particular domain, formula, and parameter tuple, and not on a prechosen class
of name ranks. -/
theorem forces_replacement {n} (φ : Formula (n+2)) (p : P) :
    S.Forces Fin.elim0 p (SetLanguage.replacement φ) := by
  unfold SetLanguage.replacement
  rw [Forces, S.atomic.forceFormula_close S.atomic_regular]
  simp only [S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_ex, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_relation, Fin.snoc_last, Fin.snoc_castSucc]
  have h3 (v : Fin n → S.Name) (a b c : S.Name) :
      Fin.snoc (Fin.snoc (Fin.snoc v a) b) c ∘ (fun i => i.castSucc.castSucc.castSucc) = v := by
    funext i
    simp
  have h4 (v : Fin n → S.Name) (a b c d : S.Name) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc v a) b) c) d ∘
        (fun i => i.castSucc.castSucc.castSucc.castSucc) = v := by
    funext i
    simp
  simp only [h3,h4]
  intro v σ q hqp h r hrq
  change S.TotalFunctionalF σ v φ q at h
  have hfunc := S.singleValued_of_totalFunctional σ v φ h
  have hf {t : P} (htq : t ≤ q) : S.SingleValuedF σ v φ t :=
    fun x y z a hat => hfunc x y z a (hat.trans htq)
  refine ⟨r,le_rfl,S.replacementImage σ v φ,?_⟩
  intro ν
  exact ⟨fun t htr => (S.mem_replacementImage σ v φ (hf (htr.trans hrq)) ν).mp,
    fun t htr => (S.mem_replacementImage σ v φ (hf (htr.trans hrq)) ν).mpr⟩

end SmallGroup
end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable [Small.{u} Γ] (S : SymmetricSystem.{u} P Γ)

/-- Full ZF in the concrete hereditary-symmetry interpretation. The quantifier
domain is the unbounded class of all HS names. Each schema instance is proved
by its own actual set-name, including unrestricted Separation and Replacement. -/
theorem forces_ZF (p : P) : ∀ φ ∈ SetLanguage.ZF, S.Forces Fin.elim0 p φ := by
  intro φ hφ
  cases hφ with
  | extensionality => exact S.forces_extensionality p
  | emptySet => exact S.forces_emptySet p
  | pairing => exact S.forces_pairing p
  | union => exact S.forces_union p
  | powerSet => exact S.forces_powerSet p
  | infinity => exact S.forces_infinity p
  | foundation => exact S.forces_foundation p
  | separation φ => exact S.forces_separation φ p
  | replacement φ => exact S.forces_replacement φ p

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
