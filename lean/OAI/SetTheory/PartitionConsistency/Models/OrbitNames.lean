import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.DiagramPlacements
import OAI.SetTheory.PartitionConsistency.Forcing.ProductNames

namespace OAI

/-! ## OrderedPair -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

@[simp] theorem Name.smul_pair (g : Γ) (σ τ : S.Name) :
    g • σ.pair τ = (g • σ).pair (g • τ) := by
  apply Subtype.ext
  exact ConditionAction.Name.smul_pair (S.code_mem ⊤) g (S.code_top_fixed g) σ.val τ.val

/-- The equivariant name for the actual Kuratowski pair. -/
def Name.opair {S : SymmetricSystem.{u} P Γ} (σ τ : S.Name) : S.Name := (σ.pair σ).pair (σ.pair τ)

@[simp] theorem Name.smul_opair (g : Γ) (σ τ : S.Name) :
    g • σ.opair τ = (g • σ).opair (g • τ) := by simp [Name.opair]

theorem mem_pair_left (p : P) (σ τ : S.Name) : S.atomic.MemF p σ (σ.pair τ) :=
  (S.mem_pair σ τ σ p).mpr (fun q _ => ⟨q,le_rfl,Or.inl (S.atomic.eq_refl q σ)⟩)

theorem mem_pair_right (p : P) (σ τ : S.Name) : S.atomic.MemF p τ (σ.pair τ) :=
  (S.mem_pair σ τ τ p).mpr (fun q _ => ⟨q,le_rfl,Or.inr (S.atomic.eq_refl q τ)⟩)

theorem eq_pair_congr {p : P} {σ σ' τ τ' : S.Name}
    (hσ : S.atomic.EqF p σ σ') (hτ : S.atomic.EqF p τ τ') :
    S.atomic.EqF p (σ.pair τ) (σ'.pair τ') := by
  apply S.eq_of_same_members
  intro ν q hqp
  rw [S.mem_pair,S.mem_pair]
  constructor
  · intro h r hrq
    obtain ⟨s,hsr,h | h⟩ := h r hrq
    · exact ⟨s,hsr,Or.inl (S.atomic.eq_trans h (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hσ))⟩
    · exact ⟨s,hsr,Or.inr (S.atomic.eq_trans h (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hτ))⟩
  · intro h r hrq
    obtain ⟨s,hsr,h | h⟩ := h r hrq
    · exact ⟨s,hsr,Or.inl (S.atomic.eq_trans h
        (S.atomic.eq_symm (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hσ)))⟩
    · exact ⟨s,hsr,Or.inr (S.atomic.eq_trans h
        (S.atomic.eq_symm (S.atomic.eq_mono (hsr.trans (hrq.trans hqp)) hτ)))⟩

theorem mem_singleton (p : P) (σ τ : S.Name) :
    S.atomic.MemF p σ (τ.pair τ) ↔ S.atomic.EqF p σ τ := by
  rw [S.mem_pair]
  constructor
  · intro h
    apply S.atomic_regular.1
    intro q hqp
    obtain ⟨r,hrq,h | h⟩ := h q hqp <;> exact ⟨r,hrq,h⟩
  · intro h q hqp
    exact ⟨q,le_rfl,Or.inl (S.atomic.eq_mono hqp h)⟩

theorem eq_pair_singleton {p : P} {σ τ ν : S.Name}
    (he : S.atomic.EqF p (σ.pair τ) (ν.pair ν)) :
    S.atomic.EqF p σ ν ∧ S.atomic.EqF p τ ν := by
  constructor
  · exact (S.mem_singleton p σ ν).mp
      ((S.atomic.mem_congr (S.atomic.eq_refl p σ) he).mp (S.mem_pair_left p σ τ))
  · exact (S.mem_singleton p τ ν).mp
      ((S.atomic.mem_congr (S.atomic.eq_refl p τ) he).mp (S.mem_pair_right p σ τ))

/-- Cancellation for unordered pairs with a common first entry. -/
theorem eq_pair_cancel_left {p : P} {σ τ ν : S.Name}
    (he : S.atomic.EqF p (σ.pair τ) (σ.pair ν)) : S.atomic.EqF p τ ν := by
  apply S.atomic_regular.1
  intro q hqp
  have hm := (S.atomic.mem_congr (S.atomic.eq_refl p τ) he).mp (S.mem_pair_right p σ τ)
  obtain ⟨r,hrq,h | h⟩ := (S.mem_pair σ ν τ p).mp hm q hqp
  · have hs := S.eq_pair_congr (S.atomic.eq_refl r σ) h
    have h' := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hqp) he)) hs
    exact ⟨r,hrq,S.atomic.eq_trans h (S.atomic.eq_symm (S.eq_pair_singleton h').2)⟩
  · exact ⟨r,hrq,h⟩

theorem eq_opair_congr {p : P} {σ σ' τ τ' : S.Name}
    (hσ : S.atomic.EqF p σ σ') (hτ : S.atomic.EqF p τ τ') :
    S.atomic.EqF p (σ.opair τ) (σ'.opair τ') :=
  S.eq_pair_congr (S.eq_pair_congr hσ hσ) (S.eq_pair_congr hσ hτ)

/-- Injectivity of ordered-pair names is a forcing theorem, not an assumption
on the name quotient. -/
theorem eq_opair_iff {p : P} {σ σ' τ τ' : S.Name} :
    S.atomic.EqF p (σ.opair τ) (σ'.opair τ') ↔
      S.atomic.EqF p σ σ' ∧ S.atomic.EqF p τ τ' := by
  constructor
  · intro he
    have hσ : S.atomic.EqF p σ σ' := by
      apply S.atomic_regular.1
      intro q hqp
      have hm := (S.atomic.mem_congr (S.atomic.eq_refl p (σ.pair σ)) he).mp
        (S.mem_pair_left p (σ.pair σ) (σ.pair τ))
      obtain ⟨r,hrq,h | h⟩ := (S.mem_pair (σ'.pair σ') (σ'.pair τ') (σ.pair σ) p).mp hm q hqp
      · exact ⟨r,hrq,(S.eq_pair_singleton h).1⟩
      · exact ⟨r,hrq,S.atomic.eq_symm (S.eq_pair_singleton (S.atomic.eq_symm h)).1⟩
    refine ⟨hσ,?_⟩
    have h := S.atomic.eq_trans (S.atomic.eq_symm (S.eq_opair_congr hσ (S.atomic.eq_refl p τ))) he
    have h' := S.eq_pair_cancel_left h
    exact S.eq_pair_cancel_left h'
  · rintro ⟨hσ,hτ⟩
    exact S.eq_opair_congr hσ hτ

/-- The pure first-order unordered-pair formula agrees with the canonical name. -/
theorem forces_unorderedPair {n} (v : Fin n → S.Name) (p : P) (a x y : Fin n) :
    S.Forces v p (SetLanguage.unorderedPair a x y) ↔
      S.atomic.EqF p (v a) ((v x).pair (v y)) := by
  simp only [Forces,SetLanguage.unorderedPair,Formula.iff,
    S.atomic.forceFormula_rename S.atomic_regular,S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_disj,
    ForcingQuotient.AtomicData.forceFormula_equal]
  constructor
  · intro h
    apply S.eq_of_same_members
    intro ν q hqp
    rw [S.mem_pair]
    exact ⟨(h ν).1 q hqp,(h ν).2 q hqp⟩
  · intro he ν
    constructor
    · intro q hqp hm
      exact (S.mem_pair _ _ ν q).mp
        ((S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp he)).mp hm)
    · intro q hqp hm
      exact (S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp he)).mpr
        ((S.mem_pair _ _ ν q).mpr hm)

/-- The pure first-order Kuratowski-pair formula agrees with the canonical name. -/
theorem forces_orderedPair {n} (v : Fin n → S.Name) (p : P) (a x y : Fin n) :
    S.Forces v p (SetLanguage.orderedPair a x y) ↔
      S.atomic.EqF p (v a) ((v x).opair (v y)) := by
  simp only [Forces,SetLanguage.orderedPair,S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    S.forces_unorderedPair]
  constructor
  · intro h
    apply S.atomic_regular.1
    intro q hqp
    obtain ⟨r,hrq,A,h⟩ := h q hqp
    obtain ⟨s,hsr,B,hA,hB,hp⟩ := h r le_rfl
    exact ⟨s,hsr.trans hrq,S.atomic.eq_trans hp (S.eq_pair_congr hA hB)⟩
  · intro h q hqp
    refine ⟨q,le_rfl,(v x).pair (v x),?_⟩
    intro r hrq
    exact ⟨r,le_rfl,(v x).pair (v y),S.atomic.eq_refl _ _, S.atomic.eq_refl _ _,
      S.atomic.eq_mono (hrq.trans hqp) h⟩

/-- Internal application is literal membership of the Kuratowski-pair name. -/
theorem app_iff_mem_opair (p : P) (f x y : S.Name) :
    S.App p f x y ↔ S.atomic.MemF p (x.opair y) f := by
  simp only [App,Forces,SetLanguage.edge,S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_orderedPair]
  constructor
  · intro h
    apply S.atomic_regular.2
    intro q hqp
    obtain ⟨r,hrq,z,hm,he⟩ := h q hqp
    exact ⟨r,hrq,(S.atomic.mem_congr he (S.atomic.eq_refl r f)).mp hm⟩
  · intro h q hqp
    exact ⟨q,le_rfl,x.opair y,S.atomic.mem_mono hqp h,S.atomic.eq_refl _ _⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Orbit -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The forcing membership value of an arbitrary collected family. The
index type, not the ranks of its entries, is required to be small. -/
theorem mem_collect {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.collect f R H hH permutes) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i a, R i a ∧ r ≤ a ∧ S.atomic.EqF r ν (f i) := by
  constructor
  · intro hm q hqp
    obtain ⟨r,hrq,τ,a,he,hra,heq⟩ := S.mem_iff.mp hm q hqp
    obtain ⟨i,b,hR,hτ,hba⟩ := (S.edge_collectRaw f R τ.raw (S.code a)).mp he
    obtain rfl := S.code_injective hba
    exact ⟨r,hrq,i,b,hR,hra,(Name.ext hτ : f i = τ) ▸ heq⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,i,a,hR,hra,heq⟩ := h q hqp
    exact ⟨r,hrq,f i,a,(S.edge_collectRaw f R _ _).mpr ⟨i,a,hR,rfl,rfl⟩,hra,heq⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
variable {M I : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- Compatible diagrams with the same center agree pointwise. This is the
functional feature of diagram forcing used by the name-orbit presentation. -/
theorem eq_of_compatible_centers {r p q : Diagram M I}
    (hrp : r ≤ p) (hrq : r ≤ q) (hcenter : p 1 = q 1) : p = q := by
  obtain ⟨a,rfl⟩ := hrp
  obtain ⟨b,rfl⟩ := hrq
  have hab : a = b := r.injective (by simpa only [sub_apply,mul_one] using hcenter)
  rw [hab]

end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.CohenForcing.Condition
universe u
variable {I κ : Type u}

@[simp] theorem permute_top (π : Equiv.Perm I) :
    (⊤ : Condition I κ).permute π = ⊤ := by
  apply ext
  simp only [permute, graph_top, Set.image_empty]

end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Ordinary names in an orbit agree literally when their supporting diagrams
do. This does not define an action on an evaluated symmetric model. -/
theorem smul_name_eq_of_diagram_eq
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ)
    (π ρ : Equiv.Perm I) (hp : p.permute π = p.permute ρ) : π • σ = ρ • σ := by
  have hg : ρ⁻¹ * π ∈ SupportFilter.Fix p.range := by
    apply (SupportFilter.mem_Fix _ _).mpr
    rintro j ⟨x,rfl⟩
    have hh := congrArg (fun d : Diagram M I => d x) hp
    change π (p x) = ρ (p x) at hh
    change ρ.symm (π (p x)) = p x
    rw [hh,Equiv.symm_apply_apply]
  have hh := congrArg (fun ν => ρ • ν) (hσ _ hg)
  simpa only [mul_smul,smul_inv_smul] using hh

/-- The invariant graph of the partial name-orbit map in
`eq:partial-orbit-map`. Each entry is activated by its actual moved diagram. -/
def orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).collect
    (fun π : Equiv.Perm I => (label (M := M) hμ c (π (p 1))).opair (π • σ))
    (fun π t => t = (((⊤ : CohenForcing.Condition I κ),p.permute π) : Poset M I κ))
    ⊤ (system (M := M) (I := I) (κ := κ) hμ).normal.1 (by
      intro ρ _ π t ht
      refine ⟨ρ * π,?_,?_⟩
      · simp only [Name.smul_opair,smul_label,mul_smul]; rfl
      · rw [ht,move_coe]
        change ((CohenForcing.Condition.permute ρ (⊤ : CohenForcing.Condition I κ),(p.permute π).permute ρ) : Poset M I κ) = _
        simp only [CohenForcing.Condition.permute_top,Diagram.permute_mul])

@[simp] theorem smul_orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (ρ : Equiv.Perm I) : ρ • orbitGraph hμ c σ p = orbitGraph hμ c σ p := by
  apply Subtype.ext
  apply (system (M := M) (I := I) (κ := κ) hμ).collectName_fixed _ _ ⊤ _ ρ (Subgroup.mem_top _)
  intro γ _ π t ht
  refine ⟨γ * π,?_,?_⟩
  · simp only [Name.smul_opair,smul_label,mul_smul]; rfl
  · rw [ht,move_coe]
    change ((CohenForcing.Condition.permute γ (⊤ : CohenForcing.Condition I κ),
      (p.permute π).permute γ) : Poset M I κ) = _
    simp only [CohenForcing.Condition.permute_top,Diagram.permute_mul]

/-- Complete local-witness description of the partial graph, including the
moved diagram that authorizes a contributed pair. -/
theorem mem_orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF t ν (orbitGraph hμ c σ p) ↔
      ∀ q, q ≤ t → ∃ r, r ≤ q ∧ ∃ π : Equiv.Perm I,
        r ≤ (((⊤ : CohenForcing.Condition I κ),p.permute π) : Poset M I κ) ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν ((label (M := M) hμ c (π (p 1))).opair (π • σ)) := by
  rw [orbitGraph,(system (M := M) (I := I) (κ := κ) hμ).mem_collect]
  simp only [exists_eq_left]

/-- Application is computed by actual contributed input-output pairs. -/
theorem app_orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (x y : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x y ↔
      ∀ q, q ≤ t → ∃ r, r ≤ q ∧ ∃ π : Equiv.Perm I,
        r ≤ (((⊤ : CohenForcing.Condition I κ),p.permute π) : Poset M I κ) ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r x (label (M := M) hμ c (π (p 1))) ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r y (π • σ) := by
  rw [(system (M := M) (I := I) (κ := κ) hμ).app_iff_mem_opair,mem_orbitGraph]
  simp only [(system (M := M) (I := I) (κ := κ) hμ).eq_opair_iff]

/-- The identity copy maps the label at the supporting diagram's center to
the original arbitrary-rank name. -/
theorem orbitGraph_app_self (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I) :
    (system (M := M) (I := I) (κ := κ) hμ).App (((⊤ : CohenForcing.Condition I κ),p) : Poset M I κ) (orbitGraph hμ c σ p)
      (label (M := M) hμ c (p 1)) σ := by
  apply (app_orbitGraph hμ c σ p _ _ _).mpr
  intro q hq
  refine ⟨q,le_rfl,1,?_,?_,?_⟩
  · simpa only [Diagram.permute_one] using hq
  · exact (system (M := M) (I := I) (κ := κ) hμ).atomic.eq_refl q _
  · simpa only [one_smul] using (system (M := M) (I := I) (κ := κ) hμ).atomic.eq_refl q σ

/-- All contributed inputs lie in the one invariant label set. -/
theorem orbitGraph_input (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (x y : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (h : (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x y) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF t x (labelSet (M := M) (I := I) hμ c) := by
  apply (mem_labelSet hμ c x t).mpr
  intro q hq
  obtain ⟨r,hr,π,_,hx,_⟩ := (app_orbitGraph hμ c σ p x y t).mp h q hq
  exact ⟨r,hr,π (p 1),hx⟩

/-- The graph is forced single-valued. Its two contributing diagrams are
compared only below a common condition, never by moving a fixed generic. -/
theorem orbitGraph_unique [Uncountable κ] (c : κ → ZFSet.{u})
    (hc : Function.Injective c)
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ)
    (x y z : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hy : (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x y)
    (hz : (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x z) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF t y z := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  apply S.atomic_regular.1
  intro q hq
  obtain ⟨r,hrq,π,hrπ,hxπ,hyπ⟩ := (app_orbitGraph hμ c σ p x y t).mp hy q hq
  obtain ⟨s,hsr,ρ,hsρ,hxρ,hzρ⟩ := (app_orbitGraph hμ c σ p x z t).mp hz r (hrq.trans hq)
  have heq := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hsr hxπ)) hxρ
  have hcenter : π (p 1) = ρ (p 1) := by
    by_contra hn
    exact label_not_equal hμ c hc hn s heq
  obtain ⟨s₀,hs₀⟩ := exists_condition_below s
  have hsp : s₀.2 ≤ p.permute π := (WithTop.coe_le_coe.mp (hs₀.trans (hsr.trans hrπ))).2
  have hsq : s₀.2 ≤ p.permute ρ := (WithTop.coe_le_coe.mp (hs₀.trans hsρ)).2
  have hp := Diagram.eq_of_compatible_centers hsp hsq hcenter
  have hn := smul_name_eq_of_diagram_eq hμ σ p hσ π ρ hp
  refine ⟨s,hsr.trans hrq,?_⟩
  rw [hn] at hyπ
  exact S.atomic.eq_trans (S.atomic.eq_mono hsr hyπ) (S.atomic.eq_symm hzρ)

end
end PartitionConsistency.ProductForcing

end OAI
