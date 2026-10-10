import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.OrbitNames

namespace OAI

/-! ## Descent -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Independently placed active copies are equal, for arbitrary-rank names.
A shared third copy transports the given equality into a common extension
of each potential counterexample, using the proved three-copy placement. -/
theorem active_equal_independent [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hinter : s₀.range ∩ s₁.range = p.range)
    (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ σ₁ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ₀ : ∀ g ∈ SupportFilter.Fix s₀.range, g • σ₀ = σ₀)
    (hσ₁ : ∀ g ∈ SupportFilter.Fix s₁.range, g • σ₁ = σ₁)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ v.range)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀ σ₁)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) (hβ : ∀ j ∈ p.range, β j = j)
    (hind : (s₀.permute α).range ∩ (s₀.permute β).range = p.range)
    (r : Poset M I κ)
    (hrα : r ≤ permute α (d.restrict s₀.range,s₀))
    (hrβ : r ≤ permute β (d.restrict s₀.range,s₀)) :
    (system hμ).atomic.EqF r (α • σ₀) (β • σ₀) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  apply S.atomic_regular.1
  intro a har
  obtain ⟨q,hqa⟩ := exists_condition_below a
  have hqα : q ≤ permute α (d.restrict s₀.range,s₀) :=
    WithTop.coe_le_coe.mp (hqa.trans (har.trans hrα))
  have hqβ : q ≤ permute β (d.restrict s₀.range,s₀) :=
    WithTop.coe_le_coe.mp (hqa.trans (har.trans hrβ))
  obtain ⟨π,ρ,hπ,hρ,hπρ,t,htq,htπ,htρ⟩ := descent_comparison_placement hsize hmerger
    p s₀ s₁ v hinter hv₀ hv₁ α β hα hβ hind d q.1 hd q.2 hqα.2 hqβ.2 hqα.1 hqβ.1
  have heqπ := (S.eq_symmetry π ((d,v) : Poset M I κ) σ₀ σ₁).mp heq
  have heqρ := (S.eq_symmetry ρ ((d,v) : Poset M I κ) σ₀ σ₁).mp heq
  rw [show S.move π ((d,v) : Poset M I κ) = (permute π (d,v) : Poset M I κ) from move_coe hμ π _] at heqπ
  rw [show S.move ρ ((d,v) : Poset M I κ) = (permute ρ (d,v) : Poset M I κ) from move_coe hμ ρ _] at heqρ
  have hnameπ := smul_name_eq_of_diagram_eq hμ σ₀ s₀ hσ₀ π α hπ
  have hnameρ := smul_name_eq_of_diagram_eq hμ σ₀ s₀ hσ₀ ρ β hρ
  have hnameπρ := smul_name_eq_of_diagram_eq hμ σ₁ s₁ hσ₁ π ρ hπρ
  rw [hnameπ,hnameπρ] at heqπ
  rw [hnameρ] at heqρ
  exact ⟨t,(WithTop.coe_le_coe.mpr htq).trans hqa,
    S.atomic.eq_trans (S.atomic.eq_mono (WithTop.coe_le_coe.mpr htπ) heqπ)
      (S.atomic.eq_symm (S.atomic.eq_mono (WithTop.coe_le_coe.mpr htρ) heqρ))⟩

/-- Root-preserving translates of a diagram still extend its root. -/
theorem permute_le_root (p s : Diagram M I) (hs : s ≤ p)
    (α : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) : s.permute α ≤ p := by
  have hp := Diagram.permute_eq_of_fixes_range α p hα
  rw [← hp]
  exact (Diagram.permuteOrderIso α).monotone hs

/-- Coherence for arbitrary overlaps. A third independent active copy can
be placed compatibly below every proposed common extension; the independent
comparison then identifies both given copies with that third one. -/
theorem active_equal [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ σ₁ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ₀ : ∀ g ∈ SupportFilter.Fix s₀.range, g • σ₀ = σ₀)
    (hσ₁ : ∀ g ∈ SupportFilter.Fix s₁.range, g • σ₁ = σ₁)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ v.range)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀ σ₁)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) (hβ : ∀ j ∈ p.range, β j = j)
    (r : Poset M I κ)
    (hrα : r ≤ permute α (d.restrict s₀.range,s₀))
    (hrβ : r ≤ permute β (d.restrict s₀.range,s₀)) :
    (system hμ).atomic.EqF r (α • σ₀) (β • σ₀) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  let δ := d.restrict s₀.range
  apply S.atomic_regular.1
  intro a har
  obtain ⟨q,hqa⟩ := exists_condition_below a
  have hqα : q ≤ permute α (δ,s₀) := WithTop.coe_le_coe.mp (hqa.trans (har.trans hrα))
  have hqβ : q ≤ permute β (δ,s₀) := WithTop.coe_le_coe.mp (hqa.trans (har.trans hrβ))
  have hsα : s₀.permute α ≤ p := permute_le_root p s₀ hs₀ α hα
  have hsβ : s₀.permute β ≤ p := permute_le_root p s₀ hs₀ β hβ
  have hqp : q.2 ≤ p := hqα.2.trans hsα
  have hroot : CohenForcing.Condition.Compatible (q.1.restrict p.range) (δ.restrict p.range) := by
    have hδ : (δ.permute α).restrict p.range = δ.restrict p.range :=
      CohenForcing.Condition.restrict_permute_of_fixes α δ hα
    exact CohenForcing.Condition.compatible_iff.mpr
      ⟨q.1,q.1.le_restrict _,hδ ▸ (hqα.1.trans ((δ.permute α).le_restrict _))⟩
  obtain ⟨γ,hγ,hind,t,htq,htγ⟩ := compatible_placement hsize hmerger p q.2 s₀ hqp hs₀ q.1 δ hroot
  have hsγ : s₀.permute γ ≤ p := permute_le_root p s₀ hs₀ γ hγ
  have hαγ : (s₀.permute α).range ∩ (s₀.permute γ).range = p.range := by
    apply Set.Subset.antisymm
    · intro j hj
      exact hind ▸ ⟨Diagram.range_antitone hqα.2 hj.1,hj.2⟩
    · intro j hj
      exact ⟨Diagram.range_antitone hsα hj,Diagram.range_antitone hsγ hj⟩
  have hβγ : (s₀.permute β).range ∩ (s₀.permute γ).range = p.range := by
    apply Set.Subset.antisymm
    · intro j hj
      exact hind ▸ ⟨Diagram.range_antitone hqβ.2 hj.1,hj.2⟩
    · intro j hj
      exact ⟨Diagram.range_antitone hsβ hj,Diagram.range_antitone hsγ hj⟩
  have heαγ := active_equal_independent hμ hsize hmerger p s₀ s₁ v hinter hv₀ hv₁
    σ₀ σ₁ hσ₀ hσ₁ d hd heq α γ hα hγ hαγ t
    (WithTop.coe_le_coe.mpr (htq.trans hqα)) (WithTop.coe_le_coe.mpr htγ)
  have heβγ := active_equal_independent hμ hsize hmerger p s₀ s₁ v hinter hv₀ hv₁
    σ₀ σ₁ hσ₀ hσ₁ d hd heq β γ hβ hγ hβγ t
    (WithTop.coe_le_coe.mpr (htq.trans hqβ)) (WithTop.coe_le_coe.mpr htγ)
  exact ⟨t,(WithTop.coe_le_coe.mpr htq).trans hqa,S.atomic.eq_trans heαγ (S.atomic.eq_symm heβγ)⟩

/-- Literal diagram support is inherited by stronger diagrams. -/
theorem supported_mono {p s : Diagram M I} (hsp : s ≤ p)
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ) :
    ∀ g ∈ SupportFilter.Fix s.range, g • σ = σ := by
  intro g hg
  apply hσ
  exact (SupportFilter.mem_Fix _ _).mpr
    (fun j hj => (SupportFilter.mem_Fix _ _).mp hg j (Diagram.range_antitone hsp hj))

/-- The unrestricted-rank support intersection lemma, in direct product
forcing form. Both root equalities hold under the respective restrictions
of the original Cohen witness, not under an extra compatibility hypothesis. -/
theorem support_descent [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ σ₁ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ₀ : ∀ g ∈ SupportFilter.Fix s₀.range, g • σ₀ = σ₀)
    (hσ₁ : ∀ g ∈ SupportFilter.Fix s₁.range, g • σ₁ = σ₁)
    (d : CohenForcing.Condition I κ)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀ σ₁) :
    ∃ σ : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (∀ g ∈ SupportFilter.Fix p.range, g • σ = σ) ∧
      (system hμ).atomic.EqF ((d.restrict s₀.range,s₀) : Poset M I κ) σ σ₀ ∧
      (system hμ).atomic.EqF ((d.restrict s₁.range,s₁) : Poset M I κ) σ σ₁ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hv : ∀ π ∈ SupportFilter.Fix v.range, ∀ i : Fin 2,
      π • (![σ₀,σ₁] : Fin 2 → S.Name) i = ![σ₀,σ₁] i := by
    intro π hπ i
    fin_cases i
    · exact supported_mono hμ hv₀ σ₀ hσ₀ π hπ
    · exact supported_mono hμ hv₁ σ₁ hσ₁ π hπ
  have heq' : S.atomic.EqF ((d.restrict v.range,v) : Poset M I κ) σ₀ σ₁ := by
    have hh := forces_iff_restrict hμ hsize hmerger (.equal 0 1) ![σ₀,σ₁] v hv d
    simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
      Matrix.cons_val_one] using hh.mp (by
        simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
          Matrix.cons_val_one] using heq)
  let H := SupportFilter.Fix p.range
  let f : H → S.Name := fun g => g.val • σ₀
  let a : H → Poset M I κ := fun g =>
    (permute g.val ((d.restrict v.range).restrict s₀.range,s₀) : Poset M I κ)
  have hH : H ∈ S.filter := ⟨p.range,(Diagram.cardinal_range p).trans_le hcard,le_rfl⟩
  have hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i) := by
    intro g hg i
    refine ⟨⟨g * i.val,H.mul_mem hg i.property⟩,?_,?_⟩
    · exact mul_smul g i.val σ₀
    · change (permute (g * i.val) ((d.restrict v.range).restrict s₀.range,s₀) : Poset M I κ) =
        S.move g (permute i.val ((d.restrict v.range).restrict s₀.range,s₀))
      rw [move_coe,permute_mul]
  have hc : ∀ i j q, q ≤ a i → q ≤ a j → S.atomic.EqF q (f i) (f j) := by
    intro i j q hi hj
    exact active_equal hμ hsize hmerger p s₀ s₁ v hs₀ hinter hv₀ hv₁ σ₀ σ₁ hσ₀ hσ₁
      (d.restrict v.range) (d.support_restrict_subset _) heq' i.val j.val
      ((SupportFilter.mem_Fix _ _).mp i.property) ((SupportFilter.mem_Fix _ _).mp j.property)
      q hi hj
  let σ := S.equivariantMix f a H hH hperm
  have hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ :=
    S.equivariantMix_fixed f a H hH hperm
  have hres (s : Diagram M I) (hvs : v ≤ s) :
      (d.restrict v.range).restrict s.range = d.restrict s.range := by
    ext z
    simp only [CohenForcing.Condition.mem_restrict]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,Diagram.range_antitone hvs h.2⟩,h.2⟩⟩
  have hσ₀' : S.atomic.EqF ((d.restrict s₀.range,s₀) : Poset M I κ) σ σ₀ := by
    have hh := S.eq_equivariantMix_at f a H hH hperm hc 1
    change S.atomic.EqF (a 1) σ (f 1) at hh
    simpa only [a,f,Subgroup.coe_one,permute_one,one_smul,hres s₀ hv₀] using hh
  have heq' : S.atomic.EqF ((d,v) : Poset M I κ) σ σ₁ :=
    S.atomic.eq_trans (S.atomic.eq_mono (WithTop.coe_le_coe.mpr ⟨d.le_restrict _,hv₀⟩) hσ₀') heq
  have hv' : ∀ π ∈ SupportFilter.Fix s₁.range, ∀ i : Fin 2,
      π • (![σ,σ₁] : Fin 2 → S.Name) i = ![σ,σ₁] i := by
    intro π hπ i
    fin_cases i
    · exact supported_mono hμ hs₁ σ hσ π hπ
    · exact hσ₁ π hπ
  refine ⟨σ,hσ,hσ₀',?_⟩
  have hh := forces_at_supporting_root hμ hsize hmerger (.equal 0 1)
    ![σ,σ₁] s₁ v hv₁ hv' d (by
      simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
        Matrix.cons_val_one] using heq')
  simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
    Matrix.cons_val_one] using hh

end
end PartitionConsistency.ProductForcing


/-! ## LocalName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Separation retains the literal common support of the bounding name and
all of its parameters. -/
theorem separate_fixed {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (g : Γ) (hσ : g • σ = σ) (hv : ∀ i, g • v i = v i) :
    g • S.separate σ v φ = S.separate σ v φ := by
  apply Subtype.ext
  exact S.collectName_fixed _ _ _ (S.separationTest_permute σ v φ) g
    ⟨congrArg Subtype.val hσ,(S.mem_tupleStabilizer v g).mpr hv⟩

/-- Normalizing a subset name does not enlarge its support. -/
theorem normalize_fixed (σ ν : S.Name) (g : Γ)
    (hσ : g • σ = σ) (hν : g • ν = ν) :
    g • S.normalize σ ν = S.normalize σ ν := by
  apply S.separate_fixed σ ![ν] (.mem 1 0) g hσ
  intro i
  fin_cases i
  exact hν

end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable (c : κ → ZFSet.{u})

/-- The normalization bound is the actual set of all pairs of individual
label names with condition codes; there is no bound on the ranks of the
original subsets being represented. -/
theorem labelSet_subsetBound :
    (system (M := M) (I := I) (κ := κ) hμ).subsetBound (labelSet hμ c) =
      (system (M := M) (I := I) (κ := κ) hμ).collectRaw
        (label hμ c) (fun _ _ => True) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i,p,_,rfl⟩ := (S.mem_collectRaw _ _ z).mp hz
    have hi := i.property
    simp only [labelSet_raw] at hi
    obtain ⟨j,q,_,hj,_⟩ := (S.edge_collectRaw _ _ _ _).mp hi
    exact (S.mem_collectRaw _ _ _).mpr ⟨j,p,True.intro,by rw [hj]; rfl⟩
  · intro hz
    obtain ⟨j,p,_,rfl⟩ := (S.mem_collectRaw _ _ z).mp hz
    have he : ZFSet.pair (label (M := M) hμ c j).raw (S.code ⊤) ∈ (labelSet (M := M) (I := I) hμ c).raw := by
      rw [labelSet_raw]
      exact (S.edge_collectRaw _ _ _ _).mpr ⟨j,⊤,rfl,rfl,rfl⟩
    exact (S.mem_collectRaw _ _ _).mpr
      ⟨⟨((label (M := M) hμ c j).raw,S.code ⊤),he⟩,p,True.intro,rfl⟩

/-- Every normalized candidate is forced to be a subset of the label set,
not just those candidates which happen to be classes for a particular E. -/
theorem normalized_subset_labelSet
    (ν : (system (M := M) (I := I) (κ := κ) hμ).PowerCandidate (labelSet hμ c))
    (p : Poset M I κ) :
    (system hμ).SubsetF p ν.val (labelSet hμ c) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  intro τ q _ hm
  apply (mem_labelSet hμ c τ q).mpr
  intro s hsq
  obtain ⟨t,hts,ρ,d,he,_,heq⟩ := S.mem_iff.mp hm s hsq
  have hb := ν.property he
  rw [labelSet_subsetBound hμ c] at hb
  obtain ⟨j,_,_,hj,_⟩ := (S.edge_collectRaw _ _ _ _).mp hb
  have hh : label (M := M) hμ c j = ρ := Name.ext hj
  exact ⟨t,hts,j,hh ▸ heq⟩

/-- The ground collection X(r): all normalized subset names supported
literally by the diagram range. It is a set, rather than an unrestricted
class of HS names. -/
def LocalName (r : Diagram M I) :=
  {ν : (system (M := M) (I := I) (κ := κ) hμ).PowerCandidate (labelSet hμ c) //
    ∀ π ∈ SupportFilter.Fix r.range, π • ν.val = ν.val}

instance (r : Diagram M I) : Small.{u} (LocalName hμ c r) := inferInstanceAs
  (Small.{u} {ν : (system (M := M) (I := I) (κ := κ) hμ).PowerCandidate (labelSet hμ c) //
    ∀ π ∈ SupportFilter.Fix r.range, π • ν.val = ν.val})

namespace LocalName
variable {hμ c}

def name {r : Diagram M I} (ν : LocalName hμ c r) :
    (system (M := M) (I := I) (κ := κ) hμ).Name := ν.val.val

theorem fixed {r : Diagram M I} (ν : LocalName hμ c r) :
    ∀ π ∈ SupportFilter.Fix r.range, π • ν.name = ν.name := ν.property

@[ext] theorem ext {r : Diagram M I} {ν τ : LocalName hμ c r}
    (h : ν.name = τ.name) : ν = τ := Subtype.ext (Subtype.ext h)

def restrict {r s : Diagram M I} (hsr : s ≤ r) (ν : LocalName hμ c r) :
    LocalName hμ c s :=
  ⟨ν.val,supported_mono hμ hsr ν.name ν.fixed⟩

@[simp] theorem restrict_name {r s : Diagram M I} (hsr : s ≤ r)
    (ν : LocalName hμ c r) : (ν.restrict hsr).name = ν.name := rfl

@[simp] theorem restrict_restrict {r s t : Diagram M I} (hsr : s ≤ r) (hts : t ≤ s)
    (ν : LocalName hμ c r) : (ν.restrict hsr).restrict hts = ν.restrict (hts.trans hsr) := rfl

theorem restrict_injective {r s : Diagram M I} (hsr : s ≤ r) :
    Function.Injective (restrict (hμ := hμ) (c := c) hsr) := by
  intro ν τ h
  exact ext (congrArg (name (r := s)) h)

end LocalName

/-- Canonical normalization into X(r), for any supported name at any rank. -/
def localNormalize (r : Diagram M I)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hν : ∀ π ∈ SupportFilter.Fix r.range, π • ν = ν) : LocalName hμ c r :=
  ⟨⟨(system hμ).normalize (labelSet hμ c) ν,(system hμ).normalize_bounded _ _⟩,
    fun π hπ => (system hμ).normalize_fixed _ _ π (smul_labelSet hμ c π) (hν π hπ)⟩

theorem localNormalize_eq (r : Diagram M I)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hν : ∀ π ∈ SupportFilter.Fix r.range, π • ν = ν)
    (p : Poset M I κ) (hsub : (system hμ).SubsetF p ν (labelSet hμ c)) :
    (system hμ).atomic.EqF p ν (localNormalize hμ c r ν hν).name :=
  (system hμ).normalize_eq _ _ hsub

/-- Every literally supported raw subset of the normalization bound is HS.
Thus X(r) omits no supported normalized name by using the HS-name type. -/
theorem localName_of_raw (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (ν : ZFSet.{u})
    (hb : ν ⊆ (system (M := M) (I := I) (κ := κ) hμ).subsetBound (labelSet hμ c))
    (hν : ∀ π ∈ SupportFilter.Fix r.range,
      mapConditions ((system (M := M) (I := I) (κ := κ) hμ).action.actCode π) ν = ν) :
    ∃ τ : LocalName hμ c r, τ.name.raw = ν := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hcodes : ν ⊆ S.collectRaw (label hμ c) (fun _ _ => True) := by
    rwa [labelSet_subsetBound hμ c] at hb
  have hn : IsName S.action.conditions ν := by
    apply IsName.intro
    intro z hz
    obtain ⟨j,p,_,rfl⟩ := (S.mem_collectRaw _ _ z).mp (hcodes hz)
    exact ⟨(label (M := M) hμ c j).raw,S.code p,rfl,S.code_mem p,
      (label (M := M) hμ c j).isName⟩
  let ν' : S.action.Name := ⟨ν,hn⟩
  have hs : ConditionAction.Name.HS S.filter ν' := by
    apply ConditionAction.Name.hs_iff.mpr
    constructor
    · apply S.normal.2.1 (SupportFilter.Fix r.range) _
        ⟨r.range,(Diagram.cardinal_range r).trans_le hcard,le_rfl⟩
      intro π hπ
      exact ConditionAction.Name.ext (hν π hπ)
    · rintro τ ⟨a,ha⟩
      obtain ⟨j,_,_,hj,_⟩ := (S.edge_collectRaw _ _ _ _).mp (hcodes ha)
      have hh : (label (M := M) hμ c j).val = τ := ConditionAction.Name.ext hj
      exact hh ▸ (label (M := M) hμ c j).hs
  exact ⟨⟨⟨⟨ν',hs⟩,hb⟩,fun π hπ => Name.ext (hν π hπ)⟩,rfl⟩

/-- Support descent followed by normalization supplies a member of the
*ground set* X(p), with the equalities at the two original supporting roots.
No statement that the descended name is a class is postulated here. -/
theorem localName_descent [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ : LocalName hμ c s₀) (σ₁ : LocalName hμ c s₁)
    (d : CohenForcing.Condition I κ)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀.name σ₁.name) :
    ∃ σ : LocalName hμ c p,
      (system hμ).atomic.EqF ((d.restrict s₀.range,s₀) : Poset M I κ) σ.name σ₀.name ∧
      (system hμ).atomic.EqF ((d.restrict s₁.range,s₁) : Poset M I κ) σ.name σ₁.name := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨ν,hν,hν₀,hν₁⟩ := support_descent hμ hcard hsize hmerger p s₀ s₁ v hs₀ hs₁
    hinter hv₀ hv₁ σ₀.name σ₁.name σ₀.fixed σ₁.fixed d heq
  have hn (i : Poset M I κ) (σ : S.PowerCandidate (labelSet hμ c))
      (hi : S.atomic.EqF i ν σ.val) :
      S.atomic.EqF i (localNormalize hμ c p ν hν).name σ.val := by
    have hsub : S.SubsetF i ν (labelSet hμ c) :=
      (S.subset_congr hi (S.atomic.eq_refl i (labelSet hμ c))).mpr
        (normalized_subset_labelSet hμ c σ i)
    exact S.atomic.eq_trans (S.atomic.eq_symm (localNormalize_eq hμ c p ν hν i hsub)) hi
  exact ⟨localNormalize hμ c p ν hν,hn _ σ₀.val hν₀,hn _ σ₁.val hν₁⟩

end
end PartitionConsistency.ProductForcing


/-! ## LocalQuotient -/

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

/-- Transport of a filter along an order automorphism. It transports the
filter, not the interpretation of all names in a single fixed extension. -/
def GenericFilter.move (F : GenericFilter P) (e : P ≃o P) : GenericFilter P where
  carrier := {p | e.symm p ∈ F}
  lower' := by
    intro p q hpq hq
    exact F.lower (e.symm.monotone hpq) hq
  nonempty' := by
    obtain ⟨p,hp⟩ := F.nonempty
    refine ⟨e p,?_⟩
    change e.symm (e p) ∈ F
    exact (e.symm_apply_apply p).symm ▸ hp
  directed' := by
    intro p hp q hq
    obtain ⟨r,hr,hrp,hrq⟩ := F.directed _ hp _ hq
    refine ⟨e r,?_,?_,?_⟩
    · change e.symm (e r) ∈ F
      exact (e.symm_apply_apply r).symm ▸ hr
    · change e r ≤ p
      exact e.apply_symm_apply p ▸ e.monotone hrp
    · change e r ≤ q
      exact e.apply_symm_apply q ▸ e.monotone hrq

@[simp] theorem GenericFilter.mem_move (F : GenericFilter P) (e : P ≃o P) (p : P) :
    e p ∈ F.move e ↔ p ∈ F := by change e.symm (e p) ∈ F ↔ p ∈ F; simp

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

/-- Atomic forcing at a fixed ground diagram, retaining the Cohen coordinate
as the forcing parameter. Its laws follow from actual product forcing. -/
def localAtomic (r : Diagram M I) :
    AtomicData (CohenForcing.Condition I κ) (system (M := M) (I := I) (κ := κ) hμ).Name where
  EqF d σ τ := (system hμ).atomic.EqF ((d,r) : Poset M I κ) σ τ
  MemF d σ τ := (system hμ).atomic.MemF ((d,r) : Poset M I κ) σ τ
  eq_mono h := (system hμ).atomic.eq_mono (WithTop.coe_le_coe.mpr ⟨h,le_rfl⟩)
  mem_mono h := (system hμ).atomic.mem_mono (WithTop.coe_le_coe.mpr ⟨h,le_rfl⟩)
  eq_refl _ σ := (system hμ).atomic.eq_refl _ σ
  eq_symm := (system hμ).atomic.eq_symm
  eq_trans := (system hμ).atomic.eq_trans
  mem_congr := (system hμ).atomic.mem_congr

/-- The local equality relation is witnessed by a Cohen condition in F. -/
def localSetoid (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I) :
    Setoid (LocalName hμ c r) where
  r σ τ := (localAtomic hμ r).EqG F σ.name τ.name
  iseqv := ⟨fun σ => (localAtomic hμ r).eqG_refl F σ.name,
    fun h => (localAtomic hμ r).eqG_symm F h,
    fun h k => (localAtomic hμ r).eqG_trans F h k⟩

/-- All local normalized subsets modulo local forced equality. The local
E-class sets used subsequently are subcollections of this actual quotient. -/
def LocalQuotient (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I) :=
  Quotient (localSetoid (c := c) hμ F r)

instance (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I) :
    Small.{u} (LocalQuotient (c := c) hμ F r) :=
  small_of_surjective (Quotient.mk'_surjective (s := localSetoid (c := c) hμ F r))

namespace LocalQuotient
variable {hμ}
variable (F : GenericFilter (CohenForcing.Condition I κ))

def ofName {r : Diagram M I} (σ : LocalName hμ c r) : LocalQuotient (c := c) hμ F r :=
  Quotient.mk _ σ

theorem ofName_eq {r : Diagram M I} (σ τ : LocalName hμ c r) :
    ofName F σ = ofName F τ ↔ (localAtomic hμ r).EqG F σ.name τ.name :=
  Quotient.eq

/-- Retaining the same representative gives the restriction/inclusion map. -/
def restrict {r s : Diagram M I} (hsr : s ≤ r) :
    LocalQuotient (c := c) hμ F r → LocalQuotient (c := c) hμ F s :=
  Quotient.map (LocalName.restrict hsr) (by
    rintro σ τ ⟨d,hd,h⟩
    refine ⟨d,hd,?_⟩
    exact (system hμ).atomic.eq_mono
      (p := ((OrderDual.ofDual d,r) : Poset M I κ))
      (q := ((OrderDual.ofDual d,s) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨le_rfl,hsr⟩) h)

@[simp] theorem restrict_ofName {r s : Diagram M I} (hsr : s ≤ r)
    (σ : LocalName hμ c r) : restrict F hsr (ofName F σ) = ofName F (σ.restrict hsr) := rfl

@[simp] theorem restrict_refl {r : Diagram M I} (x : LocalQuotient (c := c) hμ F r) :
    restrict F le_rfl x = x := by
  induction x using Quotient.inductionOn
  rfl

@[simp] theorem restrict_restrict {r s t : Diagram M I} (hsr : s ≤ r) (hts : t ≤ s)
    (x : LocalQuotient (c := c) hμ F r) :
    restrict F hts (restrict F hsr x) = restrict F (hts.trans hsr) x := by
  induction x using Quotient.inductionOn
  rfl

/-- Local decision prevents a stronger diagram from identifying distinct
local classes. No genericity hypothesis on F is needed for this direction. -/
theorem restrict_injective [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {r s : Diagram M I} (hsr : s ≤ r) :
    Function.Injective (restrict (c := c) (hμ := hμ) F hsr) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h σ =>
    induction y using Quotient.inductionOn with
    | h τ =>
      intro h
      obtain ⟨d,hd,heq⟩ := (ofName_eq F (σ.restrict hsr) (τ.restrict hsr)).mp h
      apply (ofName_eq F σ τ).mpr
      refine ⟨d.restrict r.range,F.lower (d.le_restrict _) hd,?_⟩
      have hfix : ∀ π ∈ SupportFilter.Fix r.range, ∀ i : Fin 2,
          π • (![σ.name,τ.name] : Fin 2 → (system hμ).Name) i = ![σ.name,τ.name] i := by
        intro π hπ i
        fin_cases i
        · exact σ.fixed π hπ
        · exact τ.fixed π hπ
      have hh := forces_at_supporting_root hμ hsize hmerger (.equal 0 1)
        ![σ.name,τ.name] r s hsr hfix d (by exact heq)
      exact hh

/-- The intersection property of local symbolic subsets. This is the
quotient-level consequence of the proved arbitrary-rank support descent. -/
theorem intersection [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (x₀ : LocalQuotient (c := c) hμ F s₀) (x₁ : LocalQuotient (c := c) hμ F s₁)
    (heq : restrict F hv₀ x₀ = restrict F hv₁ x₁) :
    ∃ x : LocalQuotient (c := c) hμ F p,
      restrict F hs₀ x = x₀ ∧ restrict F hs₁ x = x₁ := by
  induction x₀ using Quotient.inductionOn with
  | h σ₀ =>
    induction x₁ using Quotient.inductionOn with
    | h σ₁ =>
      obtain ⟨d,hd,heq⟩ := (ofName_eq F (σ₀.restrict hv₀) (σ₁.restrict hv₁)).mp heq
      obtain ⟨σ,hσ₀,hσ₁⟩ := localName_descent hμ c hcard hsize hmerger p s₀ s₁ v hs₀ hs₁
        hinter hv₀ hv₁ σ₀ σ₁ d heq
      exact ⟨ofName F σ,(ofName_eq F _ _).mpr
        ⟨d.restrict s₀.range,F.lower (d.le_restrict _) hd,hσ₀⟩,
        (ofName_eq F _ _).mpr ⟨d.restrict s₁.range,F.lower (d.le_restrict _) hd,hσ₁⟩⟩

end LocalQuotient

/-- Literal transport carries the entire local-name collection to the moved
diagram, including normalization and the full supporting fixer. -/
def LocalName.transport {r : Diagram M I} (π : Equiv.Perm I) (σ : LocalName hμ c r) :
    LocalName hμ c (r.permute π) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  refine ⟨⟨π • σ.name,?_⟩,?_⟩
  · have hb := mapConditions_mono (S.action.actCode π) σ.val.property
    change mapConditions (S.action.actCode π) σ.name.raw ⊆
      mapConditions (S.action.actCode π) (S.subsetBound (labelSet hμ c)) at hb
    rw [S.subsetBound_fixed _ π (smul_labelSet hμ c π)] at hb
    exact hb
  · exact transported_name_supported hμ r (r.permute π) π rfl σ.name σ.fixed

@[simp] theorem LocalName.transport_name {r : Diagram M I} (π : Equiv.Perm I)
    (σ : LocalName hμ c r) : (σ.transport hμ π).name = π • σ.name := rfl

/-- Transport of local symbolic names is between F and πF. This is not an
action on some fixed evaluated universe. -/
def LocalQuotient.transport (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) {r : Diagram M I} :
    LocalQuotient (c := c) hμ F r →
      LocalQuotient (c := c) hμ (F.move (CohenForcing.Condition.permuteOrderIso π)) (r.permute π) :=
  Quotient.map (LocalName.transport hμ π) (by
    rintro σ τ ⟨d,hd,heq⟩
    refine ⟨d.permute π,(GenericFilter.mem_move F _ d).mpr hd,?_⟩
    have hh := ((system hμ).eq_symmetry π ((OrderDual.ofDual d,r) : Poset M I κ) σ.name τ.name).mp heq
    change (system hμ).atomic.EqF
      ((CohenForcing.Condition.permute π (OrderDual.ofDual d),r.permute π) : Poset M I κ)
        (π • σ.name) (π • τ.name)
    simpa only [move_coe,permute] using hh)

end
end PartitionConsistency.ProductForcing

end OAI
