import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.LocalRecords

namespace OAI

/-! ## Eligible -/


namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Actual forcing eligibility, not the existence of a preselected class
representative or a coding witness. -/
def EligibleName (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r) : Prop :=
  ∃ d : CohenForcing.Condition I κ, d ∈ F ∧ (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d,r) : Poset M I κ)
    (SetLanguage.isClass 0 1 2)

private theorem eligibleName_transport (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ σ : LocalName hμ c r)
    (he : (localAtomic hμ r).EqG F τ.name σ.name) :
    EligibleName hμ c F r E τ → EligibleName hμ c F r E σ := by
  rintro ⟨d,hd,hτ⟩
  obtain ⟨a,ha,he⟩ := he
  obtain ⟨b,hb,hbd,hba⟩ := F.directed _ hd _ ha
  refine ⟨b,hb,?_⟩
  have hbt : ((OrderDual.ofDual b,r) : Poset M I κ) ≤ ((OrderDual.ofDual d,r) : Poset M I κ) :=
    WithTop.coe_le_coe.mpr ⟨hbd,le_rfl⟩
  have hbe : ((OrderDual.ofDual b,r) : Poset M I κ) ≤ ((OrderDual.ofDual a,r) : Poset M I κ) :=
    WithTop.coe_le_coe.mpr ⟨hba,le_rfl⟩
  apply ((system hμ).atomic.forceFormula_tuple_congr
    (p := ((OrderDual.ofDual b,r) : Poset M I κ))
    (v := ![τ.name,labelSet hμ c,E]) (w := ![σ.name,labelSet hμ c,E])
    (φ := SetLanguage.isClass 0 1 2) ?_).mp
      ((system hμ).atomic.forceFormula_mono hbt hτ)
  intro i
  fin_cases i
  · exact (system hμ).atomic.eq_mono hbe he
  · exact (system hμ).atomic.eq_refl _ _
  · exact (system hμ).atomic.eq_refl _ _

theorem eligibleName_congr (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ σ : LocalName hμ c r)
    (he : (localAtomic hμ r).EqG F τ.name σ.name) :
    EligibleName hμ c F r E τ ↔ EligibleName hμ c F r E σ :=
  ⟨eligibleName_transport hμ c F r E τ σ he,
    eligibleName_transport hμ c F r E σ τ ((localAtomic hμ r).eqG_symm F he)⟩

/-- The class assertion descends to the actual local name quotient. -/
def Eligible (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) : LocalQuotient (c := c) hμ F r → Prop :=
  Quotient.lift (EligibleName hμ c F r E) (fun τ σ he =>
    propext (eligibleName_congr hμ c F r E τ σ he))

@[simp] theorem eligible_ofName (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r) :
    Eligible hμ c F r E (LocalQuotient.ofName F τ) ↔ EligibleName hμ c F r E τ := Iff.rfl

theorem eligible_restrict (F : GenericFilter (CohenForcing.Condition I κ))
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) {r s : Diagram M I} (hsr : s ≤ r)
    (x : LocalQuotient (c := c) hμ F r) (hx : Eligible hμ c F r E x) :
    Eligible hμ c F s E (LocalQuotient.restrict F hsr x) := by
  induction x using Quotient.inductionOn with
  | h τ =>
    obtain ⟨d,hd,he⟩ := hx
    exact ⟨d,hd,(system hμ).atomic.forceFormula_mono
      (p := ((d,r) : Poset M I κ)) (q := ((d,s) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨le_rfl,hsr⟩) he⟩

/-- Decision of the class test at its supporting root reflects eligibility
from every stronger diagram. No assertion of E being an equivalence relation
or of nonwellorderability is needed for this logical step. -/
theorem eligible_restrict_iff [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    {r s : Diagram M I} (hsr : s ≤ r)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E)
    (x : LocalQuotient (c := c) hμ F r) :
    Eligible hμ c F s E (LocalQuotient.restrict F hsr x) ↔ Eligible hμ c F r E x := by
  constructor
  · induction x using Quotient.inductionOn with
    | h τ =>
      rintro ⟨d,hd,hf⟩
      refine ⟨d.restrict r.range,F.lower (d.le_restrict _) hd,?_⟩
      apply forces_at_supporting_root hμ hsize hmerger (SetLanguage.isClass 0 1 2)
        ![τ.name,labelSet hμ c,E] r s hsr ?_ d hf
      intro π hπ i
      fin_cases i
      · exact τ.fixed π hπ
      · exact smul_labelSet hμ c π
      · exact hE π hπ
  · exact eligible_restrict hμ c F E hsr x

/-- D_F(r), before restricting diagrams to lie below a fixed supporting
root. Its only membership test is the forcing assertion that a name is a
class of some element of A. -/
def EligibleClasses (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) :=
  {x : LocalQuotient (c := c) hμ F r // Eligible hμ c F r E x}

instance (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) : Small.{u} (EligibleClasses hμ c F r E) :=
  inferInstanceAs (Small.{u} {x : LocalQuotient (c := c) hμ F r // Eligible hμ c F r E x})

/-- Every label in the range has its canonical eligible class name. -/
def eligibleLabel (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (j : I) (hj : j ∈ r.range) :
    EligibleClasses hμ c F r E := by
  refine ⟨LocalQuotient.ofName F (localLabelClass hμ c r E hE j hj),?_⟩
  obtain ⟨d,hd⟩ := F.nonempty
  exact ⟨d,hd,forces_localLabelClass_isClass hμ c r E hE j hj _⟩

/-- A genuinely dense set of Cohen conditions giving literal local records.
The diagram may be strengthened and the condition's support put in it. -/
def classRepresentationSet (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (τ : LocalName hμ c r) : Set (CohenForcing.Condition I κ) :=
  {d | ∃ t : Diagram M I, t ≤ r ∧ d.support ⊆ t.range ∧ ∃ j ∈ t.range,
    (system hμ).atomic.EqF ((d,t) : Poset M I κ) τ.name (labelClass hμ c E j)}

theorem classRepresentationSet_denseBelow [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e*x))ᶜ : Set M) = Cardinal.mk M)
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r)
    (d₀ : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d₀,r) : Poset M I κ)
      (SetLanguage.isClass 0 1 2)) :
    ∀ d, d ≤ d₀ → ∃ a, a ≤ d ∧ a ∈ classRepresentationSet hμ c r E τ := by
  intro d hdd
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨t,ht,x,hx,heq⟩ := (S.forces_isClass _ _ _ _ _).mp hf
    ((d,r) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hdd,le_rfl⟩)
  obtain ⟨s,hst,j,hxj⟩ := (mem_labelSet hμ c x t).mp hx t le_rfl
  let : Nonempty (Diagram M I) := ⟨r⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  have hear := (WithTop.coe_le_coe.mp ((has.trans hst).trans ht))
  have hU : Cardinal.mk ↥(a.1.support ∪ {j}) ≤ Cardinal.mk M := by
    apply (Cardinal.mk_union_le _ _).trans
    have hω := Cardinal.aleph0_le_mk M
    apply (add_le_add (a.1.cardinal_support.trans hω) ?_).trans_eq (Cardinal.add_eq_self hω)
    simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hω
  obtain ⟨b,hb,hcover⟩ := Diagram.extend_through hsize e he a.2 hU
  have hba : b ≤ a.2 := ⟨e,hb⟩
  have hlt : ((a.1,b) : Poset M I κ) ≤ t :=
    ((WithTop.coe_le_coe.mpr (show (a.1,b) ≤ a from ⟨le_rfl,hba⟩)).trans has).trans hst
  have hls : ((a.1,b) : Poset M I κ) ≤ s :=
    (WithTop.coe_le_coe.mpr (show (a.1,b) ≤ a from ⟨le_rfl,hba⟩)).trans has
  refine ⟨a.1,hear.1,b,hba.trans hear.2,fun k hk => hcover (Or.inl hk),j,
    hcover (Or.inr (Set.mem_singleton j)),?_⟩
  exact S.atomic.eq_trans (S.atomic.eq_mono hlt heq)
    (S.relationClass_congr (S.atomic.eq_refl _ _) (S.atomic.eq_refl _ _)
      (S.atomic.eq_mono hls hxj))

/-- Padding the preceding local witness set with incompatible conditions
is dense in the entire Cohen poset, as required for ordinary genericity. -/
def classRepresentationDenseSet (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (τ : LocalName hμ c r) (d₀ : CohenForcing.Condition I κ) : Set (CohenForcing.Condition I κ) :=
  {d | d ∈ classRepresentationSet hμ c r E τ ∨ ¬ Compatible d d₀}

theorem classRepresentationDenseSet_dense [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e*x))ᶜ : Set M) = Cardinal.mk M)
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r)
    (d₀ : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d₀,r) : Poset M I κ)
      (SetLanguage.isClass 0 1 2)) : Dense (classRepresentationDenseSet hμ c r E τ d₀) :=
  dense_local_or_incompatible d₀ _
    (classRepresentationSet_denseBelow hμ c hsize e he r E τ d₀ hf)

/-- Meeting this specific dense set supplies the record used in the local
quotient bound. Arbitrary filters are not silently declared generic. -/
theorem localWitness_of_meets (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀ ∈ F)
    (hmeets : ∃ d, d ∈ F ∧ d ∈ classRepresentationDenseSet hμ c r E τ d₀) :
    Nonempty (LocalWitness hμ F r (labelClass hμ c E) τ) := by
  obtain ⟨d,hd,hm⟩ := hmeets
  rcases hm with hm | hbad
  · obtain ⟨t,⟨b,hb⟩,hs,j,⟨x,rfl⟩,hx⟩ := hm
    exact ⟨⟨t,b,hb,x,d,hd,hs,hx⟩⟩
  · exact (hbad (compatible_of_mem F hd hd₀)).elim

end
end PartitionConsistency.ProductForcing


/-! ## ActualAvailability -/

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
variable {M I : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- Among two subdiagrams of the same larger diagram, range containment
reflects the diagram order. Common embeddability is essential here. -/
theorem le_of_common_and_range {t r s : Diagram M I} (htr : t ≤ r) (hts : t ≤ s)
    (hrs : s.range ⊆ r.range) : r ≤ s := by
  obtain ⟨a,rfl⟩ := htr
  obtain ⟨b,rfl⟩ := hts
  obtain ⟨c,hc⟩ := hrs (show t b ∈ (t.sub b).range by exact ⟨1,by simp⟩)
  have hab : a*c = b := t.injective hc
  exact ⟨c,by rw [sub_sub,hab]⟩

/-- An exact intersection of two roots which both extend q still extends q. -/
theorem intersection_le_root {p s₀ s₁ q : Diagram M I}
    (hs₀ : s₀ ≤ p) (h₀q : s₀ ≤ q) (h₁q : s₁ ≤ q)
    (hinter : s₀.range ∩ s₁.range = p.range) : p ≤ q := by
  apply le_of_common_and_range hs₀ h₀q
  rw [← hinter]
  exact fun _ h => ⟨range_antitone h₀q h,range_antitone h₁q h⟩

end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The local quotient bound for the actual E-class predicate. The meet
assumption is only for the explicitly proved dense record sets; it must be
supplied by ordinary forcing, not by declaring an arbitrary filter generic. -/
theorem eligibleClasses_cardinal_le [Infinite M] [Infinite I]
    (hpower : μ ^ Cardinal.aleph0 = μ) (hcard : Cardinal.mk M ≤ μ)
    (hκ : Cardinal.mk κ ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E)
    (hmeets : ∀ (τ : LocalName hμ c r) (d₀ : CohenForcing.Condition I κ), d₀ ∈ F →
      (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d₀,r) : Poset M I κ)
        (SetLanguage.isClass 0 1 2) →
      ∃ d, d ∈ F ∧ d ∈ classRepresentationDenseSet hμ c r E τ d₀) :
    Cardinal.mk (Shrink.{u} (EligibleClasses hμ c F r E)) ≤ μ := by
  let A := EligibleClasses hμ c F r E
  let B := LocallyRepresented (c := c) hμ F r (labelClass hμ c E)
  have hrep (a : A) : ∃ τ : LocalName hμ c r,
      LocalQuotient.ofName F τ = a.val ∧
      Nonempty (LocalWitness hμ F r (labelClass hμ c E) τ) := by
    obtain ⟨τ,hτ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ F r) a.val
    have hτ' : LocalQuotient.ofName F τ = a.val := hτ
    have ha : EligibleName hμ c F r E τ :=
      (eligible_ofName hμ c F r E τ).mp (hτ'.symm ▸ a.property)
    obtain ⟨d₀,hd₀,hf⟩ := ha
    exact ⟨τ,hτ,localWitness_of_meets hμ c F r E τ d₀ hd₀ (hmeets τ d₀ hd₀ hf)⟩
  let f : A → B := fun a => ⟨a.val,hrep a⟩
  have hinj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : B => z.val) h)
  have hbound : Cardinal.mk (Shrink.{u} A) ≤ Cardinal.mk (Shrink.{u} B) :=
    Cardinal.mk_le_of_injective ((equivShrink B).injective.comp
      (hinj.comp (equivShrink A).symm.injective))
  apply hbound.trans
  apply locallyRepresented_cardinal_le hμ hpower hcard hκ hsize hmerger F r _
  intro π hπ j
  rw [labelClass_move,hE π hπ]

/-- The actual symbolic class system below q. Outside the cone below q the
object type is empty, so no meaningless eligibility assertions are needed.
All maps retain representative names and all axioms are proved. -/
def eligibleSystem [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (q : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) :
    LocalDiagramSystem.System.{u,u+1} M I where
  Obj r := {x : LocalQuotient (c := c) hμ F r // r ≤ q ∧ Eligible hμ c F r E x}
  restrict hsr x := ⟨LocalQuotient.restrict F hsr x.val,
    hsr.trans x.property.1,eligible_restrict hμ c F E hsr x.val x.property.2⟩
  restrict_refl x := Subtype.ext (LocalQuotient.restrict_refl F x.val)
  restrict_comp hsr hts x := Subtype.ext (LocalQuotient.restrict_restrict F hsr hts x.val)
  injective := by
    intro r s hsr x y h
    exact Subtype.ext (LocalQuotient.restrict_injective F hsize hmerger hsr
      (congrArg Subtype.val h))
  intersection p s₀ s₁ t hs₀ hs₁ hinter ht₀ ht₁ x₀ x₁ heq := by
    have hpq := Diagram.intersection_le_root hs₀ x₀.property.1 x₁.property.1 hinter
    obtain ⟨x,hx₀,hx₁⟩ := LocalQuotient.intersection F hcard hsize hmerger
      p s₀ s₁ t hs₀ hs₁ hinter ht₀ ht₁ x₀.val x₁.val (congrArg Subtype.val heq)
    have hel : Eligible hμ c F p E x := by
      apply (eligible_restrict_iff hμ c hsize hmerger F E hs₀
        (supported_mono hμ hpq E hE) x).mp
      rw [hx₀]
      exact x₀.property.2
    exact ⟨⟨x,hpq,hel⟩,Subtype.ext hx₀,Subtype.ext hx₁⟩

/-- The availability set of an eligible E-class is the source's actual ideal:
it records existence of representatives at subdiagrams, not an ideal supplied
as extra structure. This specializes the proved intersection calculus. -/
def classAvailability [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (q r : Diagram M I) (a : M)
    (hqa : r.sub a = q)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (x : EligibleClasses hμ c F r E) : DiagramOrder.ConeIdeal (show DiagramOrder.LeftDivOrder M from a) :=
  (eligibleSystem hμ c hcard hsize hmerger F q E hE).availability r a
    ⟨x.val,⟨a,hqa⟩,x.property⟩

end
end PartitionConsistency.ProductForcing


/-! ## Contraction -/

namespace PartitionConsistency.DiagramOrder.ConeIdeal
universe u
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

/-- An ideal can be recovered above any member by taking joins with it. -/
theorem mem_iff_mem_join {a : LeftDivOrder M} (U : ConeIdeal a)
    {n z j : LeftDivOrder M} (hn : n ∈ U.carrier) (hj : IsLUB {z,n} j) :
    z ∈ U.carrier ↔ j ∈ U.carrier :=
  ⟨fun hz => U.join_closed hz hn hj, fun hjU => U.lower (hj.1 (by simp)) hjU⟩

/-- Contraction of an actual bounded ideal, with no new choice of an ideal. -/
def contract {a : LeftDivOrder M} (U : ConeIdeal a)
    {n c : LeftDivOrder M} (hn : n ∈ U.carrier) (hnc : n*c = a) : ConeIdeal c where
  carrier := {x | n*x ∈ U.carrier}
  nonempty := ⟨1,by change n*1 ∈ U.carrier; simpa only [mul_one] using hn⟩
  bounded := by
    intro x hx
    apply (LeftDivOrder.mul_le_mul_left_iff n x c).mp
    rw [hnc]
    exact U.bounded hx
  lower := by
    intro x y hxy hy
    exact U.lower ((LeftDivOrder.mul_le_mul_left_iff n y x).mpr hxy) hy
  join_closed := by
    intro x y j hx hy hj
    exact U.join_closed hx hy (LeftDivOrder.isLUB_mul_left n hj)

@[simp] theorem mem_contract {a : LeftDivOrder M} (U : ConeIdeal a)
    {n c : LeftDivOrder M} (hn : n ∈ U.carrier) (hnc : n*c = a) (x : LeftDivOrder M) :
    x ∈ (U.contract hn hnc).carrier ↔ n*x ∈ U.carrier := Iff.rfl

/-- In a monoid with conditional joins the contraction remembers the full
ideal, provided that its contraction index belongs to that ideal. -/
theorem eq_of_contract_eq (hj : HasConditionalJoins (LeftDivOrder M))
    {a n c : LeftDivOrder M} {U V : ConeIdeal a} (hnU : n ∈ U.carrier)
    (hnV : n ∈ V.carrier) (hnc : n*c = a)
    (h : U.contract hnU hnc = V.contract hnV hnc) : U = V := by
  apply ConeIdeal.ext
  ext z
  by_cases hza : z ≤ a
  · obtain ⟨j,hj⟩ := hj z n a hza (U.bounded hnU)
    obtain ⟨x,hx⟩ := hj.1 (by simp : n ∈ ({z,n} : Set (LeftDivOrder M)))
    rw [U.mem_iff_mem_join hnU hj,V.mem_iff_mem_join hnV hj,← hx]
    exact Set.ext_iff.mp (congrArg ConeIdeal.carrier h) x
  · exact ⟨fun hz => (hza (U.bounded hz)).elim,fun hz => (hza (V.bounded hz)).elim⟩

@[simp] theorem contract_one {a : LeftDivOrder M} (U : ConeIdeal a)
    (h : (1 : LeftDivOrder M) ∈ U.carrier) : U.contract h (one_mul a) = U := by
  apply ConeIdeal.ext
  ext x
  simp only [mem_contract,one_mul]

/-- Two contractions equal contraction at the product, literally on their
carriers. -/
theorem contract_contract {a n c m b : LeftDivOrder M} (U : ConeIdeal a)
    (hn : n ∈ U.carrier) (hnc : n*c = a)
    (hm : m ∈ (U.contract hn hnc).carrier) (hmb : m*b = c) :
    (U.contract hn hnc).contract hm hmb =
      U.contract hm (by rw [mul_assoc,hmb,hnc]) := by
  apply ConeIdeal.ext
  ext x
  exact iff_of_eq (congrArg (fun j => j ∈ U.carrier) (mul_assoc n m x).symm)

end PartitionConsistency.DiagramOrder.ConeIdeal

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I)

/-- Inclusion from a fixed earlier level preserves and reflects being in
any later range. -/
theorem restrict_range_iff {r s t : Diagram M I} (hrs : r ≤ s) (hst : s ≤ t)
    (y : D.Obj s) :
    (∃ z : D.Obj t, D.restrict (hrs.trans hst) z = D.restrict hrs y) ↔
      ∃ z : D.Obj t, D.restrict hst z = y := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,D.injective hrs (by rw [D.restrict_comp]; exact hz)⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,by rw [← D.restrict_comp hst hrs,hz]⟩

/-- Equality of target diagrams is sufficient to compare the ranges; all
order proofs are irrelevant. -/
theorem range_congr {r s t : Diagram M I} (x : D.Obj r)
    (hrs : r ≤ s) (hrt : r ≤ t) (h : s = t) :
    (∃ y : D.Obj s, D.restrict hrs y = x) ↔
      ∃ y : D.Obj t, D.restrict hrt y = x := by
  subst t
  rfl

/-- Availability transforms by multiplication of the subdiagram indices. -/
theorem available_sub_iff (r : Diagram M I) (n m : M) (y : D.Obj (r.sub n)) :
    D.Available (r.sub n) y m ↔
      D.Available r (D.restrict (r.self_le_sub n) y) (n*m) := by
  exact (D.restrict_range_iff (r.self_le_sub n) ((r.sub n).self_le_sub m) y).symm.trans
    (D.range_congr _ _ _ (r.sub_sub n m))

/-- An included element is available at its original diagram. -/
theorem available_restrict (r : Diagram M I) (n : M) (y : D.Obj (r.sub n)) :
    D.Available r (D.restrict (r.self_le_sub n) y) n := ⟨y,rfl⟩

/-- The availability ideal at a contracted diagram is exactly the contracted
availability ideal. -/
theorem availability_sub (r : Diagram M I) (a n c : M) (hnc : n*c = a)
    (y : D.Obj (r.sub n)) :
    D.availability (r.sub n) c y =
      (D.availability r a (D.restrict (r.self_le_sub n) y)).contract
        ⟨⟨c,hnc⟩,D.available_restrict r n y⟩ hnc := by
  apply ConeIdeal.ext
  ext x
  change (x ≤ (show LeftDivOrder M from c) ∧ D.Available (r.sub n) y x) ↔
    ((show LeftDivOrder M from n)*x ≤ (show LeftDivOrder M from a) ∧
      D.Available r _ (n*(show M from x)))
  apply and_congr
  · rw [← hnc]
    exact (LeftDivOrder.mul_le_mul_left_iff n x c).symm
  · exact D.available_sub_iff r n x y

/-- Exact fibers, defined using the proved availability ideal rather than
an arbitrarily assigned classification. -/
def Fiber (r : Diagram M I) (a : M) (U : ConeIdeal (show LeftDivOrder M from a)) :=
  {x : D.Obj r // D.availability r a x = U}

/-- The inclusion map underlying a contraction between exact fibers. -/
def fiberRestrict (hj : HasConditionalJoins (LeftDivOrder M))
    (r : Diagram M I) (a n c : M) (U : ConeIdeal (show LeftDivOrder M from a))
    (hn : (show LeftDivOrder M from n) ∈ U.carrier) (hnc : n*c = a)
    (y : D.Fiber (r.sub n) c (U.contract hn hnc)) : D.Fiber r a U :=
  ⟨D.restrict (r.self_le_sub n) y.val,by
    apply ConeIdeal.eq_of_contract_eq hj _ hn hnc
    exact (D.availability_sub r a n c hnc y.val).symm.trans y.property⟩

/-- Source contraction-identification lemma, common to label and symbolic
systems. Bijectivity uses the full-ideal reconstruction by joins. -/
theorem fiberRestrict_bijective (hj : HasConditionalJoins (LeftDivOrder M))
    (r : Diagram M I) (a n c : M) (U : ConeIdeal (show LeftDivOrder M from a))
    (hn : (show LeftDivOrder M from n) ∈ U.carrier) (hnc : n*c = a) :
    Function.Bijective (D.fiberRestrict hj r a n c U hn hnc) := by
  constructor
  · intro y z he
    apply Subtype.ext
    exact D.injective (r.self_le_sub n) (congrArg Subtype.val he)
  · intro x
    have hnx : n ∈ (D.availability r a x.val).carrier := by rw [x.property]; exact hn
    obtain ⟨y,hy⟩ := hnx.2
    refine ⟨⟨y,?_⟩,Subtype.ext hy⟩
    rw [D.availability_sub r a n c hnc y]
    apply ConeIdeal.ext
    ext z
    change (show LeftDivOrder M from n)*z ∈
      (D.availability r a (D.restrict (r.self_le_sub n) y)).carrier ↔ _
    rw [hy,x.property]
    rfl

/-- A canonical fiber equivalence. Its forward map is inclusion, not an
independent chosen bijection. -/
noncomputable def fiberEquiv (hj : HasConditionalJoins (LeftDivOrder M))
    (r : Diagram M I) (a n c : M) (U : ConeIdeal (show LeftDivOrder M from a))
    (hn : (show LeftDivOrder M from n) ∈ U.carrier) (hnc : n*c = a) :
    D.Fiber (r.sub n) c (U.contract hn hnc) ≃ D.Fiber r a U :=
  Equiv.ofBijective _ (D.fiberRestrict_bijective hj r a n c U hn hnc)

end PartitionConsistency.LocalDiagramSystem.System

end OAI
