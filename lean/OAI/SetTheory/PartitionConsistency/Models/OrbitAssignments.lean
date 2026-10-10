import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.StableSelectors

namespace OAI

/-! ## CorrectedDensity -/

/-! Exactness and the two density directions for the coset-corrected
assignment. Selector density and ordinal counts are discharged for the
concrete system in the following construction. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.componentStabilizer hj v
local notation "K" => C.tailFixer hj

/-- A corrected assignment has the actual permanent ideal at its vertex. -/
theorem corrected_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : LocalName hμ c w.diagram}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    StableAt hμ c hcard hsize hmerger E d w τ.name := by
  obtain ⟨g,hg,h⟩ := h
  have hp := preliminary_stable hμ c hcard hsize hmerger hj E hE C
    (d := g⁻¹ • d) (w := g.val⁻¹ • w) (j := g⁻¹ • j)
    (τ := τ.transport hμ g.val.val⁻¹) h
  have hs : StableAt hμ c hcard hsize hmerger E (g⁻¹ • d) (g.val⁻¹ • w) (g⁻¹ • τ.name) :=
    ⟨τ.transport hμ g.val.val⁻¹,rfl,hp.1,hp.2⟩
  exact (stableAt_permute_iff hμ c hcard hsize hmerger E hE g.val⁻¹ d w τ.name).mp hs

variable {hμ c hcard hsize hmerger hj E hE C}

omit [LinearOrder κ] [WellFoundedLT κ] in
theorem ordinalCount_mono {d e : CohenForcing.Condition I κ} (hed : e ≤ d)
    (h : OrdinalCount hμ c hcard hsize hmerger hj E hE C d) :
    OrdinalCount hμ c hcard hsize hmerger hj E hE C e :=
  fun f hfe θ hθ => h f (hfe.trans hed) θ hθ

variable (hμ c hcard hsize hmerger hj E hE C)

omit [Infinite M] [Infinite I] in
private theorem selected_exists (d : CohenForcing.Condition I κ)
    (hd : (C.tailData hj).Good d) :
    ∃ g : G, (C.tailData hj).Selected d (g : G ⧸ K) := by
  let g := ((C.tailData hj).conditionSelector d hd).out
  exact ⟨g,hd,(QuotientGroup.out_eq' _).symm⟩

/-- Dense totality, with both the ordinal computations and the selector
made at the actual moved condition. -/
theorem corrected_total (d : CohenForcing.Condition I κ)
    (hsel : ∀ d : CohenForcing.Condition I κ, ∃ e, e ≤ d ∧ (C.tailData hj).Good e)
    (hcount : ∀ g : G, OrdinalCount hμ c hcard hsize hmerger hj E hE C (g⁻¹ • d))
    (w : Vertex q) (hw : Vertex.Common v w) (j : labelFiberSet v) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      Corrected hμ c hcard hsize hmerger hj E hE C e w j τ.name := by
  obtain ⟨e,hed,he⟩ := hsel d
  obtain ⟨g,hg⟩ := selected_exists hj C e he
  have hged : g⁻¹ • e ≤ g⁻¹ • d :=
    (CohenForcing.Condition.permuteOrderIso g.val.val⁻¹).monotone hed
  obtain ⟨f,hfe,τ,hτ⟩ := preliminary_total hμ c hcard hsize hmerger hj E hE C (g⁻¹ • e)
    (ordinalCount_mono hged (hcount g)) (g⁻¹ • w) (Vertex.common_moved hj v g⁻¹ hw) (g⁻¹ • j)
  have hgf : g • f ≤ e := by
    have h := (CohenForcing.Condition.permuteOrderIso g.val.val).monotone hfe
    change g • f ≤ g • (g⁻¹ • e) at h
    simpa only [smul_inv_smul] using h
  let σ : LocalName hμ c w.diagram := (τ.transport hμ g.val.val).rebase hμ c
    (by
      change (g.val • (g.val⁻¹ • w)).diagram = w.diagram
      exact congrArg Vertex.diagram (smul_inv_smul g.val w))
  refine ⟨g • f,hgf.trans hed,σ,?_⟩
  apply (corrected_selected hμ c hcard hsize hmerger hj E hE C g (hg.mono _ hgf)).mpr
  change Preliminary hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • (g • f)) (g⁻¹ • w) (g⁻¹ • j) (g⁻¹ • (g • τ.name))
  simpa only [inv_smul_smul] using hτ

/-- Dense surjectivity onto every actual, permanently available local class. -/
theorem corrected_onto (d : CohenForcing.Condition I κ)
    (hsel : ∀ d : CohenForcing.Condition I κ, ∃ e, e ≤ d ∧ (C.tailData hj).Good e)
    (hcount : ∀ g : G, OrdinalCount hμ c hcard hsize hmerger hj E hE C (g⁻¹ • d))
    (w : Vertex q) (hw : Vertex.Common v w) (τ : (S).Name)
    (hs : StableAt hμ c hcard hsize hmerger E d w τ) :
    ∃ e, e ≤ d ∧ ∃ j : labelFiberSet v,
      Corrected hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨e,hed,he⟩ := hsel d
  obtain ⟨g,hg⟩ := selected_exists hj C e he
  obtain ⟨ρ,hρ,hel,hstable⟩ :=
    stableAt_permute hμ c hcard hsize hmerger E hE g.val⁻¹ d w τ hs
  have hged : g⁻¹ • e ≤ g⁻¹ • d :=
    (CohenForcing.Condition.permuteOrderIso g.val.val⁻¹).monotone hed
  have hhel : (S).Forces ![ρ.name,labelSet hμ c,E]
      ((g⁻¹ • e,(g⁻¹ • w).diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2) := by
    rw [hρ]
    exact (S).atomic.forceFormula_mono (WithTop.coe_le_coe.mpr
      (show (g⁻¹ • e,(g⁻¹ • w).diagram) ≤ (g⁻¹ • d,(g⁻¹ • w).diagram) from ⟨hged,le_rfl⟩)) hel
  obtain ⟨a,ha,hl⟩ := exists_linked_working_of_stable hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • e) (g⁻¹ • w) (Vertex.common_moved hj v g⁻¹ hw) ρ hhel
    (fun f hfe => hstable f (hfe.trans hged))
  rw [hρ] at hl
  obtain ⟨f,hfe,j,hj⟩ := preliminary_onto hμ c hcard hsize hmerger hj E hE C (g⁻¹ • e)
    (ordinalCount_mono hged (hcount g)) (g⁻¹ • w) (g⁻¹ • τ) a ha hl
  have hgf : g • f ≤ e := by
    have h := (CohenForcing.Condition.permuteOrderIso g.val.val).monotone hfe
    change g • f ≤ g • (g⁻¹ • e) at h
    simpa only [smul_inv_smul] using h
  refine ⟨g • f,hgf.trans hed,g • j,?_⟩
  apply (corrected_selected hμ c hcard hsize hmerger _ E hE C g (hg.mono _ hgf)).mpr
  simpa only [inv_smul_smul] using hj

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## ComponentOrbit -/

/-! Orbits of actual contraction components, under the group fixing the
root diagram. Representatives and chains are chosen only once per orbit. -/
namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section
variable (hj : HasConditionalJoins (LeftDivOrder M))

def OrbitRel (_hj : HasConditionalJoins (LeftDivOrder M)) (v w : Vertex q) : Prop := ∃ g : RootGroup q, Common v (g • w)

namespace OrbitRel
variable {hj}
theorem refl (v : Vertex q) : OrbitRel hj v v := ⟨1,by simpa using Common.refl v⟩
theorem symm {v w : Vertex q} (h : OrbitRel hj v w) : OrbitRel hj w v := by
  obtain ⟨g,hg⟩ := h
  exact ⟨g⁻¹,by simpa only [inv_smul_smul] using (hg.move g⁻¹).symm⟩
theorem trans {v w z : Vertex q} (h : OrbitRel hj v w) (h' : OrbitRel hj w z) :
    OrbitRel hj v z := by
  obtain ⟨g,hg⟩ := h
  obtain ⟨s,hs⟩ := h'
  exact ⟨g*s,by simpa only [mul_smul] using hg.trans hj (hs.move g)⟩
end OrbitRel

def orbitSetoid : Setoid (Vertex q) where
  r := OrbitRel hj
  iseqv := ⟨OrbitRel.refl,OrbitRel.symm,OrbitRel.trans⟩

abbrev ComponentOrbit := Quotient (orbitSetoid (q := q) hj)

def orbit (v : Vertex q) : ComponentOrbit (q := q) hj := Quotient.mk _ v

def orbitRep (a : ComponentOrbit (q := q) hj) : Vertex q := a.out

theorem orbit_rep (a : ComponentOrbit (q := q) hj) : orbit hj (orbitRep hj a) = a :=
  Quotient.out_eq a

theorem orbit_eq {v w : Vertex q} : orbit hj v = orbit hj w ↔ OrbitRel hj v w :=
  Quotient.eq

theorem orbit_common {v w : Vertex q} (h : Common v w) : orbit hj v = orbit hj w :=
  Quotient.sound ⟨1,by simpa only [one_smul] using h⟩

theorem orbit_move (g : RootGroup q) (w : Vertex q) : orbit hj (g • w) = orbit hj w :=
  Quotient.sound ⟨g,Common.refl (g • w)⟩

def orbitChain (H : HeightCost (LeftDivOrder M)) (a : ComponentOrbit (q := q) hj) :
    Chain (orbitRep hj a) := Classical.choice (exists_chain hj H _)

end
end PartitionConsistency.LocalDiagramSystem.Vertex


/-! ## AllComponent -/

/-! Transport of the corrected assignment to an entire orbit of components.
The only ambiguity is the actual component stabilizer, whose covariance has
already been proved with the inverse-moved Cohen condition. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.RootGroup q

def OrbitAssignment (d : CohenForcing.Condition I κ) (w : Vertex q) (j : I) (τ : (S).Name) : Prop :=
  ∃ (g : G) (k : labelFiberSet v), g • k.val = j ∧
    Corrected hμ c hcard hsize hmerger hj E hE C (g⁻¹ • d) (g⁻¹ • w) k (g⁻¹ • τ)

variable {hμ c hcard hsize hmerger hj E hE C}

theorem orbitAssignment_orbit {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Vertex.OrbitRel hj v w := by
  obtain ⟨g,k,_,h⟩ := h
  exact ⟨g⁻¹,corrected_common h⟩

theorem orbitAssignment_label {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) : j ∈ labelFiberSet w := by
  obtain ⟨g,k,rfl,h⟩ := h
  have hk : k.val ∈ labelFiberSet (g⁻¹ • w) := by
    rw [← labelFiberSet_common hj (corrected_common h)]
    exact k.property
  have hh := (labelFiberSet_permute g (g⁻¹ • w) k.val).mp hk
  change g.val k.val ∈ labelFiberSet w
  simpa only [smul_inv_smul] using hh

theorem orbitAssignment_mono {d e : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (hed : e ≤ d) (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨g,k,hk,h⟩ := h
  exact ⟨g,k,hk,corrected_mono ((CohenForcing.Condition.permuteOrderIso g.val⁻¹).monotone hed) h⟩

variable (hμ c hcard hsize hmerger hj E hE C)

theorem orbitAssignment_permute (s : G) {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : (S).Name} (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C (s • d) (s • w) (s • j) (s • τ) := by
  obtain ⟨g,k,hk,h⟩ := h
  refine ⟨s*g,k,?_,?_⟩
  · rw [mul_smul,hk]
  · simpa only [mul_inv_rev,mul_smul,inv_smul_smul] using h

theorem orbitAssignment_congr {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ σ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ)
    (he : (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j σ := by
  obtain ⟨g,k,hk,h⟩ := h
  exact ⟨g,k,hk,corrected_congr h ((root_eq_symmetry hμ g⁻¹ d w τ σ).mpr he)⟩

theorem orbitAssignment_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d z j τ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ := by
  obtain ⟨g,k,hk,h⟩ := h
  exact ⟨g,k,hk,corrected_restrict hμ c hcard hsize hmerger hj E hE C (f.move g⁻¹) h⟩

theorem orbitAssignment_descend {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : I} {τ : LocalName hμ c z.diagram}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C d z j τ.name := by
  obtain ⟨g,k,hk,h⟩ := h
  exact ⟨g,k,hk,corrected_descend hμ c hcard hsize hmerger hj E hE C (f.move g⁻¹)
    (τ := τ.transport hμ g.val⁻¹) h⟩

theorem orbitAssignment_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    StableAt hμ c hcard hsize hmerger E d w τ.name := by
  obtain ⟨g,k,_,h⟩ := h
  have hs := corrected_stable hμ c hcard hsize hmerger hj E hE C
    (d := g⁻¹ • d) (w := g⁻¹ • w) (τ := τ.transport hμ g.val⁻¹) h
  exact (stableAt_permute_iff hμ c hcard hsize hmerger E hE g⁻¹ d w τ.name).mp hs

omit [Infinite M] [Infinite I] in
/-- Two transports to the same component differ by the full stabilizer. -/
theorem component_difference (g s : G) (w : Vertex q)
    (hg : Vertex.Common v (g⁻¹ • w)) (hs : Vertex.Common v (s⁻¹ • w)) :
    g⁻¹*s ∈ Vertex.componentStabilizer hj v := by
  have hh : Vertex.Common ((g⁻¹*s) • v) (g⁻¹ • w) := by
    simpa only [mul_smul,smul_inv_smul] using hs.move (g⁻¹*s)
  exact hg.trans hj hh.symm

/-- The transport is unambiguous even when its two witnesses use unrelated
coordinate permutations. Both injectivity and single-valuedness are retained. -/
theorem orbitAssignment_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q} {j j' : I} {τ σ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ)
    (h' : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j' σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = j' := by
  obtain ⟨g,k,hk,h⟩ := h
  obtain ⟨s,l,hl,h'⟩ := h'
  let a : Vertex.componentStabilizer hj v :=
    ⟨g⁻¹*s,component_difference hj g s w (corrected_common h) (corrected_common h')⟩
  have hm := corrected_permute hμ c hcard hsize hmerger hj E hE C a
    (s⁻¹ • d) (s⁻¹ • w) l (s⁻¹ • σ) h'
  have hm' : Corrected hμ c hcard hsize hmerger hj E hE C
      (g⁻¹ • d) (g⁻¹ • w) (a • l) (g⁻¹ • σ) := by
    change Corrected hμ c hcard hsize hmerger hj E hE C
      ((g⁻¹*s) • (s⁻¹ • d)) ((g⁻¹*s) • (s⁻¹ • w)) (a • l) ((g⁻¹*s) • (s⁻¹ • σ)) at hm
    simpa only [mul_smul,smul_inv_smul] using hm
  rw [← root_eq_symmetry hμ g⁻¹ d w τ σ,corrected_eq_iff hμ c hcard hsize hmerger hj E hE C h hm']
  constructor
  · intro he
    have hv := congrArg (fun x : labelFiberSet v => g • x.val) he
    change g • k.val = g • ((g⁻¹*s) • l.val) at hv
    simpa only [mul_smul,smul_inv_smul,hk,hl] using hv
  · intro he
    apply Subtype.ext
    change k.val = (g⁻¹*s) • l.val
    apply (MulAction.injective g)
    simpa only [mul_smul,smul_inv_smul,hk,hl] using he

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## OrbitDensity -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.RootGroup q

/-- Totality after transporting to any component in the orbit. -/
theorem orbitAssignment_total_at (d : CohenForcing.Condition I κ) (w : Vertex q) (g : G)
    (hw : Vertex.Common v (g⁻¹ • w))
    (hsel : ∀ e : CohenForcing.Condition I κ, ∃ f, f ≤ e ∧ (C.tailData hj).Good f)
    (hcount : ∀ a : Vertex.componentStabilizer hj v,
      OrdinalCount hμ c hcard hsize hmerger hj E hE C (a⁻¹ • (g⁻¹ • d)))
    (j : I) (hjw : j ∈ labelFiberSet w) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      OrbitAssignment hμ c hcard hsize hmerger hj E hE C e w j τ.name := by
  have hk : (g⁻¹ • j) ∈ labelFiberSet v := by
    rw [labelFiberSet_common hj hw]
    exact (labelFiberSet_permute g⁻¹ w j).mp hjw
  let k : labelFiberSet v := ⟨g⁻¹ • j,hk⟩
  obtain ⟨f,hfd,τ,hτ⟩ := corrected_total hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • d) hsel hcount (g⁻¹ • w) hw k
  have hgf : g • f ≤ d := by
    have hh := (CohenForcing.Condition.permuteOrderIso g.val).monotone hfd
    change g • f ≤ g • (g⁻¹ • d) at hh
    simpa only [smul_inv_smul] using hh
  let σ : LocalName hμ c w.diagram := (τ.transport hμ g.val).rebase hμ c
    (by
      change (g • (g⁻¹ • w)).diagram = w.diagram
      exact congrArg Vertex.diagram (smul_inv_smul g w))
  refine ⟨g • f,hgf,σ,g,k,by exact smul_inv_smul g j,?_⟩
  change Corrected hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • (g • f)) (g⁻¹ • w) k (g⁻¹ • (g • τ.name))
  simpa only [inv_smul_smul] using hτ

/-- Surjectivity after orbital transport, still only onto an actual local
class with its permanent availability ideal. -/
theorem orbitAssignment_onto_at (d : CohenForcing.Condition I κ) (w : Vertex q) (g : G)
    (hw : Vertex.Common v (g⁻¹ • w))
    (hsel : ∀ e : CohenForcing.Condition I κ, ∃ f, f ≤ e ∧ (C.tailData hj).Good f)
    (hcount : ∀ a : Vertex.componentStabilizer hj v,
      OrdinalCount hμ c hcard hsize hmerger hj E hE C (a⁻¹ • (g⁻¹ • d)))
    (τ : (S).Name) (hs : StableAt hμ c hcard hsize hmerger E d w τ) :
    ∃ e, e ≤ d ∧ ∃ j : I,
      OrbitAssignment hμ c hcard hsize hmerger hj E hE C e w j τ := by
  have hs' := stableAt_permute hμ c hcard hsize hmerger E hE g⁻¹ d w τ hs
  obtain ⟨f,hfd,k,hk⟩ := corrected_onto hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • d) hsel hcount (g⁻¹ • w) hw (g⁻¹ • τ) hs'
  have hgf : g • f ≤ d := by
    have hh := (CohenForcing.Condition.permuteOrderIso g.val).monotone hfd
    change g • f ≤ g • (g⁻¹ • d) at hh
    simpa only [smul_inv_smul] using hh
  refine ⟨g • f,hgf,g • k.val,g,k,rfl,?_⟩
  simpa only [inv_smul_smul] using hk

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## GlobalAssignment -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

/-- The assignment on all vertices, choosing a single chain per orbit of
actual components. Its witnesses are local names and literal label indices. -/
def Assigned (d : CohenForcing.Condition I κ) (w : Vertex q) (j : I) (τ : (S).Name) : Prop :=
  ∃ a : Vertex.ComponentOrbit (q := q) hj,
    OrbitAssignment hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) d w j τ

variable {hμ c hcard hsize hmerger hj H E hE}

theorem assigned_label {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ) : j ∈ labelFiberSet w := by
  obtain ⟨a,ha⟩ := h
  exact orbitAssignment_label ha

theorem assigned_mono {d e : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (he : e ≤ d) (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ) :
    Assigned hμ c hcard hsize hmerger hj H E hE e w j τ := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_mono he ha⟩

variable (hμ c hcard hsize hmerger hj H E hE)

theorem assigned_permute (g : Vertex.RootGroup q) {d : CohenForcing.Condition I κ}
    {w : Vertex q} {j : I} {τ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ) :
    Assigned hμ c hcard hsize hmerger hj H E hE (g • d) (g • w) (g • j) (g • τ) := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_permute hμ c hcard hsize hmerger hj E hE _ g ha⟩

theorem assigned_congr {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ σ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ)
    (he : (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ) :
    Assigned hμ c hcard hsize hmerger hj H E hE d w j σ := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_congr hμ c hcard hsize hmerger hj E hE _ ha he⟩

theorem assigned_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : I} {τ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d z j τ) :
    Assigned hμ c hcard hsize hmerger hj H E hE d w j τ := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_restrict hμ c hcard hsize hmerger hj E hE _ f ha⟩

theorem assigned_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name) :
    StableAt hμ c hcard hsize hmerger E d w τ.name := by
  obtain ⟨a,ha⟩ := h
  exact orbitAssignment_stable hμ c hcard hsize hmerger hj E hE _ ha

private theorem orbitAssignment_index (a : Vertex.ComponentOrbit (q := q) hj)
    {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) d w j τ) :
    a = Vertex.orbit hj w := by
  rw [← Vertex.orbit_rep hj a,Vertex.orbit_eq]
  exact orbitAssignment_orbit h

theorem assigned_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j k : I} {τ σ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ)
    (h' : Assigned hμ c hcard hsize hmerger hj H E hE d w k σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = k := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  have hab := (orbitAssignment_index hμ c hcard hsize hmerger hj H E hE a ha).trans
    (orbitAssignment_index hμ c hcard hsize hmerger hj H E hE b hb).symm
  subst b
  exact orbitAssignment_eq_iff hμ c hcard hsize hmerger hj E hE _ ha hb

/-- Uniform count and selector hypotheses give totality on every vertex;
there is no orbit omitted from the chosen graph. -/
theorem assigned_total (d : CohenForcing.Condition I κ)
    (hsel : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ e : CohenForcing.Condition I κ,
      ∃ f, f ≤ e ∧ ((Vertex.orbitChain hj H a).tailData hj).Good f)
    (hcount : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ g : Vertex.RootGroup q,
      OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) (g • d))
    (w : Vertex q) (j : I) (hjw : j ∈ labelFiberSet w) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      Assigned hμ c hcard hsize hmerger hj H E hE e w j τ.name := by
  let a := Vertex.orbit hj w
  have hrel : Vertex.OrbitRel hj (Vertex.orbitRep hj a) w :=
    (Vertex.orbit_eq hj).mp (Vertex.orbit_rep hj a)
  obtain ⟨g,hg⟩ := hrel
  obtain ⟨e,hed,τ,hτ⟩ := orbitAssignment_total_at hμ c hcard hsize hmerger hj E hE
    (Vertex.orbitChain hj H a) d w g⁻¹ (by simpa only [inv_inv] using hg) (hsel a)
    (fun s => by
      change OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a)
        (s.val⁻¹ • ((g⁻¹)⁻¹ • d))
      simpa only [mul_smul,inv_inv] using hcount a (s.val⁻¹ * g)) j hjw
  exact ⟨e,hed,τ,a,hτ⟩

theorem assigned_onto (d : CohenForcing.Condition I κ)
    (hsel : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ e : CohenForcing.Condition I κ,
      ∃ f, f ≤ e ∧ ((Vertex.orbitChain hj H a).tailData hj).Good f)
    (hcount : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ g : Vertex.RootGroup q,
      OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) (g • d))
    (w : Vertex q) (τ : (S).Name) (hs : StableAt hμ c hcard hsize hmerger E d w τ) :
    ∃ e, e ≤ d ∧ ∃ j : I, Assigned hμ c hcard hsize hmerger hj H E hE e w j τ := by
  let a := Vertex.orbit hj w
  have hrel : Vertex.OrbitRel hj (Vertex.orbitRep hj a) w :=
    (Vertex.orbit_eq hj).mp (Vertex.orbit_rep hj a)
  obtain ⟨g,hg⟩ := hrel
  obtain ⟨e,hed,j,hj⟩ := orbitAssignment_onto_at hμ c hcard hsize hmerger hj E hE
    (Vertex.orbitChain hj H a) d w g⁻¹ (by simpa only [inv_inv] using hg) (hsel a)
    (fun s => by
      change OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a)
        (s.val⁻¹ • ((g⁻¹)⁻¹ • d))
      simpa only [mul_smul,inv_inv] using hcount a (s.val⁻¹ * g)) τ hs
  exact ⟨e,hed,j,a,hj⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## AssignmentCompatibility -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
noncomputable section

/-- The vertex associated to a literal available label at an extension of q. -/
def labelVertex {q : Diagram M I} (r : Diagram M I) (a : M) (ha : r.sub a = q)
    (j : I) (hj : j ∈ r.range) : Vertex q :=
  ⟨r,a,ha,(labelSystem (M := M)).availability r a ⟨j,hj⟩⟩

theorem labelVertex_mem {q : Diagram M I} (r : Diagram M I) (a : M) (ha : r.sub a = q)
    (j : I) (hj : j ∈ r.range) : j ∈ labelFiberSet (labelVertex r a ha j hj) :=
  ⟨⟨⟨j,hj⟩,rfl⟩,rfl⟩

/-- Enlarging a diagram induces the unique contraction carrying the
exact label fiber back to its original vertex. -/
theorem labelVertex_arrow {q : Diagram M I} (r : Diagram M I) (a : M) (ha : r.sub a = q)
    (w : Vertex q) (hrw : r ≤ w.diagram) (j : I) (hj : j ∈ labelFiberSet w) :
    Nonempty ((labelVertex r a ha j (Diagram.range_antitone hrw (labelFiberSet_subset w hj))).Arrow w) := by
  obtain ⟨x,hx⟩ := hj
  subst j
  obtain ⟨n,hn⟩ := hrw
  have hna : n*w.index = a := by
    apply Diagram.index_unique (r := r)
    rw [← Diagram.sub_sub,hn,w.root,ha]
  refine ⟨⟨n,?_,hn,?_⟩⟩
  · change (show LeftDivOrder M from n) ≤ a ∧ _
    refine ⟨⟨w.index,hna⟩,?_⟩
    rw [label_available_iff,hn]
    exact x.val.property
  · intro t
    have ht := Set.ext_iff.mp (congrArg ConeIdeal.carrier x.property) t
    change t ∈ w.ideal.carrier ↔ _
    rw [← ht]
    change (t ≤ (show LeftDivOrder M from w.index) ∧ _) ↔
      ((show LeftDivOrder M from n)*t ≤ a ∧ _)
    erw [label_available_iff,label_available_iff,← hna,LeftDivOrder.mul_le_mul_left_iff]
    erw [← Diagram.sub_sub,hn]

end
end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

theorem assigned_ideal {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name) :
    forcedAvailability hμ c hcard hsize hmerger d w.diagram w.index τ = w.ideal := by
  obtain ⟨ρ,he,_,hs⟩ := assigned_stable hμ c hcard hsize hmerger hj H E hE h
  have he' : ρ = τ := LocalName.ext he
  subst ρ
  exact hs d le_rfl

/-- Passing to a stronger diagram uses the actual label availability ideal,
so no arbitrary identification between enlarged fibers is made. -/
theorem assigned_at_extension {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name)
    (he : e ≤ d) (r : Diagram M I) (a : M) (ha : r.sub a = q) (hrw : r ≤ w.diagram) :
    Assigned hμ c hcard hsize hmerger hj H E hE e
      (labelVertex r a ha j (Diagram.range_antitone hrw (labelFiberSet_subset w (assigned_label h))))
      j (τ.restrict hrw).name := by
  obtain ⟨f⟩ := labelVertex_arrow r a ha w hrw j (assigned_label h)
  exact assigned_restrict hμ c hcard hsize hmerger hj H E hE f (assigned_mono he h)

/-- Compatible graph entries with the same literal label always have the
same value, even if they were computed at different diagrams and components. -/
theorem assigned_compatible_one {d e f : CohenForcing.Condition I κ} {w z : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram} {σ : LocalName hμ c z.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name)
    (h' : Assigned hμ c hcard hsize hmerger hj H E hE e z j σ.name)
    (hfd : f ≤ d) (hfe : f ≤ e) (r : Diagram M I) (hrw : r ≤ w.diagram) (hrz : r ≤ z.diagram) :
    (S).atomic.EqF ((f,r) : Poset M I κ) τ.name σ.name := by
  obtain ⟨a,ha⟩ := hrw.trans (show w.diagram ≤ q from ⟨w.index,w.root⟩)
  have h₁ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h hfd r a ha hrw
  have h₂ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h' hfe r a ha hrz
  exact (assigned_eq_iff hμ c hcard hsize hmerger hj H E hE h₁ h₂).mpr rfl

/-- Equal values at a common extension have equal permanent availability
ideals, hence lie in one and the same fiber and have equal labels. -/
theorem assigned_compatible_inj {d e f : CohenForcing.Condition I κ} {w z : Vertex q}
    {j k : I} {τ : LocalName hμ c w.diagram} {σ : LocalName hμ c z.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name)
    (h' : Assigned hμ c hcard hsize hmerger hj H E hE e z k σ.name)
    (hfd : f ≤ d) (hfe : f ≤ e) (r : Diagram M I) (hrw : r ≤ w.diagram) (hrz : r ≤ z.diagram)
    (heq : (S).atomic.EqF ((f,r) : Poset M I κ) τ.name σ.name) : j = k := by
  obtain ⟨a,ha⟩ := hrw.trans (show w.diagram ≤ q from ⟨w.index,w.root⟩)
  let w₁ := labelVertex r a ha j (Diagram.range_antitone hrw (labelFiberSet_subset w (assigned_label h)))
  let w₂ := labelVertex r a ha k (Diagram.range_antitone hrz (labelFiberSet_subset z (assigned_label h')))
  have h₁ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h hfd r a ha hrw
  have h₂ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h' hfe r a ha hrz
  have hU : w₁.ideal = w₂.ideal :=
    (assigned_ideal hμ c hcard hsize hmerger hj H E hE (τ := τ.restrict hrw) h₁).symm.trans
      ((forcedAvailability_congr hμ c hcard hsize hmerger f r a (τ.restrict hrw) (σ.restrict hrz) heq).trans
        (assigned_ideal hμ c hcard hsize hmerger hj H E hE (τ := σ.restrict hrz) h₂))
  have hw : w₁ = w₂ := by
    change (⟨r,a,ha,w₁.ideal⟩ : Vertex q) = ⟨r,a,ha,w₂.ideal⟩
    rw [hU]
  change Assigned hμ c hcard hsize hmerger hj H E hE f w₂ k σ.name at h₂
  rw [← hw] at h₂
  exact (assigned_eq_iff hμ c hcard hsize hmerger hj H E hE h₁ h₂).mp heq

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
