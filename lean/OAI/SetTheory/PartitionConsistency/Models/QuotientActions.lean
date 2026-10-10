import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.OrdinalChoice
import OAI.SetTheory.PartitionConsistency.Models.ConcreteSystem

namespace OAI

/-! ## SaturatedFibers -/

namespace PartitionConsistency.MonoidConstruction.Saturation
universe u
open DiagramOrder DiagramForcing LocalDiagramSystem
noncomputable section
variable (M : Object.{u}) (K : Type u) [Nonempty K] [Infinite K]

/-- Reindex the actual saturated probes into independently hit rows. This
uses infinitude of the prescribed multiplicity, not a new saturation step. -/
theorem square_ideal_probes (a b : target M K) (hb : b ≠ 1)
    (U : ConeIdeal (α := LeftDivOrder (target M K)) a) :
    ∃ m : K × K → target M K, Function.Injective m ∧
      (∀ i, m i * b = a * (target M K).e ∧ ¬ m i ∣ a ∧
        (∀ x : target M K, x ∣ a ∧ x ∣ m i ↔ x ∈ U.carrier) ∧
        ∀ x : target M K, x ∣ a → x ∉ U.carrier →
          ∀ z : target M K, x ∣ z ∧ m i ∣ z ↔ a * (target M K).e ∣ z) ∧
      ∀ i j, i ≠ j → ∀ z : target M K,
        m i ∣ z ∧ m j ∣ z ↔ a * (target M K).e ∣ z := by
  have hs : Cardinal.mk (K × K) = Cardinal.mk K := by
    rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.mul_eq_self (Cardinal.aleph0_le_mk K)]
  obtain ⟨h⟩ := Cardinal.eq.mp hs
  obtain ⟨m,hinj,hm,hi⟩ := ideal_probes M K a b hb U
  exact ⟨m ∘ h,hinj.comp h.injective,fun i => hm (h i),
    fun i j hij => hi (h i) (h j) (fun he => hij (h.injective he))⟩

end
end PartitionConsistency.MonoidConstruction.Saturation

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v w
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I)

instance fiberSmall (r : Diagram M I) (a : M) (U : ConeIdeal (show LeftDivOrder M from a))
    [Small.{w} (D.Obj r)] : Small.{w} (D.Fiber r a U) :=
  inferInstanceAs (Small.{w} {x : D.Obj r // D.availability r a x = U})

end PartitionConsistency.LocalDiagramSystem.System

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem MonoidConstruction
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

instance eligibleSystem_obj_small [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) :
    Small.{u} ((eligibleSystem hμ c hcard hsize hmerger F q E hE).Obj r) :=
  inferInstanceAs (Small.{u} {x : LocalQuotient (c := c) hμ F r //
    r ≤ q ∧ Eligible hμ c F r E x})

/-- The entire eligible quotient bounds every exact fiber. The input is
only meeting the explicit, proved dense record sets, not an assumed list
of representatives or an assumed fiber cardinal. -/
theorem classFiber_cardinal_le [Infinite M] [Infinite I]
    (hpower : μ ^ Cardinal.aleph0 = μ) (hcard : Cardinal.mk M ≤ μ)
    (hκ : Cardinal.mk κ ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    {q : Diagram M I} (w : Vertex q)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (hmeets : ∀ (τ : LocalName hμ c w.diagram) (d₀ : CohenForcing.Condition I κ), d₀ ∈ F →
      (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d₀,w.diagram) : Poset M I κ)
        (SetLanguage.isClass 0 1 2) →
      ∃ d, d ∈ F ∧ d ∈ classRepresentationDenseSet hμ c w.diagram E τ d₀) :
    Cardinal.mk (Shrink.{u} ((eligibleSystem hμ c hcard hsize hmerger F q E hE).vertexFiber w)) ≤ μ := by
  let D := eligibleSystem hμ c hcard hsize hmerger F q E hE
  let f : D.vertexFiber w → EligibleClasses hμ c F w.diagram E :=
    fun x => ⟨x.val.val,x.val.property.2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : EligibleClasses hμ c F w.diagram E => z.val) h
  have hbound : Cardinal.mk (Shrink.{u} (D.vertexFiber w)) ≤
      Cardinal.mk (Shrink.{u} (EligibleClasses hμ c F w.diagram E)) :=
    Cardinal.mk_le_of_injective ((equivShrink _).injective.comp
      (hinj.comp (equivShrink _).symm.injective))
  exact hbound.trans (eligibleClasses_cardinal_le hμ c hpower hcard hκ hsize hmerger F
    w.diagram E (supported_mono hμ ⟨w.index,w.root⟩ E hE) hmeets)

end
end PartitionConsistency.ProductForcing

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem
noncomputable section

/-- For the concrete executed saturation, an outside witness supplies dense
requirements for the exact lower class-fiber bound. All final ideals at all
vertices are covered; no algebraic profile or exact-intersection premise is
left for the extension argument to supply. -/
theorem classFiber_dense_lower {q : Diagram T I} (w : Vertex q) (b : T) (hb : b ≠ 1)
    (E : S.Name) (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e))) :
    ∃ D : K → Set (CohenForcing.Condition I κ), (∀ i, Dense (D i)) ∧
      ∀ F : GenericFilter (CohenForcing.Condition I κ), d ∈ F →
        (∀ i, ∃ a, a ∈ F ∧ a ∈ D i) →
        Nonempty (K ↪ (eligibleSystem aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers F q E
          (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE)).vertexFiber w) := by
  obtain ⟨m,_,hm,hi⟩ := Saturation.square_ideal_probes Base.object K w.index b hb w.ideal
  exact ProductForcing.classFiber_dense_lower aleph0_le_μ (posetCode κ) cardinal_T.le size_lt
    finiteMergers w T.e b m (fun i => (hm i).1) (fun i => (hm i).2.2.1)
    (fun i => (hm i).2.2.2) hi E hE t ht d hd j hj hout

private theorem concreteEligibleFiberSmall
    (F : GenericFilter (CohenForcing.Condition I κ)) {q : Diagram T I} (w : Vertex q)
    (E : S.Name) (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) :
    Small.{0} ((eligibleSystem aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers F q E
      hE).vertexFiber w) := by
  let D := eligibleSystem aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers F q E hE
  let _ : Small.{0} (D.Obj w.diagram) :=
    eligibleSystem_obj_small aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers F q
      w.diagram E hE
  exact LocalDiagramSystem.System.fiberSmall D w.diagram w.index w.ideal

/-- The exact-fiber theorem for the concrete system, with explicitly
identified ordinary Cohen requirements. No genericity or existence of an
intermediate ordinary extension is claimed by this statement. -/
theorem classFiber_dense_exact {q : Diagram T I} (w : Vertex q) (b : T) (hb : b ≠ 1)
    (E : S.Name) (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e))) :
    ∃ D : K → Set (CohenForcing.Condition I κ), (∀ i, Dense (D i)) ∧
      ∀ F : GenericFilter (CohenForcing.Condition I κ), d ∈ F →
        (∀ i, ∃ a, a ∈ F ∧ a ∈ D i) →
        (∀ (τ : LocalName aleph0_le_μ (posetCode κ) w.diagram) (d₀ : CohenForcing.Condition I κ), d₀ ∈ F →
          S.Forces ![τ.name,labelSet aleph0_le_μ (posetCode κ),E] ((d₀,w.diagram) : P)
            (SetLanguage.isClass 0 1 2) →
          ∃ a, a ∈ F ∧ a ∈ classRepresentationDenseSet aleph0_le_μ (posetCode κ) w.diagram E τ d₀) →
        Cardinal.mk (@Shrink.{0} ((eligibleSystem aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers F q E
          (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE)).vertexFiber w)
          (concreteEligibleFiberSmall F w E
            (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE))) = μ := by
  obtain ⟨D,hD,hits⟩ := classFiber_dense_lower w b hb E hE t ht d hd j hj hout
  refine ⟨D,hD,fun F hF hmeets hrecords => ?_⟩
  let _ := concreteEligibleFiberSmall F w E
    (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE)
  apply le_antisymm
  · exact ProductForcing.classFiber_cardinal_le aleph0_le_μ (posetCode κ) μ_countable_power
      cardinal_T.le (cardinal_κ ▸ aleph_one_le_μ) size_lt finiteMergers F w E
      (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) hrecords
  · obtain ⟨f⟩ := hits F hF hmeets
    exact cardinal_K.symm.trans_le
      (Cardinal.mk_le_of_injective ((equivShrink _).injective.comp f.injective))

end
end PartitionConsistency.ConcreteSystem


/-! ## Preliminary -/

/-! A preliminary assignment on the genuine symbolic component with tail
covariance. Exact cardinality at an intermediate filter is an explicit
input here; the issued dense requirements needed to obtain it are in
`SaturatedFibersWork`. No existence of a filter generic over every ambient
set is assumed or asserted. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

instance eligibleSystem_glued_small (F : GenericFilter (CohenForcing.Condition I κ)) :
    Small.{u} ((D[F]).Glued hj v) :=
  small_of_surjective ((D[F]).toGlued_surjective hj v v (Vertex.Common.refl v))

namespace ChainCode

/-- The order bound is the order type of the one fixed ground-code
wellordering, computed on a small copy of the code set. -/
def codeOrderBound : Ordinal.{u} :=
  Ordinal.type (OrderAssignment.smallRel.{u} (WellOrderingRel (α := ChainCode hμ c C)))

/-- The least-code ordering is induced on a subset of the code set, so its
order type cannot exceed the chosen ground bound. -/
theorem orderType_le (F : GenericFilter (CohenForcing.Condition I κ)) :
    Ordinal.type (OrderAssignment.smallRel.{u} (LT hμ c hcard hsize hmerger hj E hE C F)) ≤
      codeOrderBound hμ c C := by
  let e : LT hμ c hcard hsize hmerger hj E hE C F ↪r
      WellOrderingRel (α := ChainCode hμ c C) := {
    toFun := leastCode hμ c hcard hsize hmerger hj E hE C F
    inj' := leastCode_injective hμ c hcard hsize hmerger hj E hE C F
    map_rel_iff' := Iff.rfl }
  exact OrderAssignment.type_smallRel_le e

/-- This is a bounded table chosen just once for the component and its
chain; in particular it has no filter argument. -/
def componentTable : OrderAssignment.Table (labelFiberSet v) (codeOrderBound hμ c C) :=
  OrderAssignment.chooseTable _ _

/-- The preliminary bijection uses the actual least-code order and the
one fixed table. The displayed cardinal equality is precisely the point
at which the exact-fiber theorem is used. -/
def preliminary (F : GenericFilter (CohenForcing.Condition I κ))
    (hc : Cardinal.mk (Shrink.{u} ((D[F]).Glued hj v)) = Cardinal.mk (labelFiberSet v)) :
    labelFiberSet v ≃ (D[F]).Glued hj v :=
  OrderAssignment.smallAssignment (componentTable hμ c C)
    (LT hμ c hcard hsize hmerger hj E hE C F)
    (orderType_le hμ c hcard hsize hmerger hj E hE C F) hc

/-- Literal covariance of the preliminary assignment between F and kF.
The label is unchanged, as every member of the tail fixer fixes all the
labels in this fiber. The two cardinal-equality proofs are immaterial. -/
theorem preliminary_covariance (F : GenericFilter (CohenForcing.Condition I κ))
    (k : C.tailFixer hj)
    (hc : Cardinal.mk (Shrink.{u} ((D[F]).Glued hj v)) = Cardinal.mk (labelFiberSet v))
    (hc' : Cardinal.mk (Shrink.{u}
      ((D[F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)]).Glued hj v)) =
        Cardinal.mk (labelFiberSet v)) (j : labelFiberSet v) :
    preliminary hμ c hcard hsize hmerger hj E hE C
        (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) hc' j =
      transport hμ c hcard hsize hmerger hj E hE F k.val
        (preliminary hμ c hcard hsize hmerger hj E hE C F hc j) :=
  (OrderAssignment.smallAssignment_natural (componentTable hμ c C)
    _ hc _ hc' (leastCodeOrderIso hμ c hcard hsize hmerger hj E hE C F k) j).symm

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## ComponentAction -/

/-! The actual symbolic fibers carry transport between moved Cohen filters.
On the total space this is a genuine group action. The individual interpreted
universes are not being treated as if they carried this action internally. -/
namespace PartitionConsistency.ForcingQuotient
universe u
open CohenForcing
variable {I κ : Type u}

instance : MulAction (Equiv.Perm I) (GenericFilter (Condition I κ)) where
  smul π F := F.move (Condition.permuteOrderIso π)
  one_smul F := by
    ext p
    change (OrderDual.ofDual p).permute ((1 : Equiv.Perm I)⁻¹) ∈ F ↔ p ∈ F
    rw [inv_one,Condition.permute_one]
    rfl
  mul_smul π σ F := by
    ext p
    change (OrderDual.ofDual p).permute ((π*σ)⁻¹) ∈ F ↔
      ((OrderDual.ofDual p).permute π⁻¹).permute σ⁻¹ ∈ F
    rw [mul_inv_rev,Condition.permute_mul]

@[simp] theorem smul_filter (π : Equiv.Perm I) (F : GenericFilter (Condition I κ)) :
    π • F = F.move (Condition.permuteOrderIso π) := rfl

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramForcing DiagramOrder
noncomputable section
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- Coordinate transport for literal label fibers. -/
def labelTransport (π : Equiv.Perm I) : ReindexIso (labelSystem (M := M)) labelSystem π where
  app r := π.subtypeEquiv (fun j => by
    constructor
    · rintro ⟨m,hm⟩
      exact ⟨m,congrArg π hm⟩
    · rintro ⟨m,hm⟩
      exact ⟨m,π.injective hm⟩)
  natural _ _ := rfl

@[simp] theorem labelTransport_fiber_val {q : Diagram M I} (g : Vertex.RootGroup q)
    (v : Vertex q) (x : (labelSystem (M := M)).vertexFiber v) :
    ((labelTransport g.val).fiberEquiv g v x).val.val = g.val x.val.val := rfl

theorem labelFiberSet_permute {q : Diagram M I} (g : Vertex.RootGroup q)
    (v : Vertex q) (j : I) : j ∈ labelFiberSet v ↔ g.val j ∈ labelFiberSet (g • v) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(labelTransport g.val).fiberEquiv g v x,rfl⟩
  · rintro ⟨y,hy⟩
    obtain ⟨x,rfl⟩ := ((labelTransport g.val).fiberEquiv g v).surjective y
    exact ⟨x,g.val.injective hy⟩

namespace Vertex
variable {q : Diagram M I} (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q)

/-- The stabilizer permutes the actual common subset of label indices. -/
instance labelFiberAction : MulAction (componentStabilizer hj v) (labelFiberSet v) where
  smul g j := ⟨g.val.val j.val,by
    exact (labelFiberSet_common hj g.property).symm.subset
      ((labelFiberSet_permute g.val v j.val).mp j.property)⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

@[simp] theorem smul_labelFiber_val (g : componentStabilizer hj v) (j : labelFiberSet v) :
    (g • j).val = g.val.val j.val := rfl

theorem Chain.tailFixer_fixes_label (C : Chain v) (k : C.tailFixer hj) (j : labelFiberSet v) :
    k.val • j = j :=
  Subtype.ext (C.tailFixer_fixes_labels hj k j.val j.property)

end Vertex
end
end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable (v : Vertex q)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- The total symbolic component over all ordinary Cohen filters. There is
no assertion here that any particular such filter is a ground generic. -/
def Total := Σ F : GenericFilter (CohenForcing.Condition I κ), (D[F]).Glued hj v

/-- Representation in the total space, retaining its actual filter. -/
def TotalAt (w : Vertex q) (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (x : Total hμ c hcard hsize hmerger hj E hE v) : Prop :=
  At hμ c hcard hsize hmerger hj E hE x.1 w τ x.2

variable {hμ c hcard hsize hmerger hj E hE v}

theorem total_eq_of_representation {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name}
    {x y : Total hμ c hcard hsize hmerger hj E hE v}
    (hF : x.1 = y.1) (hx : TotalAt hμ c hcard hsize hmerger hj E hE v w τ x)
    (hy : TotalAt hμ c hcard hsize hmerger hj E hE v w τ y) : x = y := by
  obtain ⟨F,x⟩ := x
  obtain ⟨F',y⟩ := y
  dsimp only at hF
  subst F'
  exact congrArg (Sigma.mk F) (at_unique hx hy)

theorem total_has_representation (x : Total hμ c hcard hsize hmerger hj E hE v) :
    ∃ τ, TotalAt hμ c hcard hsize hmerger hj E hE v v τ x := by
  obtain ⟨y,hy⟩ := (D[x.1]).toGlued_surjective hj v v (Vertex.Common.refl v) x.2
  obtain ⟨σ,hσ⟩ := Quotient.mk'_surjective
    (s := localSetoid (c := c) hμ x.1 v.diagram) y.val.val
  exact ⟨σ.name,Vertex.Common.refl v,y,σ,rfl,hσ,hy⟩

variable (hμ c hcard hsize hmerger hj E hE v)

/-- A lift of transport to the total space, before verifying the action laws. -/
def totalMove (g : Vertex.componentStabilizer hj v)
    (x : Total hμ c hcard hsize hmerger hj E hE v) :
    Total hμ c hcard hsize hmerger hj E hE v :=
  ⟨g • x.1,transport hμ c hcard hsize hmerger hj E hE x.1 g x.2⟩

theorem totalAt_move (g : Vertex.componentStabilizer hj v) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (x : Total hμ c hcard hsize hmerger hj E hE v) :
    TotalAt hμ c hcard hsize hmerger hj E hE v (g.val • w) (g.val.val • τ)
      (totalMove hμ c hcard hsize hmerger hj E hE v g x) ↔
    TotalAt hμ c hcard hsize hmerger hj E hE v w τ x :=
  at_transport_iff hμ c hcard hsize hmerger hj E hE x.1 g w τ x.2

theorem totalMove_one (x : Total hμ c hcard hsize hmerger hj E hE v) :
    totalMove hμ c hcard hsize hmerger hj E hE v 1 x = x := by
  obtain ⟨τ,hτ⟩ := total_has_representation x
  apply total_eq_of_representation (one_smul _ x.1) (w := v) (τ := τ) _ hτ
  simpa only [Subgroup.coe_one,one_smul] using
    (totalAt_move hμ c hcard hsize hmerger hj E hE v 1 v τ x).mpr hτ

theorem totalMove_mul (g k : Vertex.componentStabilizer hj v)
    (x : Total hμ c hcard hsize hmerger hj E hE v) :
    totalMove hμ c hcard hsize hmerger hj E hE v (g*k) x =
      totalMove hμ c hcard hsize hmerger hj E hE v g
        (totalMove hμ c hcard hsize hmerger hj E hE v k x) := by
  obtain ⟨τ,hτ⟩ := total_has_representation x
  have hx := (totalAt_move hμ c hcard hsize hmerger hj E hE v (g*k) v τ x).mpr hτ
  have hy := (totalAt_move hμ c hcard hsize hmerger hj E hE v g (k.val • v)
    (k.val.val • τ) (totalMove hμ c hcard hsize hmerger hj E hE v k x)).mpr
      ((totalAt_move hμ c hcard hsize hmerger hj E hE v k v τ x).mpr hτ)
  apply total_eq_of_representation (mul_smul g k x.1) hx
  simpa only [Subgroup.coe_mul,mul_smul] using hy

/-- A genuine action only on the *family* of all moved computations. -/
instance totalAction : MulAction (Vertex.componentStabilizer hj v)
    (Total hμ c hcard hsize hmerger hj E hE v) where
  smul := totalMove hμ c hcard hsize hmerger hj E hE v
  one_smul := totalMove_one hμ c hcard hsize hmerger hj E hE v
  mul_smul := totalMove_mul hμ c hcard hsize hmerger hj E hE v

@[simp] theorem totalAction_fst (g : Vertex.componentStabilizer hj v)
    (x : Total hμ c hcard hsize hmerger hj E hE v) : (g • x).1 = g • x.1 := rfl

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## CodeCovariance -/

/-! Covariance on actual forcing conditions. The code order is held fixed,
whereas both the Cohen condition and the local supporting vertex move. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

omit [Infinite M] [Infinite I] in
/-- Every one of the shrinking chain diagrams supports the ordinal names,
not just the first diagram. -/
theorem chainFix_le_tailGroup (i : ℕ) :
    SupportFilter.Fix (C.vertex i).diagram.range ≤ tailGroup hj C := by
  intro π hπ
  have hr : (C.vertex i).diagram ≤ q := ⟨(C.vertex i).index,(C.vertex i).root⟩
  have hπq : π ∈ Vertex.RootGroup q := by
    apply (SupportFilter.mem_Fix _ _).mpr
    intro j hj
    exact (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hr hj)
  let g : Vertex.RootGroup q := ⟨π,hπq⟩
  have hg (j : I) (hj : j ∈ (C.vertex i).diagram.range) : g.val j = j :=
    (SupportFilter.mem_Fix _ _).mp hπ j hj
  let k : Vertex.componentStabilizer hj v := ⟨g,C.fixes_mem_stabilizer hj g i hg⟩
  exact (tailGroup_mem hj C π).mpr ⟨⟨k,i,hg⟩,rfl⟩

omit [Infinite M] [Infinite I] in
/-- The same code is linked to the transported name at the moved vertex.
It is not necessary for the permutation to fix the original root. -/
theorem links_permute (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (w : Vertex q) (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (a : ChainCode hμ c C) (h : Links hμ c C d w τ a) :
    Links hμ c C (d.permute k.val.val.val) (k.val.val • w) (k.val.val.val • τ) a := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := tail_fixed hμ c hj C k
  refine ⟨max N L,fun i hi => ?_⟩
  obtain ⟨⟨f⟩,he⟩ := hN i ((le_max_left _ _).trans hi)
  obtain ⟨hv,hn⟩ := hL i ((le_max_right _ _).trans hi)
  refine ⟨?_,?_⟩
  · simpa only [hv] using (show Nonempty ((k.val.val • w).Arrow (k.val.val • C.vertex i)) from
      ⟨f.move k.val.val⟩)
  · simpa only [hn (a i),move_coe,permute,Vertex.smul_diagram] using
      ((system hμ).eq_symmetry k.val.val.val ((d,w.diagram) : Poset M I κ) (a i).name τ).mp he

include c hsize hmerger in
/-- Local decision reflects a tail-invariant equality back from the moved
root. This is the needed covariance of ordinal VALUES, not just names. -/
theorem tail_eq_permute (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hτ : ∀ π ∈ tailGroup hj C, π • τ = τ)
    (hσ : ∀ π ∈ tailGroup hj C, π • σ = σ)
    (he : (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) τ σ) :
    (system hμ).atomic.EqF ((d.permute k.val.val.val,v.diagram) : Poset M I κ) τ σ := by
  obtain ⟨N,hN⟩ := tail_fixed hμ c hj C k
  have hk : k.val.val.val ∈ tailGroup hj C := (tailGroup_mem hj C _).mpr ⟨k,rfl⟩
  have hm : (system hμ).atomic.EqF
      ((d.permute k.val.val.val,(k.val.val • v).diagram) : Poset M I κ) τ σ := by
    simpa only [hτ _ hk,hσ _ hk,move_coe,permute,Vertex.smul_diagram] using
      ((system hμ).eq_symmetry k.val.val.val ((d,v.diagram) : Poset M I κ) τ σ).mp he
  have hf : Nonempty (v.Arrow (C.vertex N)) := by
    simpa only [C.first] using C.increasing 0 N (Nat.zero_le _)
  have hfm : Nonempty ((k.val.val • v).Arrow (C.vertex N)) := by
    simpa only [(hN N le_rfl).1] using
      (show Nonempty ((k.val.val • v).Arrow (k.val.val • C.vertex N)) from ⟨hf.some.move k.val.val⟩)
  have ht := eq_at_root hμ hsize hmerger τ σ (C.vertex N).diagram
    (k.val.val • v).diagram ⟨hfm.some.index,hfm.some.diagram⟩
    (fun π hπ => hτ π (chainFix_le_tailGroup hj C N hπ))
    (fun π hπ => hσ π (chainFix_le_tailGroup hj C N hπ)) (d.permute k.val.val.val) hm
  exact (system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (d.permute k.val.val.val,v.diagram) ≤
      (d.permute k.val.val.val,(C.vertex N).diagram) from
        ⟨le_rfl,⟨hf.some.index,hf.some.diagram⟩⟩)) ht

/-- Both ordinal name constructions are literally fixed by the tail group. -/
theorem ordinalRank_fixed (a : Index hμ c C) (π : Equiv.Perm I) (hπ : π ∈ tailGroup hj C) :
    π • ordinalRank hμ c hcard hsize hmerger hj E hE C a =
      ordinalRank hμ c hcard hsize hmerger hj E hE C a :=
  CohenSelection.rank_fixed hμ _ _ _ _ a π hπ

theorem ordinalType_fixed (π : Equiv.Perm I) (hπ : π ∈ tailGroup hj C) :
    π • ordinalType hμ c hcard hsize hmerger hj E hE C =
      ordinalType hμ c hcard hsize hmerger hj E hE C :=
  CohenSelection.orderType_fixed hμ _ _ _ _ π hπ

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
