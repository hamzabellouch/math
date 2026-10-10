import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.ConcreteSystem

namespace OAI

/-! ## Transport -/

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

@[simp] theorem GenericFilter.move_refl (F : GenericFilter P) :
    F.move (OrderIso.refl P) = F := by
  ext p
  rfl

@[simp] theorem GenericFilter.move_trans (F : GenericFilter P) (e f : P ≃o P) :
    (F.move e).move f = F.move (e.trans f) := by
  ext p
  rfl

@[simp] theorem GenericFilter.move_symm (F : GenericFilter P) (e : P ≃o P) :
    (F.move e).move e.symm = F := by
  ext p
  change OrderDual.toDual (e.symm (e (OrderDual.ofDual p))) ∈ F ↔ p ∈ F
  rw [e.symm_apply_apply]
  rfl

end PartitionConsistency.ForcingQuotient

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Equal supporting diagrams can be identified without changing any name
code. This explicit version has a definitionally unchanged underlying name. -/
def LocalName.rebase {r s : Diagram M I} (hrs : r = s) (σ : LocalName hμ c r) :
    LocalName hμ c s := ⟨σ.val,by rw [← hrs]; exact σ.property⟩

@[simp] theorem LocalName.rebase_name {r s : Diagram M I} (hrs : r = s)
    (σ : LocalName hμ c r) : (σ.rebase hμ c hrs).name = σ.name := rfl

/-- Literal name transport is a bijection of the whole ground collection,
including the support and normalization requirements. -/
def LocalName.transportEquiv (π : Equiv.Perm I) (r : Diagram M I) :
    LocalName hμ c r ≃ LocalName hμ c (r.permute π) where
  toFun := LocalName.transport hμ π
  invFun σ := (σ.transport hμ π⁻¹).rebase hμ c (r.permute_inv_permute π)
  left_inv σ := by
    apply LocalName.ext
    change π⁻¹ • (π • σ.name) = σ.name
    exact inv_smul_smul π σ.name
  right_inv σ := by
    apply LocalName.ext
    change π • (π⁻¹ • σ.name) = σ.name
    exact smul_inv_smul π σ.name

variable {c hμ}

/-- Equality of local names is preserved and reflected between the original
filter and the moved filter. Only actual product-forcing symmetry is used. -/
theorem local_eq_transport_iff (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I) (σ τ : LocalName hμ c r) :
    (localAtomic hμ (r.permute π)).EqG
        (F.move (CohenForcing.Condition.permuteOrderIso π))
        (σ.transport hμ π).name (τ.transport hμ π).name ↔
      (localAtomic hμ r).EqG F σ.name τ.name := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  constructor
  · rintro ⟨d,hd,he⟩
    change S.atomic.EqF ((OrderDual.ofDual d,r.permute π) : Poset M I κ) (π • σ.name) (π • τ.name) at he
    refine ⟨(OrderDual.ofDual d).permute π⁻¹,hd,?_⟩
    apply (S.eq_symmetry π (((OrderDual.ofDual d).permute π⁻¹,r) : Poset M I κ) σ.name τ.name).mpr
    simpa only [S,move_coe,permute,CohenForcing.Condition.permute_permute_inv] using he
  · rintro ⟨d,hd,he⟩
    change S.atomic.EqF ((OrderDual.ofDual d,r) : Poset M I κ) σ.name τ.name at he
    change ∃ d, d ∈ F.move (CohenForcing.Condition.permuteOrderIso π) ∧
      S.atomic.EqF ((OrderDual.ofDual d,r.permute π) : Poset M I κ) (π • σ.name) (π • τ.name)
    refine ⟨(OrderDual.ofDual d).permute π,(GenericFilter.mem_move F _ d).mpr hd,?_⟩
    change S.atomic.EqF (((OrderDual.ofDual d).permute π,r.permute π) : Poset M I κ) (π • σ.name) (π • τ.name)
    simpa only [S,move_coe,permute] using
      (S.eq_symmetry π ((OrderDual.ofDual d,r) : Poset M I κ) σ.name τ.name).mp he

namespace LocalQuotient
variable (F : GenericFilter (CohenForcing.Condition I κ))

@[simp] theorem transport_ofName (π : Equiv.Perm I) {r : Diagram M I}
    (σ : LocalName hμ c r) :
    transport hμ F π (ofName F σ) =
      ofName (F.move (CohenForcing.Condition.permuteOrderIso π)) (σ.transport hμ π) := rfl

theorem transport_injective (π : Equiv.Perm I) (r : Diagram M I) :
    Function.Injective (transport (c := c) hμ F π (r := r)) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h σ =>
    induction y using Quotient.inductionOn with
    | h τ =>
      intro h
      apply (ofName_eq F σ τ).mpr
      exact (local_eq_transport_iff F π r σ τ).mp (Quotient.exact h)

theorem transport_surjective (π : Equiv.Perm I) (r : Diagram M I) :
    Function.Surjective (transport (c := c) hμ F π (r := r)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h τ =>
    obtain ⟨σ,rfl⟩ := (LocalName.transportEquiv hμ c π r).surjective τ
    exact ⟨ofName F σ,rfl⟩

/-- Source (symbolic-transport) is a genuine equivalence, not only a map.
It does not assert an automorphism of one fixed interpreted model. -/
def transportEquiv (π : Equiv.Perm I) (r : Diagram M I) :
    LocalQuotient (c := c) hμ F r ≃
      LocalQuotient (c := c) hμ (F.move (CohenForcing.Condition.permuteOrderIso π)) (r.permute π) :=
  Equiv.ofBijective (transport hμ F π) ⟨transport_injective F π r,transport_surjective F π r⟩

/-- Coordinate transport commutes literally with restriction of symbolic
names. This is the naturality needed for contraction and gluing. -/
@[simp] theorem transport_restrict (π : Equiv.Perm I) {r s : Diagram M I} (hsr : s ≤ r)
    (x : LocalQuotient (c := c) hμ F r) :
    transport hμ F π (restrict F hsr x) =
      restrict (F.move (CohenForcing.Condition.permuteOrderIso π))
        ((Diagram.permuteOrderIso π).monotone hsr) (transport hμ F π x) := by
  induction x using Quotient.inductionOn
  rfl

end LocalQuotient

/-- Eligibility uses the moved equivalence-relation name and the moved
filter; the set of Cohen labels itself is fixed by coordinate permutations. -/
theorem eligibleName_coordinate_transport (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r) :
    EligibleName hμ c (F.move (CohenForcing.Condition.permuteOrderIso π))
        (r.permute π) (π • E) (τ.transport hμ π) ↔
      EligibleName hμ c F r E τ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hv : (fun i => π • (![τ.name,labelSet hμ c,E] : Fin 3 → S.Name) i) =
      ![π • τ.name,labelSet hμ c,π • E] := by
    apply funext
    intro i
    fin_cases i
    · rfl
    · exact smul_labelSet (M := M) (I := I) hμ c π
    · rfl
  constructor
  · rintro ⟨d,hd,hf⟩
    refine ⟨d.permute π⁻¹,hd,?_⟩
    apply (S.forces_symmetry π (SetLanguage.isClass 0 1 2)
      ![τ.name,labelSet hμ c,E] ((d.permute π⁻¹,r) : Poset M I κ)).mpr
    simpa only [hv,S,move_coe,permute,CohenForcing.Condition.permute_permute_inv,LocalName.transport_name] using hf
  · rintro ⟨d,hd,hf⟩
    refine ⟨d.permute π,(GenericFilter.mem_move F _ d).mpr hd,?_⟩
    simpa only [hv,S,move_coe,permute,LocalName.transport_name] using
      (S.forces_symmetry π (SetLanguage.isClass 0 1 2)
        ![τ.name,labelSet hμ c,E] ((d,r) : Poset M I κ)).mp hf

theorem eligible_coordinate_transport (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (x : LocalQuotient (c := c) hμ F r) :
    Eligible hμ c (F.move (CohenForcing.Condition.permuteOrderIso π))
        (r.permute π) (π • E) (LocalQuotient.transport hμ F π x) ↔
      Eligible hμ c F r E x := by
  induction x using Quotient.inductionOn with
  | h τ => exact eligibleName_coordinate_transport F π r E τ

/-- Transport of actual eligible classes, without assumptions that an
arbitrary model is generic or that E's quotient has chosen representatives. -/
def eligibleTransportEquiv (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    EligibleClasses hμ c F r E ≃
      EligibleClasses hμ c (F.move (CohenForcing.Condition.permuteOrderIso π)) (r.permute π) (π • E) :=
  (LocalQuotient.transportEquiv F π r).subtypeEquiv
    (fun x => (eligible_coordinate_transport F π r E x).symm)

end
end PartitionConsistency.ProductForcing


/-! ## SystemTransport -/

/-!
Naturality of the exact fibers and the glued component under relabeling.
These are assertions about the genuine local quotient systems, not choices
of fiber bijections. In the application the source and target generics differ.
-/
namespace PartitionConsistency.LocalDiagramSystem
universe u v w
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- A reindexing isomorphism of diagram systems. The compatibility square
uses the already-defined literal restriction maps. -/
structure ReindexIso (D : System.{u,v} M I) (E : System.{u,w} M I) (π : Equiv.Perm I) where
  app (r : Diagram M I) : D.Obj r ≃ E.Obj (r.permute π)
  natural {r s : Diagram M I} (hsr : s ≤ r) (x : D.Obj r) :
    app s (D.restrict hsr x) = E.restrict ((Diagram.permuteOrderIso π).monotone hsr) (app r x)

namespace ReindexIso
variable {D : System.{u,v} M I} {E : System.{u,w} M I} {π : Equiv.Perm I}
variable (T : ReindexIso D E π)

/-- An available local element remains available at exactly the same monoid
positions after both its diagram and its name are transported. -/
theorem available_iff (r : Diagram M I) (x : D.Obj r) (n : M) :
    E.Available (r.permute π) (T.app r x) n ↔ D.Available r x n := by
  have hsub := (Diagram.permuteOrderIso π).monotone (r.self_le_sub n)
  have hranges := E.range_congr (T.app r x) hsub ((r.permute π).self_le_sub n)
    (Diagram.permute_sub π r n)
  constructor
  · intro h
    have h' : ∃ y : E.Obj ((r.sub n).permute π), E.restrict hsub y = T.app r x := by
      exact hranges.mpr h
    obtain ⟨y,hy⟩ := h'
    obtain ⟨z,rfl⟩ := (T.app (r.sub n)).surjective y
    refine ⟨z,(T.app r).injective ?_⟩
    rw [T.natural]
    exact hy
  · rintro ⟨y,hy⟩
    have h' : ∃ z : E.Obj ((r.sub n).permute π), E.restrict hsub z = T.app r x :=
      ⟨T.app (r.sub n) y, (T.natural (r.self_le_sub n) y).symm.trans (congrArg (T.app r) hy)⟩
    exact hranges.mp h'

/-- Thus the entire availability ideal, not only an individual cofinal
sequence, is literally unchanged as a subset of the monoid cone. -/
theorem availability (r : Diagram M I) (a : M) (x : D.Obj r) :
    E.availability (r.permute π) a (T.app r x) = D.availability r a x := by
  apply ConeIdeal.ext
  ext n
  exact and_congr Iff.rfl (T.available_iff r x n)

variable {q : Diagram M I} (g : Vertex.RootGroup q)
variable (T : ReindexIso D E g.val)

/-- Isomorphism of the actual exact fibers at moved vertices. -/
def fiberEquiv (a : Vertex q) : D.vertexFiber a ≃ E.vertexFiber (g • a) :=
  (T.app a.diagram).subtypeEquiv (fun x => by
    change D.availability a.diagram a.index x = a.ideal ↔
      E.availability (a.diagram.permute g.val) a.index (T.app a.diagram x) = a.ideal
    rw [T.availability])

@[simp] theorem fiberEquiv_val (a : Vertex q) (x : D.vertexFiber a) :
    (T.fiberEquiv g a x).val = T.app a.diagram x.val := rfl

/-- Every contraction and its transported contraction give the same map
on symbolic elements after transport. -/
theorem fiberEquiv_arrow (hj : HasConditionalJoins (LeftDivOrder M))
    {a b : Vertex q} (f : a.Arrow b) (x : D.vertexFiber b) :
    T.fiberEquiv g a (D.arrowMap hj f x) =
      E.arrowMap hj (f.move g) (T.fiberEquiv g b x) := by
  apply Subtype.ext
  exact T.natural (show a.diagram ≤ b.diagram from ⟨f.index,f.diagram⟩) x.val

/-- A component equivalence obtained through a root fiber. The independent
proof below shows that it agrees with transport at every other vertex. -/
noncomputable def gluedEquiv (hj : HasConditionalJoins (LeftDivOrder M)) (a : Vertex q) :
    D.Glued hj a ≃ E.Glued hj (g • a) :=
  (D.fiberEquivGlued hj a a (Vertex.Common.refl a)).symm.trans
    ((T.fiberEquiv g a).trans
      (E.fiberEquivGlued hj (g • a) (g • a) (Vertex.Common.refl (g • a))))

@[simp] theorem gluedEquiv_root (hj : HasConditionalJoins (LeftDivOrder M))
    (a : Vertex q) (x : D.vertexFiber a) :
    T.gluedEquiv g hj a (D.toGlued hj a a (Vertex.Common.refl a) x) =
      E.toGlued hj (g • a) (g • a) (Vertex.Common.refl (g • a)) (T.fiberEquiv g a x) := by
  change E.toGlued hj (g • a) (g • a) (Vertex.Common.refl (g • a))
    (T.fiberEquiv g a ((D.fiberEquivGlued hj a a (Vertex.Common.refl a)).symm
      ((D.fiberEquivGlued hj a a (Vertex.Common.refl a)) x))) = _
  rw [Equiv.symm_apply_apply]

/-- Naturality on the *whole* component. In particular the root-fiber
construction of `gluedEquiv` does not make independent choices at vertices. -/
theorem gluedEquiv_toGlued (hj : HasConditionalJoins (LeftDivOrder M))
    (a b : Vertex q) (hb : Vertex.Common a b) (x : D.vertexFiber b) :
    T.gluedEquiv g hj a (D.toGlued hj a b hb x) =
      E.toGlued hj (g • a) (g • b) (hb.move g) (T.fiberEquiv g b x) := by
  obtain ⟨t,⟨f⟩,⟨h⟩⟩ := (show Vertex.Common a b from hb)
  obtain ⟨z,rfl⟩ := (D.arrowMap_bijective hj h).2 x
  have hat : Vertex.Common a t := Vertex.Common.of_arrow f
  have hleft : D.toGlued hj a b hb (D.arrowMap hj h z) =
      D.toGlued hj a a (Vertex.Common.refl a) (D.arrowMap hj f z) :=
    (D.toGlued_arrow hj a b t hb hat h z).trans
      (D.toGlued_arrow hj a a t (Vertex.Common.refl a) hat f z).symm
  rw [hleft,T.gluedEquiv_root,T.fiberEquiv_arrow,T.fiberEquiv_arrow]
  exact (E.toGlued_arrow hj (g • a) (g • a) (g • t)
    (Vertex.Common.refl (g • a)) (hat.move g) (f.move g) (T.fiberEquiv g t z)).trans
      (E.toGlued_arrow hj (g • a) (g • b) (g • t)
        (hb.move g) (hat.move g) (h.move g) (T.fiberEquiv g t z)).symm

end ReindexIso
end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The source and target here are the actual systems of eligible classes.
Transport of the filter, names and diagrams supplies every axiom of the
reindexing isomorphism. Since the permutation fixes q, it fixes E literally. -/
def eligibleSystemTransport [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) (π : Vertex.RootGroup q) :
    ReindexIso (eligibleSystem hμ c hcard hsize hmerger F q E hE)
      (eligibleSystem hμ c hcard hsize hmerger
        (F.move (CohenForcing.Condition.permuteOrderIso π.val)) q E hE) π.val where
  app r := (LocalQuotient.transportEquiv (c := c) (hμ := hμ) F π.val r).subtypeEquiv
    (fun x => by
      have hq : q.permute π.val = q :=
        Diagram.permute_eq_of_fixes_range _ _ ((SupportFilter.mem_Fix _ _).mp π.property)
      have hle : r ≤ q ↔ r.permute π.val ≤ q := by
        constructor
        · intro hr
          have hr' : r.permute π.val ≤ q.permute π.val :=
            (Diagram.permuteOrderIso π.val).monotone hr
          simpa only [hq] using hr' 
        · intro hr
          apply (Diagram.permuteOrderIso π.val).le_iff_le.mp
          change r.permute π.val ≤ q.permute π.val
          simpa only [hq] using hr
      have hel := eligible_coordinate_transport F π.val r E x
      rw [hE π.val π.property] at hel
      exact and_congr hle hel.symm)
  natural hsr x := Subtype.ext (LocalQuotient.transport_restrict F π.val hsr x.val)

end
end PartitionConsistency.ProductForcing


/-! ## ComponentRebase -/

/-! Canonical change of the chosen root of a glued component.  These maps
retain each representative literally and have no auxiliary choices. -/
namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}

/-- Changing the root inside its component changes only the proof that a
representative belongs to the component. -/
def rebaseGlued {a b : Vertex q} (hab : Vertex.Common a b) :
    D.Glued hj a ≃ D.Glued hj b where
  toFun := Quotient.map (fun x => ⟨x.val,hab.symm.trans hj x.property⟩)
    (fun _ _ h => h)
  invFun := Quotient.map (fun x => ⟨x.val,hab.trans hj x.property⟩)
    (fun _ _ h => h)
  left_inv := by intro x; induction x using Quotient.inductionOn; rfl
  right_inv := by intro x; induction x using Quotient.inductionOn; rfl

@[simp] theorem rebaseGlued_toGlued {a b : Vertex q} (hab : Vertex.Common a b)
    (w : Vertex q) (hw : Vertex.Common a w) (x : D.vertexFiber w) :
    D.rebaseGlued hj hab (D.toGlued hj a w hw x) =
      D.toGlued hj b w (hab.symm.trans hj hw) x := rfl

@[simp] theorem rebaseGlued_refl (a : Vertex q) (x : D.Glued hj a) :
    D.rebaseGlued hj (Vertex.Common.refl a) x = x := by
  induction x using Quotient.inductionOn
  rfl

@[simp] theorem rebaseGlued_trans {a b c : Vertex q}
    (hab : Vertex.Common a b) (hbc : Vertex.Common b c) (x : D.Glued hj a) :
    D.rebaseGlued hj hbc (D.rebaseGlued hj hab x) =
      D.rebaseGlued hj (hab.trans hj hbc) x := by
  induction x using Quotient.inductionOn
  rfl

end PartitionConsistency.LocalDiagramSystem.System

namespace PartitionConsistency.LocalDiagramSystem.ReindexIso
universe u v w
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {D : System.{u,v} M I} {E : System.{u,w} M I}
variable {q : Diagram M I} (g : Vertex.RootGroup q) (T : ReindexIso D E g.val)
variable (hj : HasConditionalJoins (LeftDivOrder M))
noncomputable section

/-- Naturality also holds when both chosen roots are changed. -/
theorem gluedEquiv_rebase {a b : Vertex q} (hab : Vertex.Common a b)
    (x : D.Glued hj a) :
    T.gluedEquiv g hj b (D.rebaseGlued hj hab x) =
      E.rebaseGlued hj (hab.move g) (T.gluedEquiv g hj a x) := by
  obtain ⟨y,rfl⟩ := D.toGlued_surjective hj a a (Vertex.Common.refl a) x
  rw [System.rebaseGlued_toGlued,T.gluedEquiv_toGlued,T.gluedEquiv_root,
    System.rebaseGlued_toGlued]

/-- If g stabilizes the component, transport is an equivalence to the
symbolic component at the original chosen root of the *moved* system. -/
def componentEquiv (a : Vertex q) (ha : Vertex.Common a (g • a)) :
    D.Glued hj a ≃ E.Glued hj a :=
  (T.gluedEquiv g hj a).trans (E.rebaseGlued hj ha.symm)

theorem componentEquiv_toGlued (a b : Vertex q) (ha : Vertex.Common a (g • a))
    (hb : Vertex.Common a b) (x : D.vertexFiber b) :
    T.componentEquiv g hj a ha (D.toGlued hj a b hb x) =
      E.toGlued hj a (g • b) (ha.trans hj (hb.move g)) (T.fiberEquiv g b x) := by
  change E.rebaseGlued hj ha.symm (T.gluedEquiv g hj a (D.toGlued hj a b hb x)) = _
  rw [T.gluedEquiv_toGlued,System.rebaseGlued_toGlued]

end
end PartitionConsistency.LocalDiagramSystem.ReindexIso

end OAI
