import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.AvailableRecords

namespace OAI

/-! ## Component -/

namespace PartitionConsistency.LocalDiagramSystem
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

/-- The source vertex system includes its root equation. Thus its bounded
ideal is tied to this actual diagram, not an independently selected poset. -/
structure Vertex (q : Diagram M I) where
  diagram : Diagram M I
  index : M
  root : diagram.sub index = q
  ideal : ConeIdeal (show LeftDivOrder M from index)

namespace Vertex
variable {q : Diagram M I}

/-- A contraction with its uniquely determined monoid index. -/
structure Arrow (v w : Vertex q) where
  index : M
  mem : (show LeftDivOrder M from index) ∈ v.ideal.carrier
  diagram : v.diagram.sub index = w.diagram
  ideal : ∀ x : LeftDivOrder M, x ∈ w.ideal.carrier ↔
    (show LeftDivOrder M from index)*x ∈ v.ideal.carrier

namespace Arrow
variable {v w z : Vertex q}

instance : Subsingleton (Arrow v w) := ⟨by
  rintro ⟨i,hi,hdi,hUi⟩ ⟨j,hj,hdj,hUj⟩
  have h := Diagram.index_unique (hdi.trans hdj.symm)
  subst j
  rfl⟩

/-- Equality of the right factors follows from equality of the root diagrams. -/
theorem index_mul (f : Arrow v w) : f.index * w.index = v.index := by
  apply Diagram.index_unique (r := v.diagram)
  rw [← Diagram.sub_sub,f.diagram,w.root,v.root]

def id (v : Vertex q) : Arrow v v where
  index := 1
  mem := by
    obtain ⟨n,hn⟩ := v.ideal.nonempty
    exact v.ideal.lower (show (1 : LeftDivOrder M) ≤ n from bot_le) hn
  diagram := v.diagram.sub_one
  ideal := by
    intro x
    exact iff_of_eq (congrArg (fun y : LeftDivOrder M => y ∈ v.ideal.carrier)
      (one_mul x).symm)

def comp (f : Arrow v w) (g : Arrow w z) : Arrow v z where
  index := f.index*g.index
  mem := (f.ideal g.index).mp g.mem
  diagram := by rw [← Diagram.sub_sub,f.diagram,g.diagram]
  ideal := by
    intro x
    rw [g.ideal,f.ideal]
    exact iff_of_eq (congrArg (fun y => y ∈ v.ideal.carrier) (mul_assoc _ _ _).symm)

/-- If two contractions from a vertex have comparable indices, the latter
factors uniquely through the former. -/
theorem between (f : Arrow v w) (g : Arrow v z)
    (hle : (show LeftDivOrder M from f.index) ≤ g.index) : Nonempty (Arrow w z) := by
  obtain ⟨d,hd⟩ := hle
  refine ⟨⟨d,(f.ideal d).mpr ?_,?_,?_⟩⟩
  · rw [hd]
    exact g.mem
  · erw [← f.diagram,Diagram.sub_sub,hd,g.diagram]
  · intro x
    rw [f.ideal,g.ideal,← hd,mul_assoc]

/-- There is no nontrivial identity-index contraction. -/
theorem eq_of_index_one (f : Arrow v w) (h : f.index = 1) : v = w := by
  rcases v with ⟨r,a,hr,U⟩
  rcases w with ⟨s,b,hs,V⟩
  have hrs : r = s := by simpa only [h,Diagram.sub_one] using f.diagram
  subst s
  have hab : a = b := Diagram.index_unique (hr.trans hs.symm)
  subst b
  have hUV : U = V := by
    apply ConeIdeal.ext
    ext x
    have hh := f.ideal x
    rw [h] at hh
    exact (iff_of_eq (congrArg (fun y : LeftDivOrder M => y ∈ U.carrier)
      (one_mul x).symm)).trans hh.symm
  subst V
  rfl

end Arrow

/-- The explicit contraction vertex. The right quotient is specified only
to avoid a hidden choice; left cancellation makes it unique. -/
def contractAt (v : Vertex q) (n c : M)
    (hn : (show LeftDivOrder M from n) ∈ v.ideal.carrier) (hnc : n*c = v.index) : Vertex q where
  diagram := v.diagram.sub n
  index := c
  root := by rw [Diagram.sub_sub,hnc,v.root]
  ideal := v.ideal.contract hn hnc

def toContractAt (v : Vertex q) (n c : M)
    (hn : (show LeftDivOrder M from n) ∈ v.ideal.carrier) (hnc : n*c = v.index) :
    Arrow v (v.contractAt n c hn hnc) where
  index := n
  mem := hn
  diagram := rfl
  ideal _ := Iff.rfl

/-- Every ideal element supplies an actual contraction. -/
theorem exists_contraction (v : Vertex q) (n : M)
    (hn : (show LeftDivOrder M from n) ∈ v.ideal.carrier) :
    ∃ w : Vertex q, ∃ f : Arrow v w, f.index = n := by
  obtain ⟨c,hc⟩ := v.ideal.bounded hn
  exact ⟨v.contractAt n c hn hc,v.toContractAt n c hn hc,rfl⟩

/-- Finite directedness of successors, from conditional joins of indices. -/
theorem successors_directed (hj : HasConditionalJoins (LeftDivOrder M))
    {v w z : Vertex q} (f : Arrow v w) (g : Arrow v z) :
    ∃ t : Vertex q, Nonempty (Arrow w t) ∧ Nonempty (Arrow z t) := by
  obtain ⟨k,hk⟩ := hj f.index g.index v.index (v.ideal.bounded f.mem) (v.ideal.bounded g.mem)
  have hkU := v.ideal.join_closed f.mem g.mem hk
  obtain ⟨t,h,hh⟩ := v.exists_contraction k hkU
  subst k
  exact ⟨t,f.between h (hk.1 (Or.inl rfl)),g.between h (hk.1 (Or.inr rfl))⟩

/-- Two vertices have a common successor. Directedness will identify this
with connectedness in the undirected contraction graph. -/
def Common (v w : Vertex q) : Prop :=
  ∃ t : Vertex q, Nonempty (Arrow v t) ∧ Nonempty (Arrow w t)

namespace Common

theorem refl (v : Vertex q) : Common v v := ⟨v,⟨Arrow.id v⟩,⟨Arrow.id v⟩⟩

theorem symm {v w : Vertex q} : Common v w → Common w v := by
  rintro ⟨t,hv,hw⟩
  exact ⟨t,hw,hv⟩

theorem trans (hj : HasConditionalJoins (LeftDivOrder M))
    {v w z : Vertex q} : Common v w → Common w z → Common v z := by
  rintro ⟨a,⟨f⟩,⟨g⟩⟩ ⟨b,⟨h⟩,⟨k⟩⟩
  obtain ⟨t,⟨l⟩,⟨m⟩⟩ := successors_directed hj g h
  exact ⟨t,⟨f.comp l⟩,⟨k.comp m⟩⟩

theorem of_arrow {v w : Vertex q} (f : Arrow v w) : Common v w :=
  ⟨w,⟨f⟩,⟨Arrow.id w⟩⟩

/-- Common-successor equivalence is exactly the connected component relation,
not a relation identifying more diagrams than finite zigzags do. -/
theorem iff_zigzag (hj : HasConditionalJoins (LeftDivOrder M)) (v w : Vertex q) :
    Common v w ↔ Relation.EqvGen (fun v w : Vertex q => Nonempty (Arrow v w)) v w := by
  constructor
  · rintro ⟨t,hv,hw⟩
    exact Relation.EqvGen.trans v t w (Relation.EqvGen.rel v t hv)
      (Relation.EqvGen.symm w t (Relation.EqvGen.rel w t hw))
  · intro h
    induction h with
    | rel v w h => exact of_arrow h.some
    | refl v => exact refl v
    | symm v w _ ih => exact ih.symm
    | trans v w z _ _ ih₁ ih₂ => exact ih₁.trans hj ih₂

end Common

def componentSetoid (hj : HasConditionalJoins (LeftDivOrder M)) : Setoid (Vertex q) where
  r := Common
  iseqv := ⟨Common.refl,Common.symm,Common.trans hj⟩

/-- Components are a quotient of the ground set of actual vertices. -/
def Component (q : Diagram M I) (hj : HasConditionalJoins (LeftDivOrder M)) :=
  Quotient (componentSetoid (q := q) hj)

/-- A countable cofinal sequence in the bounded ideal yields a countable
cofinal chain in the *entire* component. The target is not limited to the
successors of the one initially selected vertex. -/
theorem component_cofinal_chain (hj : HasConditionalJoins (LeftDivOrder M))
    (H : HeightCost (LeftDivOrder M)) (v : Vertex q) :
    ∃ f : ℕ → Vertex q, f 0 = v ∧
      (∀ i j, i ≤ j → Nonempty (Arrow (f i) (f j))) ∧
      (∀ i, Common v (f i)) ∧
      ∀ w, Common v w → ∃ i, Nonempty (Arrow w (f i)) := by
  classical
  obtain ⟨n,hn₀,hnU,hnmono,hncof⟩ := v.ideal.countable_cofinal_sequence H hj
  choose f g hg using fun i => v.exists_contraction (n i) (hnU i)
  refine ⟨f,(g 0).eq_of_index_one ((hg 0).trans hn₀) |>.symm,?_,?_,?_⟩
  · intro i j hij
    exact (g i).between (g j) (by rw [hg i,hg j]; exact hnmono hij)
  · intro i
    exact Common.of_arrow (g i)
  · intro w hw
    obtain ⟨t,⟨a⟩,⟨b⟩⟩ := hw
    obtain ⟨i,hi⟩ := hncof a.index a.mem
    obtain ⟨c⟩ := a.between (g i) (by rw [hg i]; exact hi)
    exact ⟨i,⟨b.comp c⟩⟩

end Vertex
end PartitionConsistency.LocalDiagramSystem


/-! ## FiberMap -/

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I)

/-- Coordinatized form of availability contraction, allowing an equal but
not definitionally identical target diagram. -/
theorem mem_availability_restrict (r s : Diagram M I) (a n c : M)
    (hs : r.sub n = s) (hnc : n*c = a) (y : D.Obj s) (x : LeftDivOrder M) :
    (show LeftDivOrder M from n)*x ∈
      (D.availability r a (D.restrict (show r ≤ s from ⟨n,hs⟩) y)).carrier ↔
      x ∈ (D.availability s c y).carrier := by
  subst s
  have h := Set.ext_iff.mp (congrArg ConeIdeal.carrier (D.availability_sub r a n c hnc y)) x
  exact h.symm

/-- The exact fiber at a vertex of the source's contraction graph. -/
abbrev vertexFiber {q : Diagram M I} (v : Vertex q) :=
  D.Fiber v.diagram v.index v.ideal

/-- Inclusion along an actual contraction, with its proof that exact
availability is preserved. -/
def arrowMap (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w : Vertex q} (f : v.Arrow w)
    (y : D.vertexFiber w) : D.vertexFiber v := by
  let x := D.restrict (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) y.val
  have hn : (show LeftDivOrder M from f.index) ∈ (D.availability v.diagram v.index x).carrier := by
    have h := (D.mem_availability_restrict v.diagram w.diagram v.index f.index w.index
      f.diagram f.index_mul y.val 1).mpr
        (show (1 : LeftDivOrder M) ∈ (D.availability w.diagram w.index y.val).carrier from
          ⟨bot_le,D.available_one _ _⟩)
    change (show LeftDivOrder M from f.index) * (1 : LeftDivOrder M) ∈
      (D.availability v.diagram v.index
        (D.restrict (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) y.val)).carrier at h
    simpa only [mul_one (show LeftDivOrder M from f.index)] using h
  refine ⟨x,ConeIdeal.eq_of_contract_eq hj hn f.mem f.index_mul ?_⟩
  apply ConeIdeal.ext
  ext z
  change (show LeftDivOrder M from f.index)*z ∈ (D.availability v.diagram v.index x).carrier ↔ _
  rw [D.mem_availability_restrict _ _ _ _ _ f.diagram f.index_mul y.val z,
    y.property,f.ideal]
  rfl

@[simp] theorem arrowMap_val (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w : Vertex q} (f : v.Arrow w) (y : D.vertexFiber w) :
    (D.arrowMap hj f y).val = D.restrict (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) y.val := rfl

/-- Every contraction induces a bijection of its actual exact fibers. -/
theorem arrowMap_bijective (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w : Vertex q} (f : v.Arrow w) :
    Function.Bijective (D.arrowMap hj f) := by
  constructor
  · intro x y h
    exact Subtype.ext (D.injective ⟨f.index,f.diagram⟩ (congrArg Subtype.val h))
  · intro x
    have hn : (show LeftDivOrder M from f.index) ∈ (D.availability v.diagram v.index x.val).carrier := by
      rw [x.property]
      exact f.mem
    obtain ⟨y,hy⟩ := (D.range_congr x.val (v.diagram.self_le_sub f.index)
      (show v.diagram ≤ w.diagram from ⟨f.index,f.diagram⟩) f.diagram).mp hn.2
    refine ⟨⟨y,?_⟩,Subtype.ext hy⟩
    apply ConeIdeal.ext
    ext z
    rw [← D.mem_availability_restrict _ _ _ _ _ f.diagram f.index_mul y z,hy,x.property]
    exact (f.ideal z).symm

/-- All composition is the literal composition of inclusions. In particular
parallel chains cannot independently permute a fiber. -/
theorem arrowMap_comp (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} {v w z : Vertex q} (f : v.Arrow w) (g : w.Arrow z)
    (x : D.vertexFiber z) : D.arrowMap hj f (D.arrowMap hj g x) = D.arrowMap hj (f.comp g) x := by
  apply Subtype.ext
  exact D.restrict_comp _ _ _

@[simp] theorem arrowMap_id (hj : HasConditionalJoins (LeftDivOrder M))
    {q : Diagram M I} (v : Vertex q) (x : D.vertexFiber v) :
    D.arrowMap hj (Vertex.Arrow.id v) x = x := by
  apply Subtype.ext
  exact D.restrict_refl _

end PartitionConsistency.LocalDiagramSystem.System


/-! ## Gluing -/

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}

/-- The disjoint union used for gluing; its summands are the actual exact
fibers of the inclusion system. -/
abbrev Point (q : Diagram M I) := Σ w : Vertex q, D.vertexFiber w

/-- Two representatives agree when compared at a common contraction. -/
def Matches (x y : D.Point q) : Prop :=
  ∃ (w : Vertex q) (f : x.1.Arrow w) (g : y.1.Arrow w) (z : D.vertexFiber w),
    D.arrowMap hj f z = x.2 ∧ D.arrowMap hj g z = y.2

namespace Matches

protected theorem refl (x : D.Point q) : D.Matches hj x x :=
  ⟨x.1,Vertex.Arrow.id x.1,Vertex.Arrow.id x.1,x.2,D.arrowMap_id hj _ _,D.arrowMap_id hj _ _⟩

protected theorem symm {x y : D.Point q} (h : D.Matches hj x y) : D.Matches hj y x := by
  obtain ⟨w,f,g,z,hf,hg⟩ := h
  exact ⟨w,g,f,z,hg,hf⟩

/-- Transitivity uses directedness and surjectivity of the restriction maps;
no independent bijections are chosen at vertices. -/
protected theorem trans {x y z : D.Point q}
    (hxy : D.Matches hj x y) (hyz : D.Matches hj y z) : D.Matches hj x z := by
  obtain ⟨a,f,g,b,hf,hg⟩ := hxy
  obtain ⟨c,h,k,d,hh,hk⟩ := hyz
  obtain ⟨t,⟨l⟩,⟨m⟩⟩ := Vertex.successors_directed hj g h
  obtain ⟨e,he⟩ := (D.arrowMap_bijective hj l).2 b
  have hgm : g.comp l = h.comp m := Subsingleton.elim _ _
  have hd : D.arrowMap hj m e = d := by
    apply (D.arrowMap_bijective hj h).1
    rw [D.arrowMap_comp,← hgm,← D.arrowMap_comp,he,hg,hh]
  refine ⟨t,f.comp l,k.comp m,e,?_,?_⟩
  · rw [← D.arrowMap_comp,he,hf]
  · rw [← D.arrowMap_comp,hd,hk]

/-- Gluing does not make any two different members of one fiber equal. -/
theorem same (w : Vertex q) (x y : D.vertexFiber w) :
    D.Matches hj ⟨w,x⟩ ⟨w,y⟩ ↔ x = y := by
  constructor
  · rintro ⟨t,f,g,z,hf,hg⟩
    have he : f = g := Subsingleton.elim _ _
    exact hf.symm.trans (he ▸ hg)
  · rintro rfl
    exact Matches.refl D hj _

theorem common {x y : D.Point q} (h : D.Matches hj x y) : Vertex.Common x.1 y.1 := by
  obtain ⟨w,f,g,_⟩ := h
  exact ⟨w,⟨f⟩,⟨g⟩⟩

end Matches

/-- Representatives in one component, before taking the identification
quotient. The selected vertex determines a component, not an additional
edge relation or a different family of fibers. -/
abbrev ComponentPoint (root : Vertex q) := {x : D.Point q // Vertex.Common root x.1}

def gluingSetoid (root : Vertex q) : Setoid (D.ComponentPoint root) where
  r x y := D.Matches hj x.val y.val
  iseqv := ⟨fun x => Matches.refl D hj x.val,
    fun h => h.symm D hj,fun h k => h.trans D hj k⟩

/-- The source glued component. -/
def Glued (root : Vertex q) := Quotient (D.gluingSetoid hj root)

def toGlued (root w : Vertex q) (hw : Vertex.Common root w)
    (x : D.vertexFiber w) : D.Glued hj root := Quotient.mk _ ⟨⟨w,x⟩,hw⟩

/-- Inclusion of each entire fiber is injective. -/
theorem toGlued_injective (root w : Vertex q) (hw : Vertex.Common root w) :
    Function.Injective (D.toGlued hj root w hw) := by
  intro x y he
  exact (Matches.same D hj w x y).mp (Quotient.exact he)

/-- Every representative of the glued set has a unique representative in
any specified vertex fiber. -/
theorem toGlued_surjective (root w : Vertex q) (hw : Vertex.Common root w) :
    Function.Surjective (D.toGlued hj root w hw) := by
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
    obtain ⟨t,⟨f⟩,⟨g⟩⟩ := hw.symm.trans hj z.property
    obtain ⟨x,hx⟩ := (D.arrowMap_bijective hj g).2 z.val.2
    refine ⟨D.arrowMap hj f x,Quotient.sound ?_⟩
    exact ⟨t,f,g,x,rfl,hx⟩

noncomputable def fiberEquivGlued (root w : Vertex q) (hw : Vertex.Common root w) :
    D.vertexFiber w ≃ D.Glued hj root :=
  Equiv.ofBijective (D.toGlued hj root w hw)
    ⟨D.toGlued_injective hj root w hw,D.toGlued_surjective hj root w hw⟩

/-- The canonical fiber identifications commute with the gluing maps. -/
theorem toGlued_arrow (root w z : Vertex q) (hw : Vertex.Common root w)
    (hz : Vertex.Common root z) (f : w.Arrow z) (x : D.vertexFiber z) :
    D.toGlued hj root w hw (D.arrowMap hj f x) = D.toGlued hj root z hz x := by
  apply Quotient.sound
  exact ⟨z,f,Vertex.Arrow.id z,x,rfl,D.arrowMap_id hj _ _⟩

end PartitionConsistency.LocalDiagramSystem.System

end OAI
