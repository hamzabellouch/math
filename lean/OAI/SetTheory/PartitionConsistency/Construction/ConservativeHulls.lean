import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.MergerPushouts
import OAI.SetTheory.PartitionConsistency.Construction.SaturatedMonoids

namespace OAI

/-! ## MonoidColimit -/

/-! The directed unions used by the monoid construction retain their
universal property against arbitrary monoid homomorphisms. The stronger
category of conservative height/cost embeddings is not a restriction on
the presentation universal property. -/
namespace PartitionConsistency.MonoidConstruction.DirectedColimit
universe u v
open CategoryTheory CategoryTheory.Limits
noncomputable section
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ Object.{u})
variable {N : Type v} [Monoid N]

/-- Evaluation of a directed union in an arbitrary target monoid. -/
def monoidLift (f : ∀ i, F.obj i →* N)
    (hf : ∀ i j h, (f j).comp (transition F i j h) = f i) : object F →* N where
  toFun := DirectLimit.lift (transition F) (fun i => f i)
    (fun i j h x => (DFunLike.congr_fun (hf i j h) x).symm)
  map_one' := by
    let j : J := Classical.arbitrary J
    change DirectLimit.lift (transition F) (fun i => f i) _ 1 = 1
    rw [← (old F j).map_one]
    exact (f j).map_one
  map_mul' x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    change DirectLimit.lift (transition F) (fun i => f i) _
      (old F i x * old F i y) = _
    rw [← (old F i).map_mul]
    exact (f i).map_mul x y

@[simp] theorem monoidLift_old (f : ∀ i, F.obj i →* N)
    (hf : ∀ i j h, (f j).comp (transition F i j h) = f i) (i : J) (x : F.obj i) :
    monoidLift F f hf (old F i x) = f i x := rfl

@[simp] theorem monoidLift_comp_old (f : ∀ i, F.obj i →* N)
    (hf : ∀ i j h, (f j).comp (transition F i j h) = f i) (i : J) :
    (monoidLift F f hf).comp (old F i) = f i := by ext; rfl

/-- Every element of the union belongs to a stage, so homomorphisms are
uniquely determined on stages, without preservation assumptions on them. -/
theorem monoidHom_ext {f g : object F →* N}
    (h : ∀ i, f.comp (old F i) = g.comp (old F i)) : f = g := by
  ext x
  obtain ⟨i,y,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
  exact DFunLike.congr_fun (h i) y

theorem monoidLift_unique (f : ∀ i, F.obj i →* N)
    (hf : ∀ i j h, (f j).comp (transition F i j h) = f i)
    (g : object F →* N) (hg : ∀ i, g.comp (old F i) = f i) :
    g = monoidLift F f hf := by
  apply monoidHom_ext F
  intro i
  rw [monoidLift_comp_old,hg]

/-- A fixed coherent base maps to a directed union independently of the stage
used to define the map. -/
def fromBase {A : Type v} [Monoid A] (g : ∀ i, A →* F.obj i) : A →* object F :=
  (old F (Classical.arbitrary J)).comp (g (Classical.arbitrary J))

theorem fromBase_eq {A : Type v} [Monoid A] (g : ∀ i, A →* F.obj i)
    (hg : ∀ i j h, (transition F i j h).comp (g i) = g j) (i : J) :
    fromBase F g = (old F i).comp (g i) := by
  obtain ⟨j,hi,hj⟩ := exists_ge_ge (Classical.arbitrary J) i
  have ht (k : J) (h : k ≤ j) : (old F k).comp (g k) = (old F j).comp (g j) := by
    rw [← hg k j h,← MonoidHom.comp_assoc]
    congr 1
    ext x
    exact (old_map F k j h x).symm
  exact (ht _ hi).trans (ht _ hj).symm

/-- The literal map of direct limits induced by a coherent map of stages. -/
def monoidMap (G : J ⥤ Object.{u}) (g : ∀ i, F.obj i →* G.obj i)
    (hg : ∀ i j h, (transition G i j h).comp (g i) = (g j).comp (transition F i j h)) :
    object F →* object G :=
  monoidLift F (fun i => (old G i).comp (g i)) (fun i j h => by
    erw [MonoidHom.comp_assoc,← hg i j h,← MonoidHom.comp_assoc]
    congr 1
    ext x
    exact old_map G i j h x)

@[simp] theorem monoidMap_comp_old (G : J ⥤ Object.{u}) (g : ∀ i, F.obj i →* G.obj i)
    (hg : ∀ i j h, (transition G i j h).comp (g i) = (g j).comp (transition F i j h))
    (i : J) : (monoidMap F G g hg).comp (old F i) = (old G i).comp (g i) :=
  monoidLift_comp_old F _ _ i

end
end PartitionConsistency.MonoidConstruction.DirectedColimit


/-! ## DirectedPushout -/

namespace PartitionConsistency.MonoidConstruction.DirectedColimit
universe u
open CategoryTheory CategoryTheory.Limits MonoidPushout
noncomputable section
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F G : J ⥤ Object.{u})
variable {A B : Type u} [Monoid A] [Monoid B]
variable (f : A →* B) (a : ∀ i, A →* F.obj i) (b : ∀ i, B →* G.obj i)
  (g : ∀ i, F.obj i →* G.obj i)
  (ha : ∀ i j h, (transition F i j h).comp (a i) = a j)
  (hb : ∀ i j h, (transition G i j h).comp (b i) = b j)
  (hg : ∀ i j h, (transition G i j h).comp (g i) = (g j).comp (transition F i j h))

include ha hb
/-- Pushout presentations commute with the actual directed unions in the
construction. In particular, a limit stage of the selected subconstruction
has the same presentation whether its cells were attached before or after
the fixed base change `f`. -/
theorem pushout_of_stage (h : ∀ i, IsPushout f (a i) (b i) (g i)) :
    IsPushout f (fromBase F a) (fromBase G b) (monoidMap F G g hg) where
  comm := by
    let j : J := Classical.arbitrary J
    erw [fromBase_eq G b hb j,MonoidHom.comp_assoc,(h j).comm,
      ← MonoidHom.comp_assoc]
  universal c d hc := by
    have hi (i : J) : c.comp f = (d.comp (old F i)).comp (a i) := by
      erw [hc,fromBase_eq F a ha i,MonoidHom.comp_assoc]
      rfl
    let t (i : J) : G.obj i →* _ := (h i).lift c (d.comp (old F i)) (hi i)
    have ht₁ (i : J) : (t i).comp (b i) = c := (h i).lift_comp_left _ _ _
    have ht₂ (i : J) : (t i).comp (g i) = d.comp (old F i) :=
      (h i).lift_comp_right _ _ _
    have hco (i j : J) (hij : i ≤ j) : (t j).comp (transition G i j hij) = t i := by
      apply (h i).hom_ext
      · rw [MonoidHom.comp_assoc,hb,ht₁,ht₁]
      · erw [MonoidHom.comp_assoc,hg,← MonoidHom.comp_assoc,ht₂,
          MonoidHom.comp_assoc,ht₂]
        congr 1
        ext x
        exact old_map F i j hij x
    let k := monoidLift G t hco
    have hk₁ : k.comp (fromBase G b) = c := by
      erw [fromBase_eq G b hb (Classical.arbitrary J),← MonoidHom.comp_assoc]
      exact ((congrArg (fun l => l.comp (b (Classical.arbitrary J)))
        (monoidLift_comp_old G t hco (Classical.arbitrary J)))).trans (ht₁ _)
    have hk₂ : k.comp (monoidMap F G g hg) = d := by
      apply monoidHom_ext F
      intro i
      erw [MonoidHom.comp_assoc,monoidMap_comp_old,← MonoidHom.comp_assoc]
      change ((monoidLift G t hco).comp (old G i)).comp (g i) = _
      rw [monoidLift_comp_old,ht₂]
    refine ⟨k,⟨hk₁,hk₂⟩,?_⟩
    intro l hl
    apply monoidHom_ext G
    intro i
    apply (h i).hom_ext
    · erw [MonoidHom.comp_assoc,MonoidHom.comp_assoc,
        ← fromBase_eq G b hb i,hl.1,hk₁]
    · erw [MonoidHom.comp_assoc,MonoidHom.comp_assoc,
        ← monoidMap_comp_old F G g hg i,← MonoidHom.comp_assoc,
        ← MonoidHom.comp_assoc,hl.2,hk₂]

end
end PartitionConsistency.MonoidConstruction.DirectedColimit


/-! ## ConservativeHull -/

/-! Countable conservative submonoids.  This closes an arbitrary countable
set under specified countable dependencies, right factors and joins.  It is
only the hull part of the countable-base rearrangement; it does not identify
the complement presentation with an iterated gate tower. -/
namespace PartitionConsistency.CountableHull
universe u
noncomputable section
open scoped Classical
variable {A : Type u} (s : Set A) (op : A → A → Set A)

def stage : ℕ → Set A
  | 0 => s
  | n+1 => stage n ∪ ⋃ x ∈ stage n, ⋃ y ∈ stage n, op x y

def carrier : Set A := ⋃ n, stage s op n

theorem stage_mono : Monotone (stage s op) :=
  monotone_nat_of_le_succ (fun _ => Set.subset_union_left)

theorem subset_carrier : s ⊆ carrier s op := fun _ h => Set.mem_iUnion.mpr ⟨0,h⟩

theorem countable (hs : s.Countable) (hop : ∀ x y, (op x y).Countable) :
    (carrier s op).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hs
  | succ n hn =>
    exact hn.union (hn.biUnion (fun x _ => hn.biUnion (fun y _ => hop x y)))

theorem closed {x y : A} (hx : x ∈ carrier s op) (hy : y ∈ carrier s op) :
    op x y ⊆ carrier s op := by
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hy
  intro z hz
  apply Set.mem_iUnion.mpr
  refine ⟨max m n+1,Or.inr ?_⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨stage_mono s op (le_max_left _ _) hm,
    Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨stage_mono s op (le_max_right _ _) hn,hz⟩⟩⟩⟩

end
end PartitionConsistency.CountableHull

namespace PartitionConsistency.DiagramOrder
universe u
noncomputable section
open scoped Classical
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

instance (S : Submonoid M) : IsConical S where
  eq_one_of_mul_eq_one {x y} h := by
    have h' : x.val * y.val = 1 := congrArg Subtype.val h
    obtain ⟨hx,hy⟩ := IsConical.eq_one_of_mul_eq_one h'
    exact ⟨Subtype.ext hx,Subtype.ext hy⟩

namespace ConservativeHull

/-- The unique right factor when it exists, and `1` otherwise. -/
def factor (x y : M) : M := if h : x ∣ y then h.choose else 1

omit [IsConical M] in
theorem factor_eq (x y z : M) (h : x*z = y) : factor x y = z := by
  have hxy : x ∣ y := ⟨z,h.symm⟩
  rw [factor,dite_eq_left hxy]
  exact mul_left_cancel (hxy.choose_spec.symm.trans h.symm)

/-- The conditional join when it exists, and `1` for a pair with disjoint
right cones. There is no completion added to the monoid. -/
def join (x y : M) : M :=
  if h : ∃ j : M, ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z then h.choose else 1

theorem join_spec (hj : HasConditionalJoins (LeftDivOrder M)) (x y : M)
    (h : ∃ z : M, x ∣ z ∧ y ∣ z) :
    ∀ z : M, x ∣ z ∧ y ∣ z ↔ join x y ∣ z := by
  have hex : ∃ j : M, ∀ z : M, x ∣ z ∧ y ∣ z ↔ j ∣ z := by
    obtain ⟨z,hx,hy⟩ := h
    exact exists_cone_join hj x y z hx hy
  rw [join,dite_eq_left hex]
  exact hex.choose_spec

/-- Closing under right factors and the actual ambient conditional joins is
sufficient for all four conservation clauses. -/
theorem conservative (hj : HasConditionalJoins (LeftDivOrder M)) (S : Submonoid M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
    (hjS : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S) : Conservative S.subtype where
  injective := Subtype.val_injective
  factors x y z he := by
    exact ⟨⟨z, factor_eq x.val y.val z he ▸ hf x.val x.property y.val y.property⟩,rfl⟩
  intersections x y j h z := by
    have div_iff (a b : S) : a.val ∣ b.val ↔ a ∣ b := by
      constructor
      · rintro ⟨c,hc⟩
        exact ⟨⟨c,factor_eq a.val b.val c hc.symm ▸ hf _ a.property _ b.property⟩,
          Subtype.ext hc⟩
      · rintro ⟨c,hc⟩
        exact ⟨c.val,congrArg Subtype.val hc⟩
    have hxy : x.val ∣ j.val ∧ y.val ∣ j.val := by
      have hh := (h j).mpr (dvd_refl _)
      exact ⟨(div_iff x j).mpr hh.1,(div_iff y j).mpr hh.2⟩
    let l : S := ⟨join x.val y.val,hjS _ x.property _ y.property⟩
    have hl := join_spec hj x.val y.val ⟨j.val,hxy⟩
    have hlj : l.val ∣ j.val := (hl _).mp hxy
    have hjl : j.val ∣ l.val := by
      have hc := (hl l.val).mpr (dvd_refl _)
      exact (div_iff j l).mpr ((h l).mp
        ⟨(div_iff x l).mp hc.1,(div_iff y l).mp hc.2⟩)
    have heq : l.val = j.val := @le_antisymm (LeftDivOrder M) _ l.val j.val
      ((LeftDivOrder.le_iff_dvd (M := M) _ _).mpr hlj)
      ((LeftDivOrder.le_iff_dvd (M := M) _ _).mpr hjl)
    change x.val ∣ z ∧ y.val ∣ z ↔ j.val ∣ z
    rw [← heq]
    exact hl z
  common x y h := by
    let l : S := ⟨join x.val y.val,hjS _ x.property _ y.property⟩
    have hl := (join_spec hj x.val y.val h l.val).mpr (dvd_refl _)
    refine ⟨l,?_,?_⟩
    · obtain ⟨c,hc⟩ := hl.1
      exact ⟨⟨c,factor_eq x.val l.val c hc.symm ▸ hf _ x.property _ l.property⟩,
        Subtype.ext hc⟩
    · obtain ⟨c,hc⟩ := hl.2
      exact ⟨⟨c,factor_eq y.val l.val c hc.symm ▸ hf _ y.property _ l.property⟩,
        Subtype.ext hc⟩

variable (hj : HasConditionalJoins (LeftDivOrder M))
variable (s : Set M) (deps : M → Set M)

def operations (x y : M) : Set M := {x*y,factor x y,join x y} ∪ deps x

def seed : Set M := insert 1 s

def submonoid : Submonoid M where
  carrier := CountableHull.carrier (seed s) (operations deps)
  one_mem' := CountableHull.subset_carrier _ _ (Set.mem_insert 1 _)
  mul_mem' hx hy := CountableHull.closed _ _ hx hy (Or.inl (Set.mem_insert _ _))

omit [IsConical M] in
theorem contains : s ⊆ submonoid s deps :=
  fun _ h => CountableHull.subset_carrier _ _ (Set.mem_insert_of_mem _ h)

omit [IsConical M] in
theorem countable (hs : s.Countable) (hd : ∀ x, (deps x).Countable) :
    (submonoid s deps : Set M).Countable := by
  apply CountableHull.countable _ _ (hs.insert 1)
  intro x y
  exact ((Set.countable_singleton _).insert _ |>.insert _).union (hd x)

omit [IsConical M] in
theorem closed_deps {x : M} (hx : x ∈ submonoid s deps) :
    deps x ⊆ submonoid s deps := by
  intro y hy
  exact CountableHull.closed _ _ hx (submonoid s deps).one_mem (Or.inr hy)

include hj in
theorem inclusion_conservative : Conservative (submonoid s deps).subtype := by
  apply conservative hj
  · intro x hx y hy
    exact CountableHull.closed _ _ hx hy (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · intro x hx y hy
    exact CountableHull.closed _ _ hx hy
      (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

include hj in
/-- Countable conservative hulls exist inside the same monoid and can be
required to contain the countably many dependencies of each retained element.
This is not yet the reordering of the original generator/relator schedule. -/
theorem exists_countable_conservative (hs : s.Countable) (hd : ∀ x, (deps x).Countable) :
    ∃ S : Submonoid M, (S : Set M).Countable ∧ s ⊆ S ∧
      Conservative S.subtype ∧ ∀ x ∈ S, deps x ⊆ S :=
  ⟨submonoid s deps,countable s deps hs hd,contains s deps,
    inclusion_conservative hj s deps,fun _ hx => closed_deps s deps hx⟩

end ConservativeHull
end
end PartitionConsistency.DiagramOrder


/-! ## ConservativeCategory -/

/-! Conservative monoids without height/cost bookkeeping. The original
saturated tower forgets to this category. It is used for rearrangements:
heights are needed for scheduling ideals, but not for old-gate descent. -/
namespace PartitionConsistency.DiagramOrder
universe u
instance {M : Type u} [LeftCancelMonoid M] (S : Submonoid M) : LeftCancelMonoid S where
  toMonoid := inferInstance
  toIsLeftCancelMul := inferInstance
end PartitionConsistency.DiagramOrder

namespace PartitionConsistency.ConservativeMonoids
universe u v w
open DiagramOrder CategoryTheory CategoryTheory.Limits
noncomputable section

structure Object where
  Carrier : Type u
  [monoid : LeftCancelMonoid Carrier]
  [conical : IsConical Carrier]
  joins : HasConditionalJoins (LeftDivOrder Carrier)

instance : CoeSort Object.{u} (Type u) := ⟨Object.Carrier⟩
attribute [instance] Object.monoid Object.conical

structure Hom (M : Object.{u}) (N : Object.{v}) extends M →* N where
  conservative : Conservative toMonoidHom

instance {M : Object.{u}} {N : Object.{v}} : CoeFun (Hom M N) (fun _ => M → N) :=
  ⟨fun f => f.toMonoidHom⟩
namespace Hom
variable {M : Object.{u}} {N : Object.{v}} {R : Object.{w}}

@[ext] theorem ext {f g : Hom M N} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr 1
  exact MonoidHom.ext h

def id (M : Object.{u}) : Hom M M := ⟨MonoidHom.id M,Conservative.id M⟩
def comp (g : Hom N R) (f : Hom M N) : Hom M R :=
  ⟨g.toMonoidHom.comp f.toMonoidHom,f.conservative.comp g.conservative⟩

@[simp] theorem id_apply (x : M) : (id M) x = x := rfl
@[simp] theorem comp_apply (g : Hom N R) (f : Hom M N) (x : M) :
    (g.comp f) x = g (f x) := rfl
@[simp] theorem id_comp (f : Hom M N) : (id N).comp f = f := by ext; rfl
@[simp] theorem comp_id (f : Hom M N) : f.comp (id M) = f := by ext; rfl

theorem injective (f : Hom M N) : Function.Injective f := f.conservative.injective
end Hom

instance : Category Object.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := by intros; apply Hom.ext; intro; rfl
  comp_id := by intros; apply Hom.ext; intro; rfl
  assoc := by intros; apply Hom.ext; intro; rfl

instance (M N : Object.{u}) : CoeFun (M ⟶ N) (fun _ => M → N) := ⟨fun f => f.toMonoidHom⟩

def forgetMargins : MonoidConstruction.Object.{u} ⥤ Object.{u} where
  obj M := ⟨M,M.joins⟩
  map f := ⟨f.toMonoidHom,f.conservative⟩

namespace DirectedColimit
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ Object.{u})

abbrev Carrier (i : J) : Type u := F.obj i

def transition (i j : J) (h : i ≤ j) : F.obj i →* F.obj j :=
  (F.map (homOfLE h)).toMonoidHom

instance : DirectedSystem (Carrier F) (transition F · · ·) where
  map_self i x := by change (F.map (homOfLE (le_refl i))) x = x; simp [homOfLE_refl,F.map_id]; rfl
  map_map i j k hkj hji x := by
    change (F.map (homOfLE hji)) ((F.map (homOfLE hkj)) x) = _
    exact congrArg (fun g : F.obj k ⟶ F.obj i => g x)
      (F.map_comp (homOfLE hkj) (homOfLE hji)).symm

omit [IsDirectedOrder J] [Nonempty J] in
theorem conservative (i j : J) (h : i ≤ j) : Conservative (transition F i j h) :=
  (F.map (homOfLE h)).conservative

abbrev Limit := DirectLimit (Carrier F) (transition F)

def old (i : J) : F.obj i →* Limit F := ConservativeLimit.of (transition F) i

theorem old_map (i j : J) (h : i ≤ j) (x : F.obj i) :
    old F j (F.map (homOfLE h) x) = old F i x :=
  ConservativeLimit.of_map (transition F) i j h x

def object : Object.{u} where
  Carrier := Limit F
  monoid := inferInstance
  conical := inferInstance
  joins := ConservativeLimit.conditionalJoins (transition F) (conservative F) (fun i => (F.obj i).joins)

def inclusion (i : J) : F.obj i ⟶ object F :=
  ⟨old F i,ConservativeLimit.of_conservative (transition F) (conservative F) i⟩

def cocone : Cocone F where
  pt := object F
  ι := {
    app := inclusion F
    naturality := by
      intro i j f
      apply Hom.ext
      intro x
      exact old_map F i j (leOfHom f) x }

variable (C : Cocone F)

def liftFun : object F → C.pt :=
  DirectLimit.lift (transition F) (fun i => C.ι.app i)
    (fun i _ h x => (congrArg (fun f : F.obj i ⟶ C.pt => f x)
      (C.ι.naturality (homOfLE h))).symm)

@[simp] theorem lift_old (i : J) (x : F.obj i) : liftFun F C (old F i x) = C.ι.app i x := rfl

def liftMonoidHom : object F →* C.pt where
  toFun := liftFun F C
  map_one' := by
    calc
      liftFun F C 1 = liftFun F C (old F (Classical.arbitrary J) 1) :=
        congrArg (liftFun F C) (map_one (old F (Classical.arbitrary J))).symm
      _ = 1 := (C.ι.app (Classical.arbitrary J)).map_one
  map_mul' x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    calc
      liftFun F C (old F i x * old F i y) = liftFun F C (old F i (x * y)) :=
        congrArg (liftFun F C) ((old F i).map_mul x y).symm
      _ = liftFun F C (old F i x) * liftFun F C (old F i y) :=
        (C.ι.app i).map_mul x y

theorem lift_conservative : Conservative (liftMonoidHom F C) where
  injective := by
    intro x y
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    exact congrArg (old F i) ((C.ι.app i).conservative.injective h)
  factors := by
    intro x y z
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    obtain ⟨t,ht⟩ := (C.ι.app i).conservative.factors x y z h
    exact ⟨old F i t,ht⟩
  intersections := by
    intro x y j hj z
    obtain ⟨i,x,y,j,rfl,rfl,rfl⟩ := DirectLimit.exists_eq_mk₃ (transition F) x y j
    have hj' : ∀ t : F.obj i, x ∣ t ∧ y ∣ t ↔ j ∣ t := by
      intro t
      have h := hj (old F i t)
      change old F i x ∣ old F i t ∧ old F i y ∣ old F i t ↔ old F i j ∣ old F i t at h
      simpa only [old,ConservativeLimit.of_dvd_iff (transition F) (conservative F)] using h
    exact (C.ι.app i).conservative.intersections x y j hj' z
  common := by
    intro x y
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    intro h
    obtain ⟨z,hx,hy⟩ := (C.ι.app i).conservative.common x y h
    exact ⟨old F i z,(old F i).map_dvd hx,(old F i).map_dvd hy⟩

def lift : object F ⟶ C.pt := ⟨liftMonoidHom F C,lift_conservative F C⟩

def isColimit : IsColimit (cocone F) where
  desc C := lift F C
  fac C i := by apply Hom.ext; intro x; rfl
  uniq C m hm := by
    apply Hom.ext
    intro x
    obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
    exact congrArg (fun f : F.obj i ⟶ C.pt => f x) (hm i)

variable {N : Type v} [Monoid N]
/-- The same direct limit has its universal property for all monoid maps,
not only maps which preserve divisions and joins. -/
def monoidLift (f : ∀ i, F.obj i →* N)
    (hf : ∀ i j h, (f j).comp (transition F i j h) = f i) : object F →* N where
  toFun := DirectLimit.lift (transition F) (fun i => f i)
    (fun i j h x => (DFunLike.congr_fun (hf i j h) x).symm)
  map_one' := by
    let j : J := Classical.arbitrary J
    change DirectLimit.lift (transition F) (fun i => f i) _ 1 = 1
    rw [← (old F j).map_one]
    exact (f j).map_one
  map_mul' x y := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition F) x y
    change DirectLimit.lift (transition F) (fun i => f i) _ (old F i x * old F i y) = _
    rw [← (old F i).map_mul]
    exact (f i).map_mul x y

@[simp] theorem monoidLift_comp_old (f : ∀ i, F.obj i →* N)
    (hf : ∀ i j h, (f j).comp (transition F i j h) = f i) (i : J) :
    (monoidLift F f hf).comp (old F i) = f i := by ext; rfl

theorem monoidHom_ext {f g : object F →* N}
    (h : ∀ i, f.comp (old F i) = g.comp (old F i)) : f = g := by
  ext x
  obtain ⟨i,y,rfl⟩ := DirectLimit.exists_eq_mk (transition F) x
  exact DFunLike.congr_fun (h i) y

end DirectedColimit

instance {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] :
    HasColimitsOfShape J Object.{u} where
  has_colimit F := ⟨⟨⟨DirectedColimit.cocone F,DirectedColimit.isColimit F⟩⟩⟩

instance {J : Type u} [LinearOrder J] [Nonempty J] : HasIterationOfShape J Object.{u} where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    infer_instance

end
end PartitionConsistency.ConservativeMonoids

end OAI
