import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.ConservativeHulls

namespace OAI

/-! ## ConservativeIntersections -/

/-! The intersections used when a presentation is restricted to a countable
hull. This establishes conservation at arbitrary cuts, not just selected cuts. -/
namespace PartitionConsistency.DiagramOrder.Conservative
universe u v w
open ConservativeHull
noncomputable section
variable {A : Type u} {B : Type v} {C : Type w}
variable [LeftCancelMonoid A] [IsConical A] [LeftCancelMonoid B] [IsConical B]
  [LeftCancelMonoid C] [IsConical C]
variable {f : A →* B} (hf : Conservative f)

omit [IsConical A] [IsConical B] in
include hf in
theorem map_factor (x y : A) : f (factor x y) = factor (f x) (f y) := by
  by_cases h : x ∣ y
  · exact (ConservativeHull.factor_eq (f x) (f y) (f (factor x y)) (by
      rw [← map_mul, factor, dite_eq_left h]; exact congrArg f h.choose_spec.symm)).symm
  · have h' := mt (hf.dvd_iff x y).mp h
    simp only [factor,dite_eq_right h,dite_eq_right h',f.map_one]

include hf in
/-- The selected conditional join (or the identity for disjoint cones) is
preserved literally by every conservative map of conditional-join monoids. -/
theorem map_join (hA : HasConditionalJoins (LeftDivOrder A))
    (hB : HasConditionalJoins (LeftDivOrder B)) (x y : A) :
    f (join x y) = join (f x) (f y) := by
  by_cases h : ∃ z : A, x ∣ z ∧ y ∣ z
  · have h' : ∃ z : B, f x ∣ z ∧ f y ∣ z := (hf.common_iff x y).mpr h
    have hl := hf.intersections x y (join x y) (join_spec hA x y h)
    have hr := join_spec hB (f x) (f y) h'
    apply @le_antisymm (LeftDivOrder B) _
    · exact (LeftDivOrder.le_iff_dvd _ _).mpr ((hl _).mp ((hr _).mpr (dvd_refl _)))
    · exact (LeftDivOrder.le_iff_dvd _ _).mpr ((hr _).mp ((hl _).mpr (dvd_refl _)))
  · have h₀ : ¬ ∃ j : A, ∀ z : A, x ∣ z ∧ y ∣ z ↔ j ∣ z := by
      rintro ⟨j,hj⟩; exact h ⟨j,(hj j).mpr (dvd_refl j)⟩
    have h₁ : ¬ ∃ j : B, ∀ z : B, f x ∣ z ∧ f y ∣ z ↔ j ∣ z := by
      rintro ⟨j,hj⟩; exact h (hf.common x y ⟨j,(hj j).mpr (dvd_refl j)⟩)
    simp only [join,dite_eq_right h₀,dite_eq_right h₁,f.map_one]

omit [IsConical A] [IsConical B] [IsConical C] in
/-- Conservation reflects through a conservative final embedding. -/
theorem of_comp {g : B →* C} (hg : Conservative g) (hgf : Conservative (g.comp f)) :
    Conservative f where
  injective := by intro x y h; exact hgf.injective (congrArg g h)
  factors x y z h := by
    obtain ⟨t,ht⟩ := hgf.factors x y (g z) (by
      change g (f x) * g z = g (f y); rw [← g.map_mul,h])
    exact ⟨t,hg.injective ht⟩
  intersections x y j hj z := by
    have h := hgf.intersections x y j hj (g z)
    change g (f x) ∣ g z ∧ g (f y) ∣ g z ↔ g (f j) ∣ g z at h
    simpa only [hg.dvd_iff] using h
  common x y h := by
    obtain ⟨z,hx,hy⟩ := h
    exact hgf.common x y ⟨g z,g.map_dvd hx,g.map_dvd hy⟩

end
end PartitionConsistency.DiagramOrder.Conservative

namespace PartitionConsistency.DiagramOrder.ConservativeHull
universe u
noncomputable section
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]
variable (hj : HasConditionalJoins (LeftDivOrder M)) (S : Submonoid M)
variable (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
  (hc : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S)

include hj hf hc
/-- A submonoid closed under the uniquely determined factors and joins has
conditional joins of its own. -/
theorem conditionalJoins : HasConditionalJoins (LeftDivOrder S) := by
  intro x y z hx hy
  let l : S := ⟨join x.val y.val,hc _ x.property _ y.property⟩
  have hco := conservative hj S hf hc
  have h := join_spec hj x.val y.val
    ⟨z.val,S.subtype.map_dvd ((LeftDivOrder.le_iff_dvd _ _).mp hx),
      S.subtype.map_dvd ((LeftDivOrder.le_iff_dvd _ _).mp hy)⟩
  refine ⟨l,(pair_lub_iff (α := LeftDivOrder S) x y l).mpr ?_⟩
  intro w
  rw [LeftDivOrder.le_iff_dvd (M := S) x w,
    LeftDivOrder.le_iff_dvd (M := S) y w, LeftDivOrder.le_iff_dvd (M := S) l w]
  change ((x : S) ∣ (w : S)) ∧ ((y : S) ∣ (w : S)) ↔ l ∣ (w : S)
  exact ((hco.dvd_iff x w).symm.and (hco.dvd_iff y w).symm).trans
    ((h w.val).trans (hco.dvd_iff l w))

end
end PartitionConsistency.DiagramOrder.ConservativeHull

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramOrder.ConservativeHull
noncomputable section
variable {M : Object.{u}}

/-- Closure under factors and ambient joins supplies a genuine object. -/
def closedObject (S : Submonoid M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S) : Object.{u} :=
  ⟨S,conditionalJoins M.joins S hf hc⟩

def closedInclusion (S : Submonoid M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, factor x y ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, join x y ∈ S) :
    closedObject S hf hc ⟶ M := ⟨S.subtype,conservative M.joins S hf hc⟩

/-- A conservative subobject can equivalently be specified by its carrier
submonoid and its two countably-ary closure requirements. -/
structure Subobject (M : Object.{u}) where
  submonoid : Submonoid M
  factors : ∀ x ∈ submonoid, ∀ y ∈ submonoid, factor x y ∈ submonoid
  joins : ∀ x ∈ submonoid, ∀ y ∈ submonoid, join x y ∈ submonoid

namespace Subobject

def object (S : Subobject M) : Object.{u} := closedObject S.submonoid S.factors S.joins

def inclusion (S : Subobject M) : S.object ⟶ M :=
  closedInclusion S.submonoid S.factors S.joins

/-- Conservative intersections exist at every original tower cut. -/
def inf (S R : Subobject M) : Subobject M where
  submonoid := S.submonoid ⊓ R.submonoid
  factors _ hx _ hy := ⟨S.factors _ hx.1 _ hy.1,R.factors _ hx.2 _ hy.2⟩
  joins _ hx _ hy := ⟨S.joins _ hx.1 _ hy.1,R.joins _ hx.2 _ hy.2⟩

/-- Pulling a retained submonoid back to an original stage also preserves
all the conservation requirements. -/
def comap {N : Object.{u}} (S : Subobject N) (f : M ⟶ N) : Subobject M where
  submonoid := S.submonoid.comap f.toMonoidHom
  factors x hx y hy := by
    change f (factor x y) ∈ S.submonoid
    rw [f.conservative.map_factor]
    exact S.factors _ hx _ hy
  joins x hx y hy := by
    change f (join x y) ∈ S.submonoid
    rw [f.conservative.map_join M.joins N.joins]
    exact S.joins _ hx _ hy

/-- Images of actual conservative maps are conservative subobjects. -/
def range {N : Object.{u}} (f : M ⟶ N) : Subobject N where
  submonoid := MonoidHom.mrange f.toMonoidHom
  factors := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact ⟨factor x y,f.conservative.map_factor x y⟩
  joins := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact ⟨join x y,f.conservative.map_join M.joins N.joins x y⟩

end Subobject
end
end PartitionConsistency.ConservativeMonoids


/-! ## Cell -/

/-! The actual countably presented operations, with their conservative
simulations and finite coefficient supports. These are the cells in the
original schedule, forgetting only the height/cost bookkeeping. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramForcing MonoidPushout
noncomputable section

structure Probe (M : Object.{u}) where
  a : M
  b : M
  e : M
  b_ne_one : b ≠ 1
  e_ne_one : e ≠ 1
  path : ProbeAlgebra.Path M a

namespace Probe
variable {M N : Object.{u}} (d : Probe M)

def extension : Object.{u} where
  Carrier := d.path.Extension d.e_ne_one d.b
  monoid := inferInstance
  conical := inferInstance
  joins := d.path.extension_hasConditionalJoins d.e_ne_one d.b M.joins d.b_ne_one

def inclusion : M ⟶ d.extension :=
  ⟨ProbeAlgebra.Word.oldHom (d.path.alphabet d.e_ne_one) d.b,
    d.path.oldHom_conservative d.e_ne_one d.b⟩

def generator (i : ℕ) : d.extension := d.path.probe d.e_ne_one d.b d.b_ne_one i

def map (f : M ⟶ N) : Probe N :=
  ⟨f d.a,f d.b,f d.e,(fun h => d.b_ne_one (f.injective (h.trans f.map_one.symm))),
    (fun h => d.e_ne_one (f.injective (h.trans f.map_one.symm))),d.path.map f.toMonoidHom⟩

def simulation (f : M ⟶ N) : d.extension ⟶ (d.map f).extension :=
  ⟨d.path.simulation d.e_ne_one f.conservative d.b,
    d.path.simulation_conservative d.e_ne_one f.conservative d.b M.joins d.b_ne_one⟩

@[simp] theorem simulation_inclusion (f : M ⟶ N) (x : M) :
    d.simulation f (d.inclusion x) = (d.map f).inclusion (f x) := rfl

@[simp] theorem simulation_generator (f : M ⟶ N) (i : ℕ) :
    d.simulation f (d.generator i) = (d.map f).generator i :=
  d.path.simulation_probe d.e_ne_one f.conservative d.b d.b_ne_one i

theorem pushout (f : M ⟶ N) :
    IsPushout d.inclusion.toMonoidHom f.toMonoidHom (d.simulation f).toMonoidHom
      (d.map f).inclusion.toMonoidHom :=
  d.path.simulation_pushout d.e_ne_one f.conservative d.b d.b_ne_one

theorem gates : HasOldGates d.inclusion.toMonoidHom :=
  d.path.hasOldGates d.e_ne_one d.b M.joins

/-- An extension is generated by the whole old monoid and its countably
many displayed generators. This is proved from the literal presentation. -/
theorem generated (S : Submonoid d.extension)
    (ho : ∀ x : M, d.inclusion x ∈ S) (hn : ∀ i, d.generator i ∈ S) : S = ⊤ := by
  let f : M →* S :=
    { toFun := fun x => ⟨d.inclusion x,ho x⟩
      map_one' := Subtype.ext d.inclusion.map_one
      map_mul' x y := Subtype.ext (d.inclusion.map_mul x y) }
  let p : ℕ → S := fun i => ⟨d.generator i,hn i⟩
  have hp : ∀ i, p i = f (d.path.factor i (i+1) (Nat.le_succ i)) * p (i+1) := by
    intro i
    apply Subtype.ext
    exact (d.path.probe_transition d.e_ne_one d.b d.b_ne_one (Nat.le_succ i)).symm
  have hx : ∀ i, p i * f d.b = f (d.path.terminal i * d.e) := by
    intro i
    apply Subtype.ext
    exact d.path.probe_mul_b d.e_ne_one d.b d.b_ne_one i
  let l := d.path.presentedLift d.e_ne_one d.b f p hp hx
  have h : S.subtype.comp l = MonoidHom.id d.extension := by
    apply d.path.presentedHom_ext d.e_ne_one d.b d.b_ne_one
    · intro x; rfl
    · intro i
      change (l (d.generator i)).val = d.generator i
      rw [show l (d.generator i) = p i from
        d.path.presentedLift_probe d.e_ne_one d.b f p hp hx d.b_ne_one i]
  apply top_unique
  intro x _
  have hh := (l x).property
  rwa [show (l x).val = x from DFunLike.congr_fun h x] at hh

/-- Only these countably many old elements are needed to specify a probe
cell; factors along the path belong to every conservative subobject that
contains the displayed endpoints. -/
def parameters : Set M := {d.a,d.b,d.e} ∪ Set.range d.path.node

theorem parameters_countable : d.parameters.Countable :=
  (Set.toFinite ({d.a,d.b,d.e} : Set M)).countable.union (Set.countable_range _)

end Probe

structure Merger (M : Object.{u}) where
  n : ℕ
  prescription : OverlapPrescription M n
  valid : prescription.Valid

namespace Merger
variable {M N : Object.{u}} (d : Merger M)

def extension : Object.{u} where
  Carrier := d.prescription.Merger d.valid
  monoid := inferInstance
  conical := inferInstance
  joins := d.prescription.merger_hasConditionalJoins d.valid M.joins

def inclusion : M ⟶ d.extension :=
  ⟨MergerAlgebra.Word.oldHom,MergerAlgebra.Word.oldHom_conservative⟩

def generator (i : Fin d.n) : d.extension := d.prescription.root d.valid i

def map (f : M ⟶ N) : Merger N :=
  ⟨d.n,d.prescription.map f.toMonoidHom,d.prescription.valid_map d.valid M.joins f.conservative⟩

def simulation (f : M ⟶ N) : d.extension ⟶ (d.map f).extension :=
  ⟨d.prescription.mergerSimulation d.valid M.joins f.conservative,
    d.prescription.mergerSimulation_conservative d.valid M.joins f.conservative⟩

@[simp] theorem simulation_inclusion (f : M ⟶ N) (x : M) :
    d.simulation f (d.inclusion x) = (d.map f).inclusion (f x) := rfl

@[simp] theorem simulation_generator (f : M ⟶ N) (i : Fin d.n) :
    d.simulation f (d.generator i) = (d.map f).generator i :=
  d.prescription.mergerSimulation_root d.valid M.joins f.conservative i

theorem pushout (f : M ⟶ N) :
    IsPushout d.inclusion.toMonoidHom f.toMonoidHom (d.simulation f).toMonoidHom
      (d.map f).inclusion.toMonoidHom :=
  d.prescription.mergerSimulation_pushout d.valid M.joins f.conservative

theorem gates : HasOldGates d.inclusion.toMonoidHom := MergerAlgebra.Word.hasOldGates

theorem generated (S : Submonoid d.extension)
    (ho : ∀ x : M, d.inclusion x ∈ S) (hn : ∀ i, d.generator i ∈ S) : S = ⊤ := by
  let f : M →* S :=
    { toFun := fun x => ⟨d.inclusion x,ho x⟩
      map_one' := Subtype.ext d.inclusion.map_one
      map_mul' x y := Subtype.ext (d.inclusion.map_mul x y) }
  let p : Fin d.n → S := fun i => ⟨d.generator i,hn i⟩
  have hp : d.prescription.Satisfies f p := by
    intro i j a b hij hab
    apply Subtype.ext
    exact d.prescription.roots_satisfy d.valid i j a b hij hab
  let l := d.prescription.presentedLift d.valid f p hp
  have h : S.subtype.comp l = MonoidHom.id d.extension := by
    apply d.prescription.presentedHom_ext d.valid
    · intro x; rfl
    · intro i
      change (l (d.generator i)).val = d.generator i
      rw [show l (d.generator i) = p i from
        d.prescription.presentedLift_root d.valid f p hp i]
  apply top_unique
  intro x _
  have hh := (l x).property
  rwa [show (l x).val = x from DFunLike.congr_fun h x] at hh

def parameters : Set M :=
  {x | ∃ i j a b, d.prescription.start i j = some (a,b) ∧ (x = a ∨ x = b)}

theorem parameters_countable : d.parameters.Countable := by
  have h : d.parameters ⊆ Set.range (fun ij : Fin d.n × Fin d.n =>
      ((d.prescription.start ij.1 ij.2).getD (1,1)).1) ∪
    Set.range (fun ij : Fin d.n × Fin d.n =>
      ((d.prescription.start ij.1 ij.2).getD (1,1)).2) := by
    rintro x ⟨i,j,a,b,hab,hx⟩
    rcases hx with rfl | rfl
    · exact Or.inl ⟨(i,j),by simp only [hab,Option.getD_some]⟩
    · exact Or.inr ⟨(i,j),by simp only [hab,Option.getD_some]⟩
  exact ((Set.countable_range _).union (Set.countable_range _)).mono h

end Merger

abbrev Cell (M : Object.{u}) := Probe M ⊕ Merger M

namespace Cell
variable {M N : Object.{u}}

def extension : Cell M → Object.{u}
  | .inl d => d.extension
  | .inr d => d.extension

def inclusion : (d : Cell M) → M ⟶ d.extension
  | .inl d => d.inclusion
  | .inr d => d.inclusion

def Generators : Cell M → Type
  | .inl _ => ℕ
  | .inr d => Fin d.n

instance (d : Cell M) : Countable d.Generators := by cases d <;> dsimp [Generators] <;> infer_instance

def generator : (d : Cell M) → d.Generators → d.extension
  | .inl d => d.generator
  | .inr d => d.generator

def parameters : Cell M → Set M
  | .inl d => d.parameters
  | .inr d => d.parameters

theorem parameters_countable (d : Cell M) : d.parameters.Countable := by
  cases d with
  | inl d => exact d.parameters_countable
  | inr d => exact d.parameters_countable

def map : Cell M → (M ⟶ N) → Cell N
  | .inl d,f => .inl (d.map f)
  | .inr d,f => .inr (d.map f)

def simulation : (d : Cell M) → (f : M ⟶ N) → d.extension ⟶ (d.map f).extension
  | .inl d,f => d.simulation f
  | .inr d,f => d.simulation f

theorem pushout (d : Cell M) (f : M ⟶ N) :
    IsPushout d.inclusion.toMonoidHom f.toMonoidHom (d.simulation f).toMonoidHom
      (d.map f).inclusion.toMonoidHom := by
  cases d with
  | inl d => exact d.pushout f
  | inr d => exact d.pushout f

theorem gates (d : Cell M) : HasOldGates d.inclusion.toMonoidHom := by
  cases d with
  | inl d => exact d.gates
  | inr d => exact d.gates

theorem generated (d : Cell M) (S : Submonoid d.extension)
    (ho : ∀ x : M, d.inclusion x ∈ S) (hn : ∀ i, d.generator i ∈ S) : S = ⊤ := by
  cases d with
  | inl d => exact d.generated S ho hn
  | inr d => exact d.generated S ho hn

theorem mem_closure (d : Cell M) (x : d.extension) :
    x ∈ Submonoid.closure (Set.range d.inclusion ∪ Set.range d.generator) := by
  rw [d.generated _ (fun x => Submonoid.subset_closure (Or.inl ⟨x,rfl⟩))
    (fun i => Submonoid.subset_closure (Or.inr ⟨i,rfl⟩))]
  trivial

/-- The countable list of new generators remains whole, but each particular
word uses just finitely many old coefficients. No finite support is claimed
for the countable path which specifies the cell. -/
theorem finite_coefficients (d : Cell M) (x : d.extension) :
    ∃ s : Finset M, x ∈ Submonoid.closure (d.inclusion '' (s : Set M) ∪ Set.range d.generator) := by
  classical
  apply Submonoid.closure_induction (s := Set.range d.inclusion ∪ Set.range d.generator)
    (motive := fun x _ => ∃ s : Finset M,
      x ∈ Submonoid.closure (d.inclusion '' (s : Set M) ∪ Set.range d.generator))
    ?_ ?_ ?_ (d.mem_closure x)
  · intro y hy
    rcases hy with ⟨a,rfl⟩ | ⟨i,rfl⟩
    · exact ⟨{a},Submonoid.subset_closure (Or.inl ⟨a,by simp,rfl⟩)⟩
    · exact ⟨∅,Submonoid.subset_closure (Or.inr ⟨i,rfl⟩)⟩
  · exact ⟨∅,Submonoid.one_mem _⟩
  · rintro y z _ _ ⟨s,hs⟩ ⟨t,ht⟩
    refine ⟨s ∪ t,Submonoid.mul_mem _ ?_ ?_⟩
    · apply (Submonoid.closure_mono (Set.union_subset_union ?_ Set.Subset.rfl)) hs
      exact Set.image_mono (by intro a ha; exact Finset.mem_union.mpr (Or.inl ha))
    · apply (Submonoid.closure_mono (Set.union_subset_union ?_ Set.Subset.rfl)) ht
      exact Set.image_mono (by intro a ha; exact Finset.mem_union.mpr (Or.inr ha))

end Cell

/-- Forgetting heights takes each executed request to precisely one of the
cells above, not to an object merely satisfying the same axioms. -/
def RequestCell {M : MonoidConstruction.Object.{u}} :
    MonoidConstruction.Request M → Cell (forgetMargins.obj M)
  | .inl d => .inl ⟨d.a,d.b,M.e,d.b_ne_one,M.e_ne_one,d.path⟩
  | .inr d => .inr ⟨d.n,d.prescription,d.valid⟩

end
end PartitionConsistency.ConservativeMonoids

end OAI
