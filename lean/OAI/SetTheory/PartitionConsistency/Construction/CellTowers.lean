import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.ConservativeCells

namespace OAI

/-! ## CellRestriction -/

/-! Reflecting a scheduled operation to a conservative subobject that
contains its literal countable parameter set. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramForcing
noncomputable section

namespace Probe
variable {M N : Object.{u}}

@[ext] theorem ext {d c : Probe M} (ha : d.a = c.a) (hb : d.b = c.b)
    (he : d.e = c.e) (hn : d.path.node = c.path.node) : d = c := by
  cases d with | mk a b e hb' he' p =>
    cases c with | mk a' b' e' hb'' he'' q =>
      dsimp only at ha hb he hn
      subst a'; subst b'; subst e'
      cases p; cases q
      congr

/-- No closure-of-path assertion is presumed: divisibility is reflected by
conservation, and the actual countably many nodes are pulled back. -/
theorem exists_preimage (d : Probe N) (f : M ⟶ N)
    (h : d.parameters ⊆ Set.range f) : ∃ c : Probe M, c.map f = d := by
  classical
  obtain ⟨a,ha⟩ := h (show d.a ∈ d.parameters from Or.inl (by simp))
  obtain ⟨b,hb⟩ := h (show d.b ∈ d.parameters from Or.inl (by simp))
  obtain ⟨e,he⟩ := h (show d.e ∈ d.parameters from Or.inl (by simp))
  have hn : ∀ i, ∃ n, f n = d.path.node i :=
    fun i => h (Or.inr ⟨i,rfl⟩)
  choose n hn using hn
  have hzero : n 0 = 1 := f.injective (by rw [hn,d.path.zero,f.map_one])
  have hinc {i j : ℕ} (hij : i ≤ j) : n i ∣ n j :=
    (f.conservative.dvd_iff _ _).mp (by rw [hn,hn]; exact d.path.increasing hij)
  have hbound (i : ℕ) : n i ∣ a :=
    (f.conservative.dvd_iff _ _).mp (by rw [hn,ha]; exact d.path.bounded i)
  have hb' : b ≠ 1 := by intro hh; apply d.b_ne_one; rw [← hb,hh,f.map_one]
  have he' : e ≠ 1 := by intro hh; apply d.e_ne_one; rw [← he,hh,f.map_one]
  let c : Probe M := ⟨a,b,e,hb',he',⟨n,hzero,hinc,hbound⟩⟩
  exact ⟨c,ext ha hb he (funext hn)⟩

end Probe

namespace Merger
variable {M N : Object.{u}}

/-- The finite presentation uses only the displayed starts. Every validity
clause is reflected along the conservative inclusion, not added as a new
hypothesis on the selected prescription. -/
theorem exists_preimage (d : Merger N) (f : M ⟶ N)
    (h : d.parameters ⊆ Set.range f) : ∃ c : Merger M, c.map f = d := by
  classical
  have hs : ∀ i j a b, d.prescription.start i j = some (a,b) →
      ∃ x y, f x = a ∧ f y = b := by
    intro i j a b hab
    obtain ⟨x,hx⟩ := h ⟨i,j,a,b,hab,Or.inl rfl⟩
    obtain ⟨y,hy⟩ := h ⟨i,j,a,b,hab,Or.inr rfl⟩
    exact ⟨x,y,hx,hy⟩
  let start (i j : Fin d.n) : Option (M × M) :=
    match he : d.prescription.start i j with
    | none => none
    | some (a,b) => some ((hs i j a b he).choose,(hs i j a b he).choose_spec.choose)
  let P : OverlapPrescription M d.n := ⟨start⟩
  have hm : P.map f.toMonoidHom = d.prescription := by
    have heq : (P.map f.toMonoidHom).start = d.prescription.start := by
      funext i j
      change (start i j).map _ = d.prescription.start i j
      dsimp only [start]
      split
      · rename_i he
        simp only [Option.map_none,he]
      · rename_i a b he
        simp only [he,Option.map_some,Option.some.injEq]
        exact Prod.ext (hs i j a b he).choose_spec.choose_spec.1
          (hs i j a b he).choose_spec.choose_spec.2
    exact congrArg OverlapPrescription.mk heq
  have hp : P.Valid := P.valid_of_map f.conservative (hm ▸ d.valid)
  let c : Merger M := ⟨d.n,P,hp⟩
  refine ⟨c,?_⟩
  have heq : Merger.mk d.n (P.map f.toMonoidHom)
      (P.valid_map hp M.joins f.conservative) = Merger.mk d.n d.prescription d.valid := by
    congr 1
  exact heq.trans (by cases d; rfl)

end Merger

namespace Cell
variable {M N : Object.{u}}

theorem exists_preimage (d : Cell N) (f : M ⟶ N)
    (h : d.parameters ⊆ Set.range f) : ∃ c : Cell M, c.map f = d := by
  cases d with
  | inl d =>
    obtain ⟨c,hc⟩ := d.exists_preimage f h
    exact ⟨.inl c,congrArg Sum.inl hc⟩
  | inr d =>
    obtain ⟨c,hc⟩ := d.exists_preimage f h
    exact ⟨.inr c,congrArg Sum.inr hc⟩

/-- In particular, every parameter-containing conservative subobject admits
the same actual operation. -/
theorem exists_restriction (d : Cell M) (S : Subobject M)
    (h : d.parameters ⊆ S.submonoid) :
    ∃ c : Cell S.object, c.map S.inclusion = d :=
  d.exists_preimage S.inclusion (fun x hx => ⟨⟨x,h hx⟩,rfl⟩)

end Cell
end
end PartitionConsistency.ConservativeMonoids


/-! ## CellularTower -/

/-! Cellular towers inside their actual terminal monoid. The countable hull
retains literal generators and finite old coefficients. -/
namespace PartitionConsistency.DiagramOrder.Conservative
universe u v
variable {M : Type u} {N : Type v} [LeftCancelMonoid M] [IsConical M]
  [LeftCancelMonoid N] [IsConical N]

omit [IsConical M] [IsConical N] in
/-- A monoid isomorphism preserves all four conservation conditions. -/
theorem of_mulEquiv (e : M ≃* N) : Conservative e.toMonoidHom where
  injective := e.injective
  factors x y z _ := ⟨e.symm z,e.apply_symm_apply z⟩
  intersections x y j h z := by
    obtain ⟨w,rfl⟩ := e.surjective z
    change (e x ∣ e w ∧ e y ∣ e w ↔ e j ∣ e w)
    simpa only [map_dvd_iff] using h w
  common x y h := by
    obtain ⟨z,hx,hy⟩ := h
    obtain ⟨w,rfl⟩ := e.surjective z
    exact ⟨w, (map_dvd_iff e).mp hx, (map_dvd_iff e).mp hy⟩
end PartitionConsistency.DiagramOrder.Conservative

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramOrder.ConservativeHull CategoryTheory MonoidPushout
noncomputable section
open scoped Classical

def ofMulEquiv {M N : Object.{u}} (e : M ≃* N) : M ⟶ N :=
  ⟨e.toMonoidHom,Conservative.of_mulEquiv e⟩

namespace Subobject
variable {T : Object.{u}}

@[ext] theorem ext {S R : Subobject T} (h : S.submonoid = R.submonoid) : S = R := by
  cases S; cases R; cases h; rfl

def top : Subobject T where
  submonoid := ⊤
  factors := by intros; trivial
  joins := by intros; trivial

def hom {S R : Subobject T} (h : S.submonoid ≤ R.submonoid) : S.object ⟶ R.object :=
  ⟨Submonoid.inclusion h,Conservative.of_comp R.inclusion.conservative
    (show Conservative (R.inclusion.toMonoidHom.comp (Submonoid.inclusion h)) from
      S.inclusion.conservative)⟩

@[simp] theorem hom_apply {S R : Subobject T} (h : S.submonoid ≤ R.submonoid)
    (x : S.object) : (hom h x).val = x.val := rfl

end Subobject
/-- An actual presentation cell, identified with a subobject of the very
same terminal monoid. The identification fixes every old element. -/
structure Attachment {T : Object.{u}} (S R : Subobject T) where
  cell : Cell S.object
  equiv : cell.extension ≃* R.object
  old : ∀ x : S.object, (equiv (cell.inclusion x)).val = x.val

namespace Attachment
variable {T : Object.{u}} {S R : Subobject T} (d : Attachment S R)

def embedding : d.cell.extension ⟶ T := R.inclusion.comp (ofMulEquiv d.equiv)

def generator (i : d.cell.Generators) : T := d.embedding (d.cell.generator i)

def parameters : Set T := S.inclusion '' d.cell.parameters

@[simp] theorem embedding_old (x : S.object) : d.embedding (d.cell.inclusion x) = x.val :=
  d.old x

theorem parameters_countable : d.parameters.Countable :=
  d.cell.parameters_countable.image _

include d in
theorem old_le : S.submonoid ≤ R.submonoid := by
  intro x hx
  have hh := (d.equiv (d.cell.inclusion ⟨x,hx⟩)).property
  change d.embedding (d.cell.inclusion ⟨x,hx⟩) ∈ R.submonoid at hh
  erw [d.embedding_old] at hh
  exact hh

/-- A retained word has a finite list of old coefficients, even in a
countably presented cell. -/
theorem finite_coefficients (x : R.object) :
    ∃ s : Finset S.object, x.val ∈ Submonoid.closure
      (S.inclusion '' (s : Set S.object) ∪ Set.range d.generator) := by
  obtain ⟨s,hs⟩ := d.cell.finite_coefficients (d.equiv.symm x)
  refine ⟨s,?_⟩
  let Q := Submonoid.closure (S.inclusion '' (s : Set S.object) ∪ Set.range d.generator)
  have h : Submonoid.closure (d.cell.inclusion '' (s : Set S.object) ∪
      Set.range d.cell.generator) ≤ Q.comap d.embedding.toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro z (⟨y,hy,rfl⟩ | ⟨i,rfl⟩)
    · change d.embedding (d.cell.inclusion y) ∈ Q
      rw [d.embedding_old]
      exact Submonoid.subset_closure (Or.inl ⟨y,hy,rfl⟩)
    · exact Submonoid.subset_closure (Or.inr ⟨i,rfl⟩)
  have hh := h hs
  change (d.equiv (d.equiv.symm x)).val ∈ Q at hh
  simpa only [d.equiv.apply_symm_apply] using hh

end Attachment

variable (T : Object.{u}) (J : Type u) [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J]

/-- The original construction as a continuous tower of literal cells.
Identity steps are allowed, so a selected or an omitted subconstruction can
keep the same index order without compressing its limit cuts. -/
structure CellTower where
  stage : J → Subobject T
  mono : Monotone (fun i => (stage i).submonoid)
  terminal : (stage ⊤).submonoid = ⊤
  continuous : ∀ i, Order.IsSuccLimit i → ∀ x, x ∈ (stage i).submonoid →
    ∃ j < i, x ∈ (stage j).submonoid
  step : ∀ i, (stage i).submonoid = (stage (Order.succ i)).submonoid ∨
    Nonempty (Attachment (stage i) (stage (Order.succ i)))

namespace CellTower
variable {T J} (D : CellTower T J)

/-- The unique original successor where an element first appears. -/
def NewAt (i : J) (x : T) : Prop :=
  x ∈ (D.stage (Order.succ i)).submonoid ∧ x ∉ (D.stage i).submonoid

omit [OrderBot J] [WellFoundedLT J] in
theorem NewAt.not_isMax {i : J} {x : T} (h : D.NewAt i x) : ¬ IsMax i := by
  intro hi
  exact h.2 ((show Order.succ i = i from Order.succ_eq_iff_isMax.mpr hi) ▸ h.1)

omit [OrderBot J] [WellFoundedLT J] in
theorem NewAt.neq {i : J} {x : T} (h : D.NewAt i x) :
    (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid := by
  intro he
  exact h.2 (he ▸ h.1)

omit [OrderBot J] [WellFoundedLT J] in
theorem NewAt.unique {i j : J} {x : T} (hi : D.NewAt i x) (hj : D.NewAt j x) : i = j := by
  apply le_antisymm
  · by_contra h
    have hd := (Order.succ_le_iff_of_not_isMax (hj.not_isMax D)).mpr (lt_of_not_ge h)
    exact hi.2 (D.mono hd hj.1)
  · by_contra h
    have hd := (Order.succ_le_iff_of_not_isMax (hi.not_isMax D)).mpr (lt_of_not_ge h)
    exact hj.2 (D.mono hd hi.1)

theorem exists_newAt {x : T} (hx : x ∉ (D.stage ⊥).submonoid) : ∃ i, D.NewAt i x := by
  have hex : {i | x ∈ (D.stage i).submonoid}.Nonempty :=
    ⟨⊤,by change x ∈ (D.stage ⊤).submonoid; rw [D.terminal]; trivial⟩
  let b := wellFounded_lt.min _ hex
  have hb : x ∈ (D.stage b).submonoid := wellFounded_lt.min_mem _ hex
  have hmin : ∀ j < b, x ∉ (D.stage j).submonoid := by
    intro j hj hm
    exact (not_lt_of_ge (WellFoundedLT.min_le (show j ∈ {i | x ∈ (D.stage i).submonoid} from hm))) hj
  have key (b : J) : x ∈ (D.stage b).submonoid →
      (∀ j < b, x ∉ (D.stage j).submonoid) → ∃ i, D.NewAt i x := by
    induction b using SuccOrder.limitRecOn with
    | isMin i hi => intro hb _; exact (hx (hi.eq_bot ▸ hb)).elim
    | succ i hi _ => intro hb hmin; exact ⟨i,hb,hmin i (Order.lt_succ_of_not_isMax hi)⟩
    | isSuccLimit i hi _ =>
      intro hb hmin
      obtain ⟨j,hj,hm⟩ := D.continuous i hi x hb
      exact (hmin j hj hm).elim
  exact key b hb hmin

omit [WellFoundedLT J]

def newIndex (x : T) : J := if h : ∃ i, D.NewAt i x then h.choose else ⊥

theorem newIndex_eq {x : T} {i : J} (h : D.NewAt i x) : D.newIndex x = i := by
  have he : ∃ j, D.NewAt j x := ⟨i,h⟩
  rw [newIndex,dite_eq_left he]
  exact NewAt.unique D he.choose_spec h

/-- The chosen cell at an active stage is independent of the queried word. -/
def stepCell (i : J) (h : (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid) :
    Attachment (D.stage i) (D.stage (Order.succ i)) := ((D.step i).resolve_left h).some

def coefficients (i : J) (h : (D.stage i).submonoid ≠ (D.stage (Order.succ i)).submonoid)
    (x : (D.stage (Order.succ i)).object) : Finset (D.stage i).object :=
  ((D.stepCell i h).finite_coefficients x).choose

def dependencies (x : T) : Set T :=
  if h : D.NewAt (D.newIndex x) x then
    (D.stepCell (D.newIndex x) (h.neq D)).parameters ∪
      Set.range (D.stepCell (D.newIndex x) (h.neq D)).generator ∪
      (D.stage (D.newIndex x)).inclusion ''
        (D.coefficients (D.newIndex x) (h.neq D) ⟨x,h.1⟩ : Set (D.stage (D.newIndex x)).object)
  else ∅

theorem dependencies_countable (x : T) : (D.dependencies x).Countable := by
  classical
  rw [dependencies]
  split
  · exact ((Attachment.parameters_countable _).union (Set.countable_range _)).union
      (Set.Countable.image (Finset.countable_toSet _) _)
  · exact Set.countable_empty

theorem dependencies_at {i : J} {x : T} (h : D.NewAt i x) :
    D.dependencies x = (D.stepCell i (h.neq D)).parameters ∪
      Set.range (D.stepCell i (h.neq D)).generator ∪
      (D.stage i).inclusion '' (D.coefficients i (h.neq D) ⟨x,h.1⟩ :
        Set (D.stage i).object) := by
  have hi := D.newIndex_eq h
  subst i
  rw [dependencies,dite_eq_left h]

/-- Close under dependencies as well as factors and actual conditional
joins. This is a submonoid of the terminal monoid, not a substitute monoid. -/
def hull (s : Set T) : Subobject T where
  submonoid := ConservativeHull.submonoid (s ∪ (D.stage ⊥).submonoid) D.dependencies
  factors _ hx _ hy := CountableHull.closed _ _ hx hy
    (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  joins _ hx _ hy := CountableHull.closed _ _ hx hy
    (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem hull_countable {s : Set T} (hs : s.Countable)
    (hb : ((D.stage ⊥).submonoid : Set T).Countable) :
    ((D.hull s).submonoid : Set T).Countable :=
  ConservativeHull.countable _ _ (hs.union hb) D.dependencies_countable

theorem subset_hull (s : Set T) : s ⊆ (D.hull s).submonoid :=
  fun _ hx => ConservativeHull.contains _ _ (Or.inl hx)

theorem bottom_le_hull (s : Set T) : (D.stage ⊥).submonoid ≤ (D.hull s).submonoid :=
  fun _ hx => ConservativeHull.contains _ _ (Or.inr hx)

theorem hull_closed {s : Set T} {x : T} (hx : x ∈ (D.hull s).submonoid) :
    D.dependencies x ⊆ (D.hull s).submonoid := ConservativeHull.closed_deps _ _ hx

end CellTower
end
end PartitionConsistency.ConservativeMonoids

end OAI
