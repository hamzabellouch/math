import OAI.AlgebraicTopology.Cubical.Realization
import OAI.AlgebraicTopology.Cubical.ArtinChains
import OAI.Topology.EilenbergGanea.Model
import OAI.Topology.EilenbergGanea.SeedConnection
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Homotopy.Lifting

namespace OAI

noncomputable section

open Classical Set Topology
open scoped Quaternion

namespace EilenbergGanea.DescendingCube.Data
open CubeInterpolation
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
variable [Fintype A]

omit [Fintype A] in
theorem cellComm (c : D.Cell) : (c.directions : Set A).Pairwise
    (fun a b => Commute (f a) (f b)) :=
  fun _ ha _ hb he => D.commute c.top _ _ (c.subset ha) (c.subset hb) he

omit [Fintype A] in
theorem ones_eq_filter (c : D.Cell) (x : D.Coordinates c) :
    D.ones c x = c.directions.filter (fun a => D.fullCoord c x a = 1) := by
  ext a
  simp only [mem_ones,Finset.mem_filter]
  constructor
  · rintro ⟨ha,hx⟩
    exact ⟨ha,by simpa only [fullCoord,dite_eq_left ha] using hx⟩
  · rintro ⟨ha,hx⟩
    exact ⟨ha,by simpa only [fullCoord,dite_eq_left ha] using hx⟩

omit [Fintype A] in
theorem normalize_fullCoord (c : D.Cell) (x : D.Coordinates c) :
    CubeInterpolation.normalize (D.fullCoord c x) = D.normalizedCoord c x := by
  funext a
  by_cases ha : a ∈ c.directions
  · simp only [CubeInterpolation.normalize,fullCoord,normalizedCoord,dite_eq_left ha]
  · simp [CubeInterpolation.normalize,fullCoord,normalizedCoord,ha]

def interpolation (p : D.Point) (φ : G → ℝ) : ℝ :=
  operator f (D.active p) (D.cellComm (D.pointCell p)) p.coord φ p.top

theorem active_characteristic_subset (c : D.Cell) (x : D.Coordinates c) :
    D.active (D.characteristic c x) ⊆ c.directions := by
  intro a ha
  by_contra h
  apply ((D.mem_active _ _).mp ha)
  change D.normalizedCoord c x a = 0
  simp [normalizedCoord,h]

theorem interpolation_characteristic (c : D.Cell) (x : D.Coordinates c) (φ : G → ℝ) :
    D.interpolation (D.characteristic c x) φ =
      operator f c.directions (D.cellComm c) (D.fullCoord c x) φ c.top := by
  have hsub := D.active_characteristic_subset c x
  have he := operator_subset f (D.active (D.characteristic c x)) c.directions
    (D.cellComm c) hsub (D.normalizedCoord c x) (by
      intro a _ hn
      exact not_not.mp (by simpa only [mem_active,characteristic] using hn))
  have hn := operator_normalize f c.directions (D.cellComm c) (D.fullCoord c x)
  simp only [normalize_fullCoord,← ones_eq_filter] at hn
  have hh := congrArg (fun T : Module.End ℝ (G → ℝ) => T φ c.top) hn
  rw [Module.End.mul_apply,translation_apply,he] at hh
  exact hh.symm

theorem interpolation_continuous (φ : G → ℝ) :
    Continuous (fun p : D.Point => D.interpolation p φ) := by
  apply D.evaluation_quotient.continuous_iff.mpr
  apply continuous_sigma
  intro c
  change Continuous (fun x : D.Coordinates c => D.interpolation (D.characteristic c x) φ)
  simp only [interpolation_characteristic]
  exact operator_continuous f c.directions _ (D.fullCoord c)
    (fun a _ => D.fullCoord_continuous c a) φ c.top

theorem interpolation_vertex_pos (p : D.Point) :
    0 < D.interpolation p (fun a => if a = p.top then 1 else 0) := by
  apply operator_pos
  · intro a _; exact ⟨p.nonneg a,p.lt_one a⟩
  · intro a; split_ifs <;> norm_num
  · simp

omit [Fintype A] in
theorem descending_operator_delta_zero (s : Finset A) (g : G) (hs : s ⊆ D.desc g)
    (x : A → ℝ) (b : G) (hb : D.length g ≤ D.length b) (hne : b ≠ g) :
    operator f s (fun a ha d hd hne => D.commute g a d (hs ha) (hs hd) hne)
      x (fun a => if a = b then 1 else 0) g = 0 := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp [operator_empty,hne.symm]
  | @insert a s ha ih =>
    have hga := hs (Finset.mem_insert_self a s)
    have hs0 : s ⊆ D.desc g := fun d hd => hs (Finset.mem_insert_of_mem hd)
    have hs1 : s ⊆ D.desc (g * f a) := by
      intro d hd
      exact D.preserve g a d hga (hs0 hd) (by intro he; exact ha (he ▸ hd))
    have hd := D.decrease g a hga
    have hb1 : D.length (g*f a) ≤ D.length b := by omega
    have hne1 : b ≠ g*f a := by intro he; rw [he] at hb; omega
    have hc : (↑(insert a s) : Set A).Pairwise (fun a d => Commute (f a) (f d)) :=
      fun _ ha _ hd hne => D.commute g _ _ (hs ha) (hs hd) hne
    change operator f (insert a s) hc x (fun a => if a = b then 1 else 0) g = 0
    rw [operator_insert f s a ha,Module.End.mul_apply,blend_apply]
    rw [ih g hs0 hb hne,ih (g*f a) hs1 hb1 hne1]
    ring

theorem interpolation_vertex_zero (p : D.Point) (b : G)
    (hb : D.length p.top ≤ D.length b) (hne : b ≠ p.top) :
    D.interpolation p (fun a => if a = b then 1 else 0) = 0 :=
  D.descending_operator_delta_zero (D.active p) p.top (D.pointCell p).subset p.coord b hb hne

theorem interpolation_top_eq (p q : D.Point)
    (he : ∀ φ, D.interpolation p φ = D.interpolation q φ) : p.top = q.top := by
  have length_le (p q : D.Point) (he : ∀ φ, D.interpolation p φ = D.interpolation q φ) :
      D.length q.top ≤ D.length p.top := by
    by_contra hn
    have hlt : D.length p.top < D.length q.top := lt_of_not_ge hn
    have hne : q.top ≠ p.top := by intro eq; rw [eq] at hlt; exact lt_irrefl _ hlt
    have hz := D.interpolation_vertex_zero p q.top hlt.le hne
    have hp := D.interpolation_vertex_pos q
    rw [← he,hz] at hp
    exact lt_irrefl _ hp
  have h₁ := length_le p q he
  by_contra hne
  have hz := D.interpolation_vertex_zero q p.top h₁ hne
  have hp := D.interpolation_vertex_pos p
  rw [he,hz] at hp
  exact lt_irrefl _ hp

variable (exponent : A → G →* Multiplicative ℝ)
variable (hexponent : ∀ g a, a ∈ D.desc g → ∀ b, b ∈ D.desc g →
  (exponent a (f b)).toAdd = if a = b then 1 else 0)

include hexponent in
theorem interpolation_exponent (p : D.Point) (a : A) (ha : a ∈ D.desc p.top) :
    D.interpolation p (fun g => (exponent a g).toAdd) =
      (exponent a p.top).toAdd + p.coord a := by
  refine (operator_linear f (exponent a) (D.active p)
    (D.cellComm (D.pointCell p)) p.coord p.top).trans ?_
  congr 1
  have he : ∀ b ∈ D.active p, (exponent a (f b)).toAdd = if a = b then 1 else 0 :=
    fun b hb => hexponent p.top a ha b ((D.pointCell p).subset hb)
  simp only [Finset.sum_congr rfl (fun b hb => congrArg (fun t : ℝ => p.coord b * t) (he b hb)),
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq]
  by_cases h : p.coord a = 0
  · simp [h]
  · simp [mem_active,h]

include exponent hexponent in
theorem interpolation_injective : Function.Injective
    (fun p : D.Point => fun φ : G → ℝ => D.interpolation p φ) := by
  intro p q he
  have he' : ∀ φ, D.interpolation p φ = D.interpolation q φ := fun φ => congrFun he φ
  have hb := D.interpolation_top_eq p q he'
  apply Point.ext hb
  funext a
  by_cases ha : a ∈ D.desc p.top
  · have hq : a ∈ D.desc q.top := by simpa only [hb] using ha
    have hh := he' (fun g => (exponent a g).toAdd)
    rw [D.interpolation_exponent exponent hexponent p a ha,
      D.interpolation_exponent exponent hexponent q a hq,hb] at hh
    exact add_left_cancel hh
  · have hp : p.coord a = 0 := by_contra (fun hn => ha (p.support a hn))
    have hq : q.coord a = 0 := by
      by_contra hn
      exact ha (by simpa only [hb] using q.support a hn)
    rw [hp,hq]

include exponent hexponent in
theorem point_t2 : T2Space D.Point :=
  T2Space.of_injective_continuous
    (D.interpolation_injective exponent hexponent)
    (continuous_pi (fun φ => D.interpolation_continuous φ))

end EilenbergGanea.DescendingCube.Data

open Classical Topology
namespace WeakRealization

/-- A homeomorphism is induced by point-separating coordinates and actual
continuous lifts on each characteristic disk, in both directions. -/
def homeomorph {ι κ X Y Z : Type*} {E : ι → Type*} {F : κ → Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [∀ i, TopologicalSpace (E i)] [∀ j, TopologicalSpace (F j)]
    (e : ((i : ι) × E i) → X) (f : ((j : κ) × F j) → Y)
    (he : IsQuotientMap e) (hf : IsQuotientMap f)
    (J : X → Z) (K : Y → Z) (hJ : Function.Injective J) (hK : Function.Injective K)
    (hxy : ∀ i, ∃ φ : C(E i,Y), ∀ t, K (φ t) = J (e ⟨i,t⟩))
    (hyx : ∀ j, ∃ φ : C(F j,X), ∀ t, J (φ t) = K (f ⟨j,t⟩)) : X ≃ₜ Y := by
  have hx : ∀ x, ∃ y, K y = J x := by
    intro x
    obtain ⟨⟨i,t⟩,rfl⟩ := he.surjective x
    obtain ⟨φ,hφ⟩ := hxy i
    exact ⟨φ t,hφ t⟩
  have hy : ∀ y, ∃ x, J x = K y := by
    intro y
    obtain ⟨⟨j,t⟩,rfl⟩ := hf.surjective y
    obtain ⟨φ,hφ⟩ := hyx j
    exact ⟨φ t,hφ t⟩
  let A : X → Y := fun x => (hx x).choose
  let B : Y → X := fun y => (hy y).choose
  have hA : ∀ x, K (A x) = J x := fun x => (hx x).choose_spec
  have hB : ∀ y, J (B y) = K y := fun y => (hy y).choose_spec
  refine {
    toEquiv := {
      toFun := A
      invFun := B
      left_inv := fun x => hJ ((hB (A x)).trans (hA x))
      right_inv := fun y => hK ((hA (B y)).trans (hB y)) }
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · apply he.continuous_iff.mpr
    apply continuous_sigma
    intro i
    obtain ⟨φ,hφ⟩ := hxy i
    have hh : (fun t => A (e ⟨i,t⟩)) = φ := by
      funext t
      exact hK ((hA _).trans (hφ t).symm)
    change Continuous (fun t => A (e ⟨i,t⟩))
    rw [hh]
    exact φ.continuous
  · apply hf.continuous_iff.mpr
    apply continuous_sigma
    intro j
    obtain ⟨φ,hφ⟩ := hyx j
    have hh : (fun t => B (f ⟨j,t⟩)) = φ := by
      funext t
      exact hJ ((hB _).trans (hφ t).symm)
    change Continuous (fun t => B (f ⟨j,t⟩))
    rw [hh]
    exact φ.continuous

end WeakRealization

namespace EilenbergGanea.CubeInterpolation
open CubicalChains.Reorientation
variable {G V : Type*} [Group G]

/-- Interpolation in a listed cube, independent of any topological model. -/
def listed (f : V → G) (w : List V) (x : V → ℝ) : Module.End ℝ (G → ℝ) :=
  (w.map (fun v => blend (f v) (x v))).prod

@[simp] theorem listed_nil (f : V → G) (x : V → ℝ) : listed f [] x = 1 := rfl
@[simp] theorem listed_cons (f : V → G) (v : V) (w : List V) (x : V → ℝ) :
    listed f (v::w) x = blend (f v) (x v) * listed f w x := rfl

theorem operator_listed [DecidableEq V] (f : V → G) (w : List V) (hw : w.Nodup)
    (hc : (w.toFinset : Set V).Pairwise (fun v u => Commute (f v) (f u))) (x : V → ℝ) :
    operator f w.toFinset hc x = listed f w x :=
  Finset.noncommProd_toFinset w _ _ hw

/-- Literal multilinear invariance under reversing selected cube directions. -/
theorem listed_reorientation (f : V → G) (w : List (Signed V))
    (hw : w.Pairwise (fun a b => Commute (f a.1) (f b.1)))
    (x : Signed V → ℝ) (z : V → ℝ)
    (hx : ∀ a ∈ w, x a = if a.2 then 1-z a.1 else z a.1) (φ : G → ℝ) (g : G) :
    listed (step f) w x φ g = listed f (w.map Prod.fst) z φ (origin f g w) := by
  induction w generalizing g with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨ha,hw⟩ := List.pairwise_cons.mp hw
    have hxw : ∀ b ∈ w, x b = if b.2 then 1-z b.1 else z b.1 :=
      fun b hb => hx b (by simp [hb])
    simp only [listed_cons,List.map_cons,Module.End.mul_apply,blend_apply,
      ih hw hxw,hx a (by simp),step,origin]
    cases hb : a.2
    · simp only [Bool.false_eq_true,↓reduceIte]
      rw [origin_shift f g (f a.1) w ha]
    · simp only [↓reduceIte]
      rw [origin_shift f g (f a.1)⁻¹ w (fun b hb => (ha b hb).inv_left),
        inv_mul_cancel_right]
      ring

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.ArtinCubicalTopology
open TraceWords CubeInterpolation CubicalChains.Reorientation
variable {V : Type*} [Fintype V] (L : SimpleGraph V)

local instance : Std.Symm L.Adj := ⟨fun _ _ h => h.symm⟩
local instance : Std.Irrefl L.Adj := ⟨fun _ => L.irrefl⟩

abbrev f := artinGenerator L
abbrev comm := fun v w h => adjacent_generators_commute L (v := v) (w := w) h
abbrev D := artinDescendingData L
abbrev Positive := CubeRealization.Point L (f L) (comm L)
abbrev Descending := (D L).Point

omit [Fintype V] in
@[simp] theorem step_eq (a : Letter V) : step (f L) a = letterValue (f L) (invLetter a) := by
  cases a with | mk v b => cases b <;> rfl

def exponent (v : V) : ArtinGroup L →* Multiplicative ℝ :=
  artinLift L (fun w => Multiplicative.ofAdd (if v = w then (1 : ℝ) else 0))
    (fun _ _ _ => Commute.all _ _)

omit [Fintype V] in
@[simp] theorem exponent_generator (v w : V) :
    (exponent L v (f L w)).toAdd = if v = w then 1 else 0 := by
  simp [exponent,f]

omit [Fintype V] in
@[simp] theorem height_generator (v : V) : (height L (f L v)).toAdd = 1 := by
  exact congrArg Multiplicative.toAdd (PresentedGroup.toGroup.of _)

def signedExponent (a : Letter V) : ArtinGroup L →* Multiplicative ℝ :=
  artinLift L (fun v => Multiplicative.ofAdd
    (if a.1 = v then (if a.2 then (-1 : ℝ) else 1) else 0))
    (fun _ _ _ => Commute.all _ _)

theorem signedExponent_step (g : ArtinGroup L) (a : Letter V) (ha : a ∈ (D L).desc g)
    (b : Letter V) (hb : b ∈ (D L).desc g) :
    (signedExponent L a (letterValue (f L) (invLetter b))).toAdd = if a = b then 1 else 0 := by
  by_cases he : a = b
  · subst b
    rcases a with ⟨v,b⟩
    cases b <;> simp [signedExponent,letterValue,invLetter,f]
  · have hi : Independent L a b := rightDescents_pairwise L g
      (by simpa [D,artinDescendingData] using ha) (by simpa [D,artinDescendingData] using hb) he
    have hv : a.1 ≠ b.1 := hi.ne
    rcases b with ⟨v,b⟩
    cases b <;> simp [signedExponent,letterValue,invLetter,f,hv,he]

theorem positive_interp_inj : Function.Injective
    (fun p : Positive L => fun φ => CubeRealization.interpolation L (f L) (comm L) p φ) :=
  CubeRealization.interpolation_injective L (f L) (comm L) (height L) (height_generator L)
    (exponent L) (exponent_generator L)

theorem descending_interp_inj : Function.Injective
    (fun p : Descending L => fun φ => (D L).interpolation p φ) :=
  (D L).interpolation_injective (signedExponent L) (by
    intro g a ha b hb
    by_cases he : a = b <;> simpa [he] using signedExponent_step L g a ha b hb)

def flip (b : Bool) (t : unitInterval) : unitInterval :=
  if b then unitInterval.symm t else t

@[simp] theorem flip_flip (b : Bool) (t : unitInterval) : flip b (flip b t) = t := by
  cases b <;> simp [flip]

theorem flip_continuous (b : Bool) : Continuous (flip b) := by
  cases b
  · exact continuous_id
  · exact unitInterval.continuous_symm

def vertexEquiv (w : Word V) (hw : (w.map Prod.fst).Nodup) :
    w.toFinset ≃ (w.map Prod.fst).toFinset :=
  Equiv.ofBijective (fun a => ⟨a.val.1,by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a.val,List.mem_toFinset.mp a.property,rfl⟩)⟩) (by
    constructor
    · intro a b he
      apply Subtype.ext
      exact (List.nodup_map_iff_inj_on (hw.of_map Prod.fst)).mp hw
        a.val (List.mem_toFinset.mp a.property) b.val (List.mem_toFinset.mp b.property) (congrArg Subtype.val he)
    · intro v
      obtain ⟨a,ha,he⟩ := List.mem_map.mp (List.mem_toFinset.mp v.property)
      exact ⟨⟨a,by simpa using ha⟩,Subtype.ext he⟩)

omit [Fintype V] in
@[simp] theorem vertexEquiv_val (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (a : w.toFinset) : (vertexEquiv w hw a).val = a.val.1 := rfl

def toPositiveCoords (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (x : w.toFinset → unitInterval) : (w.map Prod.fst).toFinset → unitInterval :=
  fun v => flip ((vertexEquiv w hw).symm v).val.2 (x ((vertexEquiv w hw).symm v))

omit [Fintype V] in
@[simp] theorem toPositiveCoords_apply (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (x : w.toFinset → unitInterval) (a : w.toFinset) :
    toPositiveCoords w hw x (vertexEquiv w hw a) = flip a.val.2 (x a) := by
  simp [toPositiveCoords]

omit [Fintype V] in
theorem toPositiveCoords_continuous (w : Word V) (hw : (w.map Prod.fst).Nodup) :
    Continuous (toPositiveCoords w hw) :=
  continuous_pi (fun _ => (flip_continuous _).comp (continuous_apply _))

def toDescendingCoords (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (z : (w.map Prod.fst).toFinset → unitInterval) : w.toFinset → unitInterval :=
  fun a => flip a.val.2 (z (vertexEquiv w hw a))

omit [Fintype V] in
theorem toDescendingCoords_continuous (w : Word V) (hw : (w.map Prod.fst).Nodup) :
    Continuous (toDescendingCoords w hw) :=
  continuous_pi (fun _ => (flip_continuous _).comp (continuous_apply _))

omit [Fintype V] in
@[simp] theorem toPositive_toDescending (w : Word V) (hw : (w.map Prod.fst).Nodup)
    (z : (w.map Prod.fst).toFinset → unitInterval) :
    toPositiveCoords w hw (toDescendingCoords w hw z) = z := by
  funext v
  obtain ⟨a,rfl⟩ := (vertexEquiv w hw).surjective v
  simp [toDescendingCoords]

def positiveCell (g : ArtinGroup L) (w : Word V) (hw : (w.map Prod.fst).Pairwise L.Adj) :
    CubeRealization.Cell (G := ArtinGroup L) L where
  base := origin (f L) g w
  directions := (w.map Prod.fst).toFinset
  clique := fun _ ha _ hb he => hw.forall (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) he

def descendingCell (g : ArtinGroup L) (w : Word V)
    (hd : ∀ a ∈ w, a ∈ rightDescents L g) : (D L).Cell where
  top := g
  directions := w.toFinset
  subset a ha := by simpa [D,artinDescendingData] using hd a (List.mem_toFinset.mp ha)

theorem interpolation_reorientation (g : ArtinGroup L) (w : Word V)
    (hw : (w.map Prod.fst).Pairwise L.Adj) (hd : ∀ a ∈ w, a ∈ rightDescents L g)
    (x : (D L).Coordinates (descendingCell L g w hd)) (φ : ArtinGroup L → ℝ) :
    (D L).interpolation ((D L).characteristic (descendingCell L g w hd) x) φ =
      CubeRealization.interpolation L (f L) (comm L)
        (CubeRealization.characteristic (f L) (comm L) (positiveCell L g w hw)
          (toPositiveCoords w hw.nodup x)) φ := by
  refine ((D L).interpolation_characteristic (descendingCell L g w hd) x φ).trans ?_
  refine Eq.trans ?_ (CubeRealization.interpolation_characteristic L (f L) (comm L)
    (positiveCell L g w hw) (toPositiveCoords w hw.nodup x) φ).symm
  have hf : (fun a : Letter V => letterValue (artinGenerator L) (invLetter a)) = step (f L) :=
    funext (fun a => (step_eq L a).symm)
  erw [operator_listed _ w (hw.nodup.of_map Prod.fst),operator_listed _ _ hw.nodup]
  have hop := congrArg (fun k : Letter V → ArtinGroup L => listed k w) hf
  rw [hop]
  apply listed_reorientation
  · exact (List.pairwise_map.mp hw).imp (fun hh => adjacent_generators_commute L hh)
  · intro a ha
    let aa : w.toFinset := ⟨a,by simpa using ha⟩
    have h₁ : (D L).fullCoord (descendingCell L g w hd) x a = (x aa : ℝ) := by
      exact (D L).fullCoord_mem (descendingCell L g w hd) x aa
    have h₂ : CubeRealization.fullCoord (positiveCell L g w hw)
        (toPositiveCoords w hw.nodup x) a.1 = (flip a.2 (x aa) : ℝ) := by
      have hh := CubeRealization.fullCoord_mem (positiveCell L g w hw)
        (toPositiveCoords w hw.nodup x) (vertexEquiv w hw.nodup aa)
      exact hh.trans (congrArg (fun z : unitInterval => (z : ℝ))
        (toPositiveCoords_apply w hw.nodup x aa))
    rw [h₁,h₂]
    cases h : a.2 <;> simp [flip]

theorem descendingCell_rep (c : (D L).Cell) :
    ∃ (g : ArtinGroup L) (w : Word V) (_hw : (w.map Prod.fst).Pairwise L.Adj)
      (hd : ∀ a ∈ w, a ∈ rightDescents L g), descendingCell L g w hd = c := by
  let w := c.directions.toList
  have hd : ∀ a ∈ w, a ∈ rightDescents L c.top := by
    intro a ha
    have hh := c.subset (Finset.mem_toList.mp ha)
    simpa [D,artinDescendingData] using hh
  have hw : (w.map Prod.fst).Pairwise L.Adj := by
    apply List.pairwise_map.mpr
    apply c.directions.nodup_toList.pairwise_of_forall_ne
    intro a ha b hb he
    exact rightDescents_pairwise L c.top (hd a ha) (hd b hb) he
  refine ⟨c.top,w,hw,hd,?_⟩
  cases c with
  | mk g s hs =>
    dsimp only [descendingCell,w]
    congr
    exact s.toList_toFinset

omit [Fintype V] in
theorem positiveCell_rep (c : CubeRealization.Cell (G := ArtinGroup L) L) :
    ∃ (g : ArtinGroup L) (w : Word V) (hw : (w.map Prod.fst).Pairwise L.Adj)
      (_hd : ∀ a ∈ w, a ∈ rightDescents L g), positiveCell L g w hw = c := by
  let v := c.directions.toList
  have hv : v.Pairwise L.Adj := c.directions.nodup_toList.pairwise_of_forall_ne
    (fun a ha b hb he => c.clique (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) he)
  let o := CubeDescents.orient L c.base v
  have hw : (o.2.map Prod.fst).Pairwise L.Adj := by
    simpa only [o,CubeDescents.orient_map] using hv
  have hd : ∀ a ∈ o.2, a ∈ rightDescents L o.1 := CubeDescents.orient_descents L c.base v hv
  refine ⟨o.1,o.2,hw,hd,?_⟩
  have hb : origin (f L) o.1 o.2 = c.base := CubeDescents.origin_orient L c.base v hv
  have hs : (o.2.map Prod.fst).toFinset = c.directions := by
    simp only [o,CubeDescents.orient_map,v,Finset.toList_toFinset]
  cases c with
  | mk g s hc =>
    change CubeRealization.Cell.mk (origin (f L) o.1 o.2) (o.2.map Prod.fst).toFinset _ = _
    congr

theorem descending_local_lift (c : (D L).Cell) :
    ∃ φ : C((D L).Coordinates c,Positive L), ∀ x,
      (fun ψ => CubeRealization.interpolation L (f L) (comm L) (φ x) ψ) =
        (fun ψ => (D L).interpolation ((D L).characteristic c x) ψ) := by
  obtain ⟨g,w,hw,hd,rfl⟩ := descendingCell_rep L c
  refine ⟨⟨fun x => CubeRealization.characteristic (f L) (comm L) (positiveCell L g w hw)
    (toPositiveCoords w hw.nodup x),
    (CubeRealization.characteristic_continuous (f L) (comm L) (positiveCell L g w hw)).comp
      (toPositiveCoords_continuous w hw.nodup)⟩,?_⟩
  intro x
  funext ψ
  exact (interpolation_reorientation L g w hw hd x ψ).symm

theorem positive_local_lift (c : CubeRealization.Cell (G := ArtinGroup L) L) :
    ∃ φ : C(CubeRealization.Coordinates c,Descending L), ∀ x,
      (fun ψ => (D L).interpolation (φ x) ψ) =
        (fun ψ => CubeRealization.interpolation L (f L) (comm L)
          (CubeRealization.characteristic (f L) (comm L) c x) ψ) := by
  obtain ⟨g,w,hw,hd,rfl⟩ := positiveCell_rep L c
  refine ⟨⟨fun x => (D L).characteristic (descendingCell L g w hd) (toDescendingCoords w hw.nodup x),
    ((D L).characteristic_continuous (descendingCell L g w hd)).comp
      (toDescendingCoords_continuous w hw.nodup)⟩,?_⟩
  intro x
  funext ψ
  change (D L).interpolation ((D L).characteristic (descendingCell L g w hd)
    (toDescendingCoords w hw.nodup x)) ψ = _
  change (w.map Prod.fst).toFinset → unitInterval at x
  simpa only [toPositive_toDescending] using interpolation_reorientation L g w hw hd
    (toDescendingCoords w hw.nodup x) ψ

/-- Reorientation preserves the actual weak topologies, not only cellular chains. -/
def reorient : Descending L ≃ₜ Positive L :=
  WeakRealization.homeomorph (D L).evaluation (CubeRealization.evaluation (f L) (comm L))
    (D L).evaluation_quotient (CubeRealization.evaluation_quotient (f L) (comm L))
    (fun p ψ => (D L).interpolation p ψ)
    (fun p ψ => CubeRealization.interpolation L (f L) (comm L) p ψ)
    (descending_interp_inj L) (positive_interp_inj L)
    (descending_local_lift L) (positive_local_lift L)

variable [Nonempty V]

/-- The ordinary positive-cube CW realization is genuinely contractible. -/
theorem positive_contractible : ContractibleSpace (Positive L) := by
  let : ContractibleSpace (Descending L) := artinDescending_contractible L
  exact (reorient L).symm.contractibleSpace

end EilenbergGanea.ArtinCubicalTopology

open Classical Set Topology
namespace CompactChart

/-- A characteristic map which has singleton fibers over its open cell has a
continuous inverse there. Compactness is used only on the closed disk; no
regularity of the attaching sphere is required. -/
theorem continuousOn_symm {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [T2Space X] (e : PartialEquiv A X) (K : Set A) (hK : IsCompact K)
    (hsub : e.source ⊆ K) (hc : ContinuousOn e K)
    (hboundary : ∀ a ∈ K, e a ∈ e.target → a ∈ e.source) :
    ContinuousOn e.symm e.target := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → X := fun a => e a
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp hc
  let r := e.target.restrictPreimage f
  have hr : Function.Surjective r := by
    intro x
    refine ⟨⟨⟨e.symm x,hsub (e.map_target x.property)⟩,?_⟩,?_⟩
    · change e (e.symm x) ∈ e.target
      rw [e.right_inv x.property]
      exact x.property
    · exact Subtype.ext (e.right_inv x.property)
  have hq : IsQuotientMap r :=
    (hf.isClosedMap.restrictPreimage e.target).isQuotientMap hf.restrictPreimage hr
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hq.continuous_iff.mpr
  have he : (fun x : e.target => e.symm x) ∘ r =
      (fun a : f ⁻¹' e.target => (a.val.val : A)) := by
    funext a
    exact e.left_inv (hboundary a.val a.val.property a.property)
  change Continuous ((fun x : e.target => e.symm x) ∘ r)
  rw [he]
  exact continuous_subtype_val.comp continuous_subtype_val

end CompactChart

namespace EilenbergGanea.CubeRealization

section
open Metric
variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

theorem chartInverse_continuousOn_of_t2 [T2Space (Point (G := G) L f comm)]
    {n : ℕ} (c : DimCell (G := G) (L := L) n) :
    ContinuousOn (chart f comm c).symm (chart f comm c).target := by
  apply CompactChart.continuousOn_symm (chart f comm c) (closedBall 0 1)
    (isCompact_closedBall _ _) ball_subset_closedBall (chart_continuous f comm c).continuousOn
  intro t ht he
  change pointCell (chart f comm c t) = c.val at he
  change t ∈ ball 0 1
  by_contra hn
  have hs : t ∈ sphere 0 1 := mem_sphere.mpr
    (le_antisymm (mem_closedBall.mp ht) (le_of_not_gt hn))
  have hd := boundary_dimension_lt f comm c hs
  rw [he,c.property] at hd
  exact (lt_irrefl _) hd

/-- The ordinary CW structure follows from the genuine normalized-cube gluing;
only Hausdorffness and compact characteristic disks are used. -/
@[instance_reducible] def cwComplexOfT2 [T2Space (Point (G := G) L f comm)] : CWComplex (univ : Set (Point (G := G) L f comm)) where
  cell := DimCell (G := G) (L := L)
  map := fun _ c => chart f comm c
  source_eq := fun _ _ => rfl
  continuousOn := fun _ c => (chart_continuous f comm c).continuousOn
  continuousOn_symm := fun _ c => chartInverse_continuousOn_of_t2 f comm c
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (chart f comm a.2 '' ball 0 1) (chart f comm b.2 '' ball 0 1)
    rw [chart_image_ball,chart_image_ball]
    apply Set.disjoint_left.mpr
    intro p ha hb
    apply hab
    have he : a.2.val = b.2.val := ha.symm.trans hb
    have hn : a.1 = b.1 := a.2.property.symm.trans ((congrArg (fun c => c.directions.card) he).trans b.2.property)
    cases a with | mk n a =>
      cases b with | mk m b =>
        dsimp at hn
        subst m
        exact congrArg (Sigma.mk n) (Subtype.ext he)
  mapsTo' := chart_mapsTo f comm
  closed' := by
    intro A _ hA
    apply (evaluation_quotient f comm).isClosed_preimage.mp
    rw [isClosed_sigma_iff]
    intro c
    let d : DimCell (G := G) (L := L) c.directions.card := ⟨c,rfl⟩
    have hh := (hA _ d).preimage (characteristic_continuous f comm c)
    rw [chart_image_disk] at hh
    change IsClosed (characteristic f comm c ⁻¹' (A ∩ Set.range (characteristic f comm c))) at hh
    change IsClosed (characteristic f comm c ⁻¹' A)
    simpa only [Set.preimage_inter,Set.preimage_range,Set.inter_univ] using hh
  union' := by
    apply Set.eq_univ_of_forall
    intro p
    let d : DimCell (G := G) (L := L) (pointCell p).directions.card := ⟨pointCell p,rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨_,Set.mem_iUnion.mpr ⟨d,?_⟩⟩
    rw [chart_image_disk]
    exact ⟨pointCoordinates p,characteristic_point f comm p⟩

end

variable {G Q V : Type*} [Group G] [Group Q] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))
variable (q : G →* Q)

include comm in
omit [Fintype V] in
theorem mappedComm : ∀ v w, L.Adj v w → Commute ((q ∘ f) v) ((q ∘ f) w) :=
  fun v w hvw => (comm v w hvw).map q

/-- Applying a group homomorphism only to the initial vertices of cubes. -/
def mapPoint (p : Point (G := G) L f comm) : Point (G := Q) L (q ∘ f) (mappedComm f comm q) where
  base := q p.base
  coord := p.coord
  nonneg := p.nonneg
  lt_one := p.lt_one
  clique := p.clique

def mapCell (c : Cell (G := G) L) : Cell (G := Q) L where
  base := q c.base
  directions := c.directions
  clique := c.clique

omit [Fintype V] in
@[simp] theorem mapPoint_base (p : Point (G := G) L f comm) :
    (mapPoint f comm q p).base = q p.base := rfl

omit [Fintype V] in
@[simp] theorem mapPoint_coord (p : Point (G := G) L f comm) :
    (mapPoint f comm q p).coord = p.coord := rfl

omit [Fintype V] in
@[simp] theorem mapPoint_characteristic (c : Cell (G := G) L) (x : Coordinates c) :
    mapPoint f comm q (characteristic f comm c x) =
      characteristic (q ∘ f) (mappedComm f comm q) (mapCell q c) x := by
  apply Point.ext
  · change q (c.base * product f comm (ones c x) _) =
      q c.base * product (q ∘ f) (mappedComm f comm q) (ones c x) _
    rw [map_mul]
    congr 1
    exact Finset.map_noncommProd _ _ _ q
  · rfl

theorem mapPoint_continuous : Continuous (mapPoint f comm q) := by
  apply (evaluation_quotient f comm).continuous_iff.mpr
  apply continuous_sigma
  intro c
  change Continuous (fun x => mapPoint f comm q (characteristic f comm c x))
  simp only [mapPoint_characteristic]
  exact characteristic_continuous (q ∘ f) (mappedComm f comm q) (mapCell q c)

omit [Fintype V] in
theorem mapCell_surjective (hq : Function.Surjective q) : Function.Surjective (mapCell (L := L) q) := by
  rintro ⟨a,s,hs⟩
  obtain ⟨g,rfl⟩ := hq a
  exact ⟨⟨g,s,hs⟩,rfl⟩

omit [Fintype V] in
theorem mapPoint_surjective (hq : Function.Surjective q) : Function.Surjective (mapPoint f comm q) := by
  rintro ⟨a,x,hx,ht,hc⟩
  obtain ⟨g,rfl⟩ := hq a
  exact ⟨⟨g,x,hx,ht,hc⟩,rfl⟩

/-- The base-label quotient is a genuine topological quotient for the weak
cubical topologies, proved by lifting each actual characteristic disk. -/
theorem mapPoint_quotient (hq : Function.Surjective q) : IsQuotientMap (mapPoint f comm q) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨mapPoint_surjective f comm q hq,?_⟩
  intro A
  constructor
  · exact fun hA => hA.preimage (mapPoint_continuous f comm q)
  · intro hA
    apply (evaluation_quotient (q ∘ f) (mappedComm f comm q)).isClosed_preimage.mp
    rw [isClosed_sigma_iff]
    intro c
    obtain ⟨d,rfl⟩ := mapCell_surjective q hq c
    have hh := hA.preimage (characteristic_continuous f comm d)
    change IsClosed ((fun x => mapPoint f comm q (characteristic f comm d x)) ⁻¹' A) at hh
    change IsClosed ((fun x : Coordinates d =>
      characteristic (q ∘ f) (mappedComm f comm q) (mapCell q d) x) ⁻¹' A)
    simpa only [mapPoint_characteristic] using hh

omit [Fintype V] in
/-- The literal group-kernel orbits are exactly the fibers of the cube map. -/
theorem mapPoint_eq_iff_orbit (p r : Point (G := G) L f comm) :
    mapPoint f comm q p = mapPoint f comm q r ↔ p ∈ MulAction.orbit q.ker r := by
  constructor
  · intro he
    have hb : q p.base = q r.base := congrArg Point.base he
    have hx : p.coord = r.coord := congrArg (fun z : Point (G := Q) L (q ∘ f)
      (mappedComm f comm q) => z.coord) he
    let g : q.ker := ⟨p.base * r.base⁻¹,by simp only [MonoidHom.mem_ker,map_mul,map_inv,hb,mul_inv_cancel]⟩
    refine ⟨g,?_⟩
    apply Point.ext
    · change (p.base * r.base⁻¹) * r.base = p.base
      simp [mul_assoc]
    · exact hx.symm
  · rintro ⟨g,rfl⟩
    apply Point.ext
    · change q ((g : G) * r.base) = q r.base
      rw [map_mul,g.property,one_mul]
    · rfl

/-- The quotient homeomorphism respects the actual weak topologies. -/
def kernelQuotientHomeomorph (hq : Function.Surjective q) :
    Quotient (MulAction.orbitRel q.ker (Point (G := G) L f comm)) ≃ₜ
      Point (G := Q) L (q ∘ f) (mappedComm f comm q) :=
  (Homeomorph.Quotient.congrRight (fun p r => (mapPoint_eq_iff_orbit f comm q p r).symm)).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨mapPoint f comm q,mapPoint_continuous f comm q⟩)
      (mapPoint_quotient f comm q hq))

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

include h hf exponent hexponent in
theorem quotientPoint_t2 (hq : Function.Surjective q) :
    T2Space (Point (G := Q) L (q ∘ f) (mappedComm f comm q)) := by
  let := point_t2 L f comm h hf exponent hexponent
  let := point_weaklyLocallyCompact L f comm
  exact (kernelQuotientHomeomorph f comm q hq).t2Space

include h hf exponent hexponent in
theorem mapPoint_covering (hq : Function.Surjective q) :
    IsQuotientCoveringMap (mapPoint f comm q) q.ker where
  toIsQuotientMap := mapPoint_quotient f comm q hq
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := mapPoint_eq_iff_orbit f comm q _ _
  disjoint := (subgroup_quotient_covering f comm h hf exponent hexponent q.ker).disjoint

end EilenbergGanea.CubeRealization

namespace EilenbergGanea
universe u
namespace ArtinCubicalTopology
open CubeRealization
variable {V : Type u} [Fintype V] [Nonempty V] (L : SimpleGraph V)

omit [Fintype V] in
theorem height_surjective : Function.Surjective (height L) := by
  intro n
  let v : V := Classical.choice inferInstance
  refine ⟨f L v ^ n.toAdd,?_⟩
  rw [map_zpow]
  apply Multiplicative.toAdd.injective
  change n.toAdd • (height L (f L v)).toAdd = n.toAdd
  simp only [height_generator,zsmul_eq_mul,mul_one,Int.cast_id]

def HeightQuotient := Point L ((height L) ∘ f L) (mappedComm (f L) (comm L) (height L))

instance : TopologicalSpace (HeightQuotient L) := inferInstanceAs (TopologicalSpace
  (Point L ((height L) ∘ f L) (mappedComm (f L) (comm L) (height L))))

/-- An ordinary cubical classifying space for the height kernel, with one cube
for every integral level and clique. Contractibility above is the explicit
word-length contraction, and the fundamental-group identification reuses
Mathlib's checked covering-monodromy equivalence. -/
theorem height_hasClassifyingSpace (d : ℕ)
    (hd : ∀ s : Finset V, (s : Set V).Pairwise L.Adj → s.card ≤ d) :
    HasClassifyingSpace.{u} (height L).ker d := by
  let X := Point L ((height L) ∘ f L) (mappedComm (f L) (comm L) (height L))
  let E := Positive L
  let : ContractibleSpace E := positive_contractible L
  let : T2Space X := quotientPoint_t2 (f L) (comm L) (height L)
    (height L) (height_generator L) (exponent L) (exponent_generator L) (height_surjective L)
  let : Topology.CWComplex (Set.univ : Set X) :=
    cwComplexOfT2 ((height L) ∘ f L) (mappedComm (f L) (comm L) (height L))
  let p : E → X := mapPoint (f L) (comm L) (height L)
  have hp : IsQuotientCoveringMap p (height L).ker :=
    mapPoint_covering (f L) (comm L) (height L) (height L) (height_generator L)
      (exponent L) (exponent_generator L) (height_surjective L)
  have hs : Function.Surjective p := mapPoint_surjective (f L) (comm L) (height L) (height_surjective L)
  let : PathConnectedSpace X := hs.pathConnectedSpace hp.continuous
  let e : E := Classical.choice (inferInstance : Nonempty E)
  refine ⟨X,inferInstance,inferInstance,inferInstance,?_,inferInstance,p e,?_,
    E,inferInstance,inferInstance,p,hp.isCoveringMap,hs⟩
  · intro k hk
    exact ⟨fun c => Nat.not_lt_of_ge ((c.property.symm ▸ hd c.val.directions c.val.clique)) hk⟩
  · exact ⟨(hp.fundamentalGroupEquiv ⟨e,rfl⟩).trans (MulEquiv.inv' ((height L).ker)).symm⟩

end ArtinCubicalTopology

/-- The fixed source group has an ordinary three-dimensional classifying CW
space, with an actually contractible surjective covering. -/
theorem source_hasClassifyingSpace_three : HasClassifyingSpace.{0} SourceGroup 3 :=
  ArtinCubicalTopology.height_hasClassifyingSpace seedGraph 3 SeedConnection.clique_card_le_three
end EilenbergGanea

end

end OAI
