import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.MonoidTowers
import OAI.SetTheory.PartitionConsistency.Algebra.DirectLimits

namespace OAI

/-! ## Schedule -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section

namespace ProbeData
variable {M N : Object.{u}}
/-- Transport parameters, not profile conclusions, from the starting stage. -/
def map (d : ProbeData M) (f : M ⟶ N) : ProbeData N where
  a := f d.a
  b := f d.b
  b_ne_one h := d.b_ne_one (f.injective (h.trans f.map_one.symm))
  path := d.path.map f.toMonoidHom

@[simp] theorem map_a (d : ProbeData M) (f : M ⟶ N) : (d.map f).a = f d.a := rfl
@[simp] theorem map_b (d : ProbeData M) (f : M ⟶ N) : (d.map f).b = f d.b := rfl
@[simp] theorem map_node (d : ProbeData M) (f : M ⟶ N) (i : ℕ) :
    (d.map f).path.node i = f (d.path.node i) := rfl
end ProbeData

namespace MergerData
variable {M N : Object.{u}}
def map (d : MergerData M) (f : M ⟶ N) : MergerData N where
  n := d.n
  positive := d.positive
  prescription := d.prescription.map f.toMonoidHom
  valid := (d.prescription.valid_map_iff M.joins f.conservative).2 d.valid
end MergerData

/-- The two actual operations to execute in a round. -/
abbrev Request (M : Object.{u}) := ProbeData M ⊕ MergerData M

namespace Request
variable {M N : Object.{u}}
def map : Request M → (M ⟶ N) → Request N
  | .inl d, f => .inl (d.map f)
  | .inr d, f => .inr (d.map f)

def target : Request M → Object.{u}
  | .inl d => d.extension
  | .inr d => d.extension

def inclusion : (d : Request M) → M ⟶ d.target
  | .inl d => d.inclusion
  | .inr d => d.inclusion

theorem cardinal_le (d : Request M) {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hM : Cardinal.mk M ≤ μ) : Cardinal.mk d.target ≤ μ := by
  cases d with
  | inl d => exact d.cardinal_le hω hM
  | inr d => exact d.cardinal_le hω hM

theorem gates (d : Request M) : HasOldGates d.inclusion.toMonoidHom := by
  cases d with
  | inl d => exact d.gates
  | inr d => exact d.gates

theorem preserves_profile (d : Request M) {a b e m : M} {n : ℕ → M}
    (h : ProbeProfile a b e m n) : ProbeProfile (d.inclusion a) (d.inclusion b)
      (d.inclusion e) (d.inclusion m) (fun i => d.inclusion (n i)) :=
  h.map d.inclusion.conservative d.gates

end Request

instance {J : Type u} [LinearOrder J] [Nonempty J] (M : Object.{u}) :
    HasIterationOfShape J (Under M) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := hj.nonempty_Iio.to_subtype
    have : IsFiltered (Set.Iio j) := inferInstance
    have : IsConnected (Set.Iio j) := IsFiltered.isConnected _
    infer_instance

instance {J : Type u} [LinearOrder J] [Nonempty J] (M : Object.{u}) :
    PreservesWellOrderContinuousOfShape J (Under.forget M) where
  preservesColimitsOfShape j hj := by
    have := hj.nonempty_Iio.to_subtype
    have : IsFiltered (Set.Iio j) := inferInstance
    have : IsConnected (Set.Iio j) := IsFiltered.isConnected _
    infer_instance

namespace Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

def step (j : J) (X : Under M) : ConstructionIteration.Step X where
  target := Under.mk (X.hom ≫ ((schedule j).map X.hom).inclusion)
  map := Under.homMk ((schedule j).map X.hom).inclusion

abbrev underFunctor : J ⥤ Under M :=
  ConstructionIteration.functor (Under.mk (𝟙 M)) (step M schedule)

abbrev functor : J ⥤ Object.{u} := underFunctor M schedule ⋙ Under.forget M

/-- Each stage has the same specified conservative map from the round's base. -/
def fromBase (j : J) : M ⟶ (functor M schedule).obj j := (underFunctor M schedule).obj j |>.hom

@[simp] theorem fromBase_naturality {i j : J} (h : i ≤ j) :
    fromBase M schedule i ≫ (functor M schedule).map (homOfLE h) = fromBase M schedule j :=
  ((underFunctor M schedule).map (homOfLE h)).w

def botIso : (functor M schedule).obj ⊥ ≅ M :=
  (Under.forget M).mapIso (ConstructionIteration.botIso (Under.mk (𝟙 M)) (step M schedule))

def succIso (j : J) (hj : ¬ IsMax j) :
    (functor M schedule).obj (Order.succ j) ≅
      ((schedule j).map (fromBase M schedule j)).target :=
  (Under.forget M).mapIso
    (ConstructionIteration.succIso (Under.mk (𝟙 M)) (step M schedule) j hj)

theorem map_succ (j : J) (hj : ¬ IsMax j) :
    (functor M schedule).map (homOfLE (Order.le_succ j)) =
      ((schedule j).map (fromBase M schedule j)).inclusion ≫ (succIso M schedule j hj).inv :=
  congrArg (Under.forget M).map
    (ConstructionIteration.map_succ (Under.mk (𝟙 M)) (step M schedule) j hj)

end Round
end
end PartitionConsistency.MonoidConstruction


/-! ## LimitProperties -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section

@[simp] theorem comp_apply {M N R : Object.{u}} (f : M ⟶ N) (g : N ⟶ R) (x : M) :
    (f ≫ g) x = g (f x) := rfl
@[simp] theorem identity_apply (M : Object.{u}) (x : M) : (𝟙 M) x = x := rfl

/-- The underlying equivalence of stages of a construction isomorphism. -/
def isoEquiv {M N : Object.{u}} (e : M ≅ N) : M ≃ N where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : M ⟶ M => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : N ⟶ N => f x) e.inv_hom_id

/-- A genuine property of a transition, not a field assumed at arbitrary limits. -/
def PreservesProfiles {M N : Object.{u}} (f : M ⟶ N) : Prop :=
  ∀ (a b e m : M) (n : ℕ → M), ProbeProfile a b e m n →
    ProbeProfile (f a) (f b) (f e) (f m) (fun i => f (n i))

namespace PreservesProfiles
variable {M N R : Object.{u}}
theorem id (M : Object.{u}) : PreservesProfiles (𝟙 M) := by intro a b e m n h; exact h

theorem comp {f : M ⟶ N} {g : N ⟶ R} (hf : PreservesProfiles f) (hg : PreservesProfiles g) :
    PreservesProfiles (f ≫ g) := by
  intro a b e m n h
  exact hg _ _ _ _ _ (hf _ _ _ _ _ h)

theorem of_surjective {f : M ⟶ N} (hf : Function.Surjective f) : PreservesProfiles f := by
  intro a b e m n h
  exact h.map f.conservative (fun x _ => Or.inl (hf x))

theorem of_iso (e : M ≅ N) : PreservesProfiles e.hom :=
  of_surjective (isoEquiv e).surjective

theorem operation (d : Request M) : PreservesProfiles d.inclusion := by
  intro a b e m n h
  exact d.preserves_profile h
end PreservesProfiles

namespace DirectedColimit
variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ Object.{u})
  {C : Cocone F} (hc : IsColimit C)
include hc

/-- Any colimit in the stage category is a union of its stages as a monoid. -/
theorem exists_rep (y : C.pt) : ∃ i : J, ∃ x : F.obj i, C.ι.app i x = y := by
  let e := (isColimit F).coconePointUniqueUpToIso hc
  obtain ⟨i,x,hx⟩ := DirectLimit.exists_eq_mk (transition F) (e.inv y)
  refine ⟨i,x,?_⟩
  have he : inclusion F i ≫ e.hom = C.ι.app i :=
    (isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  have h := congrArg e.hom hx.symm
  change e.hom (inclusion F i x) = e.hom (e.inv y) at h
  change (inclusion F i ≫ e.hom) x = (e.inv ≫ e.hom) y at h
  simpa only [he, e.inv_hom_id, identity_apply] using h

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ) (hJ : Cardinal.mk J ≤ μ)
    (hF : ∀ i, Cardinal.mk (F.obj i) ≤ μ) : Cardinal.mk C.pt ≤ μ := by
  let e := (isColimit F).coconePointUniqueUpToIso hc
  rw [← Cardinal.mk_congr (isoEquiv e)]
  exact ConservativeLimit.cardinal_le (transition F) hω hJ hF

theorem profile (i : J) (a b e m : F.obj i) (n : ℕ → F.obj i)
    (hP : ∀ j (hij : i ≤ j), ProbeProfile
      (F.map (homOfLE hij) a) (F.map (homOfLE hij) b) (F.map (homOfLE hij) e)
      (F.map (homOfLE hij) m) (fun k => F.map (homOfLE hij) (n k))) :
    ProbeProfile (C.ι.app i a) (C.ι.app i b) (C.ι.app i e)
      (C.ι.app i m) (fun k => C.ι.app i (n k)) := by
  have h := ConservativeLimit.probeProfile (transition F) (conservative F) i a b e m n hP
  let φ := (isColimit F).coconePointUniqueUpToIso hc
  have h' := PreservesProfiles.of_iso φ _ _ _ _ _ h
  have he : inclusion F i ≫ φ.hom = C.ι.app i :=
    (isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  change ProbeProfile ((inclusion F i ≫ φ.hom) a) ((inclusion F i ≫ φ.hom) b)
    ((inclusion F i ≫ φ.hom) e) ((inclusion F i ≫ φ.hom) m)
    (fun k => (inclusion F i ≫ φ.hom) (n k)) at h'
  simpa only [he] using h'

end DirectedColimit

namespace ContinuousTower
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (F : J ⥤ Object.{u}) [F.IsWellOrderContinuous]

omit [SuccOrder J] [WellFoundedLT J] in
/-- Every tested element at a limit is already present at a strict earlier cut. -/
theorem exists_rep {j : J} (hj : Order.IsSuccLimit j) (x : F.obj j) :
    ∃ i : J, ∃ hij : i < j, ∃ a : F.obj i, F.map (homOfLE hij.le) a = x := by
  have := hj.nonempty_Iio.to_subtype
  obtain ⟨i,a,ha⟩ := DirectedColimit.exists_rep _ (F.isColimitOfIsWellOrderContinuous j hj) x
  exact ⟨i.1,i.2,a,ha⟩

/-- Successor persistence together with continuity proves persistence through
arbitrary limits, without supposing that the path belongs to every stage. -/
theorem preservesProfiles
    (hsucc : ∀ j, ¬ IsMax j → PreservesProfiles (F.map (homOfLE (Order.le_succ j)))) :
    ∀ (i j : J) (hij : i ≤ j), PreservesProfiles (F.map (homOfLE hij)) := by
  intro i j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    intro hij
    have he : i = j := le_antisymm hij (hj hij)
    subst i
    simpa using PreservesProfiles.id (F.obj j)
  | succ j hj ih =>
    intro hij
    rcases hij.eq_or_lt with he | he
    · subst i
      simpa using PreservesProfiles.id (F.obj (Order.succ j))
    · have hij' : i ≤ j := (Order.lt_succ_iff_of_not_isMax hj).1 he
      have h := (ih hij').comp (hsucc j hj)
      simpa only [← F.map_comp, homOfLE_comp] using h
  | isSuccLimit j hj ih =>
    intro hij
    rcases hij.eq_or_lt with he | he
    · subst i
      simpa using PreservesProfiles.id (F.obj j)
    · intro a b e m n h
      have := hj.nonempty_Iio.to_subtype
      apply DirectedColimit.profile ((Set.principalSegIio j).monotone.functor ⋙ F)
        (F.isColimitOfIsWellOrderContinuous j hj) ⟨i,he⟩ a b e m n
      intro k hik
      exact ih k.1 k.2 hik a b e m n h

/-- Size is bounded by the size of the stage index and the existing operation
bounds. The colimit bound is a consequence, not an extra construction input. -/
theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ) (hJ : Cardinal.mk J ≤ μ)
    (h₀ : Cardinal.mk (F.obj ⊥) ≤ μ)
    (hsucc : ∀ j, ¬ IsMax j → Cardinal.mk (F.obj j) ≤ μ →
      Cardinal.mk (F.obj (Order.succ j)) ≤ μ) (j : J) : Cardinal.mk (F.obj j) ≤ μ := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    have he : j = ⊥ := by simpa using hj
    rw [he]
    exact h₀
  | succ j hj ih => exact hsucc j hj ih
  | isSuccLimit j hj ih =>
    have := hj.nonempty_Iio.to_subtype
    apply DirectedColimit.cardinal_le _ (F.isColimitOfIsWellOrderContinuous j hj) hω
    · exact (Cardinal.mk_subtype_le _).trans hJ
    · intro i; exact ih i.1 i.2

end ContinuousTower
end
end PartitionConsistency.MonoidConstruction


/-! ## Round -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section

namespace ProbeData
variable {M : Object.{u}} (d : ProbeData M)

theorem probe_gate : OldGate d.inclusion.toMonoidHom d.probe (d.a * M.e) := by
  have hg := d.path.probe_zero_gate M.e_ne_one d.b d.b_ne_one
  refine ⟨ProbeAlgebra.Word.Gate.dvd _ _ hg,ProbeAlgebra.Word.Gate.dvd_old_iff _ _ hg,?_⟩
  intro x hx z
  change (d.probe ∣ z ∧ ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b x ∣ z) ↔
    ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b (d.a * M.e) ∣ z ∧
      ProbeAlgebra.Word.old (d.path.alphabet M.e_ne_one) d.b x ∣ z
  simpa only [probe, and_comm] using! ProbeAlgebra.Word.Gate.old_intersection _ _ hg rfl
    (fun hd => hx ((ProbeAlgebra.Word.old_dvd_iff_headDiv _ _ x d.probe).2 hd)) z

/-- A previously inserted probe, not dividing `a`, meets the next probe
in exactly `ae`. This is why repeated requests give independent cones. -/
theorem independent (x : M) (hx : x ∣ d.a * M.e) (hxa : ¬ x ∣ d.a)
    (z : d.extension) : d.inclusion x ∣ z ∧ d.probe ∣ z ↔ d.inclusion (d.a * M.e) ∣ z := by
  have hxm : ¬ d.inclusion x ∣ d.probe := by
    intro h
    obtain ⟨i,hi⟩ := (d.path.probe_old_profile M.e_ne_one d.b d.b_ne_one x).1 h
    exact hxa (hi.trans (d.path.bounded i))
  have h := d.probe_gate.intersections x hxm z
  have hx' := d.inclusion.toMonoidHom.map_dvd hx
  constructor
  · intro hz; exact ((h).1 ⟨hz.2,hz.1⟩).1
  · intro hz
    have hm := d.probe_gate.divides.trans hz
    exact ⟨hx'.trans hz,hm⟩
end ProbeData

namespace Request
variable {M : Object.{u}}
theorem inclusion_eq_transport (d e : Request M) (h : d = e) :
    d.inclusion = e.inclusion ≫ (eqToIso (congrArg target h)).inv := by
  subst e
  simp
end Request

namespace Round
variable {J : Type u} [CompleteLinearOrder J] [SuccOrder J] [WellFoundedLT J]
  (M : Object.{u}) (schedule : J → Request M)

theorem bot_inv : (botIso M schedule).inv = fromBase M schedule ⊥ := by
  have h := (ConstructionIteration.botIso (Under.mk (𝟙 M)) (step M schedule)).inv.w
  change (𝟙 M) ≫ (botIso M schedule).inv = fromBase M schedule ⊥ at h
  simpa only [Category.id_comp] using h

theorem preservesProfiles (i j : J) (hij : i ≤ j) :
    PreservesProfiles ((functor M schedule).map (homOfLE hij)) := by
  apply ContinuousTower.preservesProfiles
  intro k hk
  rw [map_succ M schedule k hk]
  exact (PreservesProfiles.operation _).comp (PreservesProfiles.of_iso (succIso M schedule k hk).symm)

theorem fromBase_preservesProfiles (j : J) : PreservesProfiles (fromBase M schedule j) := by
  rw [← fromBase_naturality M schedule (bot_le : (⊥ : J) ≤ j), ← bot_inv]
  exact (PreservesProfiles.of_iso (botIso M schedule).symm).comp
    (preservesProfiles M schedule _ _ bot_le)

theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hJ : Cardinal.mk J ≤ μ) (hM : Cardinal.mk M ≤ μ) (j : J) :
    Cardinal.mk ((functor M schedule).obj j) ≤ μ := by
  apply ContinuousTower.cardinal_le _ hω hJ
  · rw [Cardinal.mk_congr (isoEquiv (botIso M schedule))]; exact hM
  · intro k hk h
    rw [Cardinal.mk_congr (isoEquiv (succIso M schedule k hk))]
    exact Request.cardinal_le _ hω h

/-- Executing a scheduled probe provides a full profile, and a genuinely
new element, at every subsequent cut of the round. -/
theorem creates_probe (j : J) (hj : ¬ IsMax j) (d : ProbeData M)
    (hd : schedule j = .inl d) (k : J) (hjk : Order.succ j ≤ k) :
    ∃ m : (functor M schedule).obj k,
      ProbeProfile (fromBase M schedule k d.a) (fromBase M schedule k d.b)
        ((functor M schedule).obj k).e m (fun i => fromBase M schedule k (d.path.node i)) ∧
      ¬ ∃ x : (functor M schedule).obj j,
        (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) x = m := by
  let d' := d.map (fromBase M schedule j)
  let iso : (functor M schedule).obj (Order.succ j) ≅ d'.extension :=
    succIso M schedule j hj ≪≫ eqToIso (by rw [hd]; rfl)
  let f : d'.extension ⟶ (functor M schedule).obj k :=
    iso.inv ≫ (functor M schedule).map (homOfLE hjk)
  have hstep : (functor M schedule).map (homOfLE (Order.le_succ j)) = d'.inclusion ≫ iso.inv := by
    rw [map_succ M schedule j hj]
    dsimp only [iso, Iso.trans_inv]
    rw [← Category.assoc]
    congr 1
    exact Request.inclusion_eq_transport _ _ (congrArg (fun r => r.map (fromBase M schedule j)) hd)
  have htrans : d'.inclusion ≫ f =
      (functor M schedule).map (homOfLE ((Order.le_succ j).trans hjk)) := by
    dsimp only [f]
    rw [← Category.assoc, ← hstep, ← Functor.map_comp, homOfLE_comp]
  have he (x : M) : f (d'.inclusion (fromBase M schedule j x)) = fromBase M schedule k x := by
    change (fromBase M schedule j ≫ d'.inclusion ≫ f) x = _
    rw [htrans, fromBase_naturality]
  have hf : PreservesProfiles f := (PreservesProfiles.of_iso iso.symm).comp
    (preservesProfiles M schedule _ _ hjk)
  refine ⟨f d'.probe,?_,?_⟩
  · have hp := hf _ _ _ _ _ d'.profile
    change ProbeProfile (f (d'.inclusion (fromBase M schedule j d.a)))
      (f (d'.inclusion (fromBase M schedule j d.b))) (f d'.extension.e) (f d'.probe)
      (fun i => f (d'.inclusion (fromBase M schedule j (d.path.node i)))) at hp
    simpa only [he, f.map_e] using hp
  · rintro ⟨x,hx⟩
    rw [← htrans] at hx
    exact d'.probe_new ⟨x,f.injective hx⟩

end Round
end
end PartitionConsistency.MonoidConstruction


/-! ## Index -/

namespace PartitionConsistency.MonoidConstruction
universe u v
open CategoryTheory CategoryTheory.Limits DiagramOrder
noncomputable section
open scoped Classical

/-- A chosen well-order on a type of requests; nothing is quotiented or omitted. -/
def WellOrdered (A : Type u) := A
namespace WellOrdered
variable (A : Type u)
instance : LinearOrder (WellOrdered A) := linearOrderOfSTO WellOrderingRel
instance : WellFoundedLT (WellOrdered A) := WellOrderingRel.isWellOrder.wf
instance [Nonempty A] : Nonempty (WellOrdered A) := inferInstanceAs (Nonempty A)
instance [Nonempty A] : OrderBot (WellOrdered A) := WellFoundedLT.toOrderBot _
instance [Nonempty A] : ConditionallyCompleteLinearOrderBot (WellOrdered A) :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _
end WellOrdered

abbrev ScheduleIndex (A : Type u) := WithTop (WellOrdered A)
instance (A : Type u) : WellFoundedLT (ScheduleIndex A) := inferInstance
instance (A : Type u) : SuccOrder (ScheduleIndex A) := SuccOrder.ofLinearWellFoundedLT _

namespace Request
variable (M : Object.{u})
def defaultProbe : ProbeData M where
  a := 1
  b := M.e
  b_ne_one := M.e_ne_one
  path := ⟨fun _ => 1,rfl,fun _ => dvd_refl _,fun _ => dvd_refl _⟩
instance : Nonempty (Request M) := ⟨.inl (defaultProbe M)⟩
end Request

end
end PartitionConsistency.MonoidConstruction

end OAI
