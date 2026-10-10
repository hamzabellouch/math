import OAI.SetTheory.PartitionPrinciple.Transfinite.AgreementLimits

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.FiniteRun

universe u
variable (Label : Type u)

noncomputable def stage : Nat → MainStage.{u}
  | 0 => initial
  | n + 1 => (stage n).next Label

noncomputable def step (n : Nat) : Transition (stage Label n) (stage Label (n + 1)) :=
  (stage Label n).nextTransition Label

noncomputable def transition {n m : Nat} (lower : n ≤ m) : Transition (stage Label n) (stage Label m) :=
  Nat.leRecOn lower (fun {k} e => e.comp (step Label k)) (Transition.identity (stage Label n))

theorem transition_self (n : Nat) :
    transition Label (Nat.le_refl n) = Transition.identity (stage Label n) := Nat.leRecOn_self _

theorem transition_step {n m : Nat} (lower : n ≤ m) :
    transition Label (Nat.le_succ_of_le lower) = (transition Label lower).comp (step Label m) :=
  Nat.leRecOn_succ lower _

theorem points_comp {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (x : (stage Label n).Point) :
    (transition Label (Nat.le_trans hnm hmk)).points.toFun x =
      (transition Label hmk).points.toFun ((transition Label hnm).points.toFun x) := by
  induction hmk with
  | refl =>
    rw [transition_self]
    rfl
  | @step k hmk ih =>
    rw [transition_step Label (Nat.le_trans hnm hmk), transition_step Label hmk]
    change (step Label k).points.toFun _ = (step Label k).points.toFun _
    exact congrArg (step Label k).points.toFun ih

theorem actors_comp {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (x : (stage Label n).Actor) :
    (transition Label (Nat.le_trans hnm hmk)).actors x =
      (transition Label hmk).actors ((transition Label hnm).actors x) := by
  induction hmk with
  | refl =>
    rw [transition_self]
    rfl
  | @step k hmk ih =>
    rw [transition_step Label (Nat.le_trans hnm hmk), transition_step Label hmk]
    change (step Label k).actors _ = (step Label k).actors _
    exact congrArg (step Label k).actors ih

abbrev Index := ULift.{u} Nat

noncomputable def orders : MeetSystem Index.{u} where
  system := {
    Point := fun i => (stage Label i.down).Point
    map := fun lower => (transition Label lower).points.toFun
    map_self := by
      intro i x
      rw [transition_self]
      rfl
    map_comp := points_comp Label
    injective := fun lower _ _ eq => embedding_injective (transition Label lower).points eq }
  order i := (stage Label i.down).order
  map_le lower := (transition Label lower).points.le_iff
  map_meet lower := (transition Label lower).points.map_meet

noncomputable def groups : GroupSystem Index.{u} where
  system := {
    Point := fun i => (stage Label i.down).Actor
    map := fun lower => (transition Label lower).actors
    map_self := by
      intro i x
      rw [transition_self]
      rfl
    map_comp := actors_comp Label
    injective := fun lower => (transition Label lower).actors_injective }
  group i := (stage Label i.down).group
  map_one lower := (transition Label lower).actors.map_one
  map_mul lower := (transition Label lower).actors.map_mul

noncomputable def actions : ActionSystem (groups Label) (orders Label) where
  action i := (stage Label i.down).action
  compatible lower g x := ((transition Label lower).equivariant g x).symm

noncomputable def heights : (orders Label).Heights
    (RationalHeights.lexOrder CountableColumns.order).toHeightOrder where
  height i := (stage Label i.down).height
  coherent lower := (transition Label lower).height

theorem agreements : (actions Label).PreservesAgreements :=
  fun lower => (transition Label lower).agreement

theorem step_strict_top (n : Nat) (x : (stage Label n).Point) :
    ¬ (stage Label (n + 1)).order.le (stage Label (n + 1)).top ((step Label n).points.toFun x) :=
  (stage Label n).next_strict_top Label x

end PartitionPilot.Compression.RecursiveMaps.MainStage.FiniteRun



namespace PartitionPilot.Compression.RecursiveMaps.MainStage.FiniteRun

open RationalHeights
universe u
variable (Label : Type u)

noncomputable def omegaHeight : StrictHeight (orders Label).boundedOrder
    (lexOrder CountableColumns.order).toHeightOrder :=
  (heights Label).limitHeight (fun i => ((stage Label i.down).height.value (stage Label i.down).top).1)
    ((heights Label).stage_bound_from_top (fun i => (stage Label i.down).top)
      (fun i => (stage Label i.down).greatest))

theorem omegaHeight_stage (i : Index.{u}) (x : (stage Label i.down).Point) :
    (omegaHeight Label).value (((orders Label).boundedInclusion i).toFun x) =
      (stage Label i.down).height.value x := rfl

theorem omegaHeight_countable : CountableRange (omegaHeight Label).value :=
  (heights Label).limitHeight_countable _ _ (fun i => (stage Label i.down).countable_height)

theorem union_bottom_at (i : Index.{u}) :
    (orders Label).system.point i (stage Label i.down).bottom =
      (orders Label).system.point ⟨0⟩ (stage Label 0).bottom := by
  have eq := (transition Label (Nat.zero_le i.down)).bottom
  have raised := congrArg ((orders Label).system.point i) eq
  exact raised.symm.trans ((orders Label).system.point_map (i := ⟨0⟩) (j := i)
    (Nat.zero_le i.down) (stage Label 0).bottom)

theorem union_bottom_least (x : (orders Label).system.Union) :
    (orders Label).unionOrder.le
      ((orders Label).system.point ⟨0⟩ (stage Label 0).bottom) x := by
  rcases (orders Label).system.cover x with ⟨i, x, rfl⟩
  rw [← union_bottom_at Label i]
  exact ((orders Label).le_stage i _ x).mpr ((stage Label i.down).least x)

noncomputable def omega : MainStage.{u} where
  Point := Option (orders Label).system.Union
  order := (orders Label).boundedOrder
  Actor := (groups Label).system.Union
  action := (actions Label).topAction
  bottom := some ((orders Label).system.point ⟨0⟩ (stage Label 0).bottom)
  least x := by
    cases x with
    | none => exact True.intro
    | some x => exact union_bottom_least Label x
  top := none
  greatest := FixedTop.greatest (orders Label).unionOrder
  height := omegaHeight Label
  countable_height := omegaHeight_countable Label

noncomputable def omegaTransition (n : Nat) : Transition (stage Label n) (omega Label) where
  points := (orders Label).boundedInclusion ⟨n⟩
  actors := (groups Label).inclusion ⟨n⟩
  actors_injective := (groups Label).inclusion_injective ⟨n⟩
  equivariant := (actions Label).topAction_stage ⟨n⟩
  bottom := congrArg some (union_bottom_at Label ⟨n⟩)
  height := omegaHeight_stage Label ⟨n⟩
  agreement := (actions Label).top_agreement (agreements Label) ⟨n⟩

theorem omega_points_coherent {n m : Nat} (lower : n ≤ m) (x : (stage Label n).Point) :
    (omegaTransition Label m).points.toFun ((transition Label lower).points.toFun x) =
      (omegaTransition Label n).points.toFun x :=
  congrArg some ((orders Label).system.point_map (i := ⟨n⟩) (j := ⟨m⟩) lower x)

theorem omega_actors_coherent {n m : Nat} (lower : n ≤ m) (g : (stage Label n).Actor) :
    (omegaTransition Label m).actors ((transition Label lower).actors g) =
      (omegaTransition Label n).actors g :=
  (groups Label).system.point_map (i := ⟨n⟩) (j := ⟨m⟩) lower g

theorem omega_strict_top (n : Nat) (x : (stage Label n).Point) :
    ¬ (omega Label).order.le (omega Label).top ((omegaTransition Label n).points.toFun x) :=
  ((orders Label).bounded_strict_top ⟨n⟩ x).2

theorem omega_point_cover (x : (omega Label).Point) :
    x = (omega Label).top ∨ ∃ n y, (omegaTransition Label n).points.toFun y = x := by
  cases x with
  | none => exact Or.inl rfl
  | some x =>
    rcases (orders Label).system.cover x with ⟨i, y, rfl⟩
    exact Or.inr ⟨i.down, y, rfl⟩

theorem omega_actor_cover (g : (omega Label).Actor) :
    ∃ n h, (omegaTransition Label n).actors h = g := by
  rcases (groups Label).system.cover g with ⟨i, h, rfl⟩
  exact ⟨i.down, h, rfl⟩

noncomputable def countableOrdinalLabelsOmega : MainStage.{1} := omega CountableColumns.Column

end PartitionPilot.Compression.RecursiveMaps.MainStage.FiniteRun



namespace PartitionPilot.Compression.RecursiveMaps.MainStage

universe u

namespace Transition

theorem ext {s t : MainStage.{u}} (f g : Transition s t)
    (points : ∀ x, f.points.toFun x = g.points.toFun x)
    (actors : ∀ x, f.actors x = g.actors x) : f = g := by
  have embedding_ext (p q : MeetEmbedding s.order t.order)
      (h : ∀ x, p.toFun x = q.toFun x) : p = q := by
    cases p
    cases q
    congr
    exact funext h
  have ep : f.points = g.points := embedding_ext _ _ points
  have eg : f.actors = g.actors := MonoidHom.ext actors
  cases f
  cases g
  cases ep
  cases eg
  rfl

theorem identity_comp {s t : MainStage.{u}} (f : Transition s t) :
    (identity s).comp f = f := ext _ _ (fun _ => rfl) (fun _ => rfl)

theorem comp_identity {s t : MainStage.{u}} (f : Transition s t) :
    f.comp (identity t) = f := ext _ _ (fun _ => rfl) (fun _ => rfl)

theorem comp_assoc {s t r q : MainStage.{u}}
    (f : Transition s t) (g : Transition t r) (h : Transition r q) :
    (f.comp g).comp h = f.comp (g.comp h) := ext _ _ (fun _ => rfl) (fun _ => rfl)

end Transition

structure Diagram (I : Type u) [LinearOrder I] where
  stage : I → MainStage.{u}
  transition : ∀ {i j}, i ≤ j → Transition (stage i) (stage j)
  self : ∀ i, transition (le_refl i) = Transition.identity (stage i)
  comp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
    transition (le_trans hij hjk) = (transition hij).comp (transition hjk)

namespace Diagram
variable {I : Type u} [LinearOrder I] (d : Diagram I)

def reindex {J : Type u} [LinearOrder J] (f : J → I) (mono : Monotone f) : Diagram J where
  stage i := d.stage (f i)
  transition h := d.transition (mono h)
  self i := d.self (f i)
  comp hij hjk := d.comp (mono hij) (mono hjk)

def constant (s : MainStage.{u}) : Diagram I where
  stage _ := s
  transition _ := Transition.identity s
  self _ := rfl
  comp _ _ := (Transition.identity_comp _).symm

def orders : MeetSystem I where
  system := {
    Point := fun i => (d.stage i).Point
    map := fun lower => (d.transition lower).points.toFun
    map_self := by intro i x; rw [d.self]; rfl
    map_comp := by
      intro i j k hij hjk x
      rw [d.comp hij hjk]
      rfl
    injective := fun h _ _ eq => embedding_injective (d.transition h).points eq }
  order i := (d.stage i).order
  map_le h := (d.transition h).points.le_iff
  map_meet h := (d.transition h).points.map_meet

def groups : GroupSystem I where
  system := {
    Point := fun i => (d.stage i).Actor
    map := fun lower => (d.transition lower).actors
    map_self := by intro i x; rw [d.self]; rfl
    map_comp := by
      intro i j k hij hjk x
      rw [d.comp hij hjk]
      rfl
    injective := fun h => (d.transition h).actors_injective }
  group i := (d.stage i).group
  map_one h := (d.transition h).actors.map_one
  map_mul h := (d.transition h).actors.map_mul

def actions : ActionSystem d.groups d.orders where
  action i := (d.stage i).action
  compatible h g x := ((d.transition h).equivariant g x).symm

def heights : d.orders.Heights
    (RationalHeights.lexOrder CountableColumns.order).toHeightOrder where
  height i := (d.stage i).height
  coherent h := (d.transition h).height

theorem agreements [Nonempty I] : d.actions.PreservesAgreements :=
  fun h => (d.transition h).agreement

structure Cone where
  apex : MainStage.{u}
  leg : ∀ i, Transition (d.stage i) apex
  coherent : ∀ {i j} (h : i ≤ j), (d.transition h).comp (leg j) = leg i

def Cone.extend (c : d.Cone) {s : MainStage.{u}} (e : Transition c.apex s) : d.Cone where
  apex := s
  leg i := (c.leg i).comp e
  coherent h := by rw [← Transition.comp_assoc, c.coherent h]

def Cone.reindex (c : d.Cone) {J : Type u} [LinearOrder J]
    (f : J → I) (mono : Monotone f) : (d.reindex f mono).Cone where
  apex := c.apex
  leg i := c.leg (f i)
  coherent h := c.coherent (mono h)

end Diagram

noncomputable def FiniteRun.diagram (Label : Type u) : Diagram FiniteRun.Index.{u} where
  stage i := FiniteRun.stage Label i.down
  transition h := FiniteRun.transition Label h
  self i := FiniteRun.transition_self Label i.down
  comp hij hjk := Transition.ext _ _
    (FiniteRun.points_comp Label hij hjk) (FiniteRun.actors_comp Label hij hjk)

end PartitionPilot.Compression.RecursiveMaps.MainStage

end

end OAI
