import OAI.SetTheory.PartitionPrinciple.Transfinite.MainOrdinalSteps

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage

universe u

namespace Transition

def transport {s t s' t' : MainStage.{u}} (f : Transition s t)
    (source : s = s') (target : t = t') : Transition s' t' := by
  cases source
  cases target
  exact f

theorem transport_twice {s t s' t' s'' t'' : MainStage.{u}} (f : Transition s t)
    (hs : s = s') (ht : t = t') (hs' : s' = s'') (ht' : t' = t'') :
    (f.transport hs ht).transport hs' ht' = f.transport (hs.trans hs') (ht.trans ht') := by
  cases hs; cases ht; cases hs'; cases ht'; rfl

theorem transport_comp {s t r s' t' r' : MainStage.{u}}
    (f : Transition s t) (g : Transition t r) (hs : s = s') (ht : t = t') (hr : r = r') :
    (f.comp g).transport hs hr = (f.transport hs ht).comp (g.transport ht hr) := by
  cases hs; cases ht; cases hr; rfl

theorem transport_injective {s t s' t' : MainStage.{u}} (hs : s = s') (ht : t = t') :
    Function.Injective (fun f : Transition s t => f.transport hs ht) := by
  cases hs; cases ht; exact Function.injective_id

end Transition

namespace Diagram
variable {I : Type u} [LinearOrder I]

def restrictLE {i j : I} (d : Diagram (Set.Iic j)) (h : i ≤ j) : Diagram (Set.Iic i) :=
  d.reindex (fun k => ⟨k.val, le_trans k.property h⟩) (fun _ _ h => h)

theorem restrictLE_self {i : I} (d : Diagram (Set.Iic i)) : d.restrictLE (le_refl i) = d := rfl

theorem restrictLE_comp {i j k : I} (d : Diagram (Set.Iic k)) (hij : i ≤ j) (hjk : j ≤ k) :
    (d.restrictLE hjk).restrictLE hij = d.restrictLE (le_trans hij hjk) := rfl

theorem transition_of_eq (d e : Diagram I) (eq : d = e) {i j : I} (h : i ≤ j) :
    (d.transition h).transport (congrArg (fun d => d.stage i) eq)
      (congrArg (fun d => d.stage j) eq) = e.transition h := by cases eq; rfl

theorem ext_of_transport (d e : Diagram I) (stages : ∀ i, d.stage i = e.stage i)
    (transitions : ∀ {i j} (h : i ≤ j),
      (d.transition h).transport (stages i) (stages j) = e.transition h) : d = e := by
  rcases d with ⟨ds, dt, di, dc⟩
  rcases e with ⟨es, et, ei, ec⟩
  have eq : ds = es := funext stages
  cases eq
  have teq : @dt = @et := by
    funext i j h
    exact transitions h
  cases teq
  rfl

variable (f : ∀ i : I, Diagram (Set.Iic i))

def Compatible : Prop := ∀ {i j} (h : i ≤ j), (f j).restrictLE h = f i

namespace Compatible
variable {f} (compatible : Compatible f)

def stage (i : I) : MainStage.{u} := (f i).stage ⟨i, le_refl i⟩

include compatible in
theorem stage_at {i j : I} (h : i ≤ j) :
    stage (f := f) i = (f j).stage ⟨i, h⟩ :=
  congrArg (fun d => d.stage ⟨i, le_refl i⟩) (compatible h).symm

def transition {i j : I} (h : i ≤ j) : Transition (stage (f := f) i) (stage (f := f) j) :=
  ((f j).transition (i := ⟨i, h⟩) (j := ⟨j, le_refl j⟩) h).transport
    (compatible.stage_at h).symm rfl

theorem transition_at {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (compatible.transition hij).transport (compatible.stage_at (le_trans hij hjk))
      (compatible.stage_at hjk) =
    (f k).transition (i := ⟨i, le_trans hij hjk⟩) (j := ⟨j, hjk⟩) hij := by
  unfold transition
  erw [Transition.transport_twice]
  exact transition_of_eq (f j) ((f k).restrictLE hjk) (compatible hjk).symm
    (i := ⟨i, hij⟩) (j := ⟨j, le_refl j⟩) hij

theorem transition_self (i : I) :
    compatible.transition (le_refl i) = Transition.identity (stage (f := f) i) := by
  change (f i).transition (le_refl (⟨i, le_refl i⟩ : Set.Iic i)) = _
  exact (f i).self _

theorem transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    compatible.transition (le_trans hij hjk) =
      (compatible.transition hij).comp (compatible.transition hjk) := by
  apply Transition.transport_injective (compatible.stage_at (le_trans hij hjk))
    (compatible.stage_at (le_refl k))
  dsimp only
  rw [Transition.transport_comp _ _ _ (compatible.stage_at hjk),
    compatible.transition_at hij hjk, compatible.transition_at hjk (le_refl k),
    compatible.transition_at (le_trans hij hjk) (le_refl k)]
  exact (f k).comp (i := ⟨i, le_trans hij hjk⟩) (j := ⟨j, hjk⟩)
    (k := ⟨k, le_refl k⟩) hij hjk

def glue : Diagram I where
  stage := stage (f := f)
  transition := compatible.transition
  self := compatible.transition_self
  comp := compatible.transition_comp

theorem glue_restrict (i : I) :
    compatible.glue.reindex (fun j : Set.Iic i => j.val) (fun _ _ h => h) = f i := by
  apply ext_of_transport _ _ (fun j => compatible.stage_at j.property)
  intro j k h
  exact compatible.transition_at h k.property

end Compatible

end Diagram

end PartitionPilot.Compression.RecursiveMaps.MainStage

end

end OAI
