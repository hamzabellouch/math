import OAI.SetTheory.PartitionPrinciple.Geometry.FinalProfilePersistence
import OAI.SetTheory.PartitionPrinciple.Geometry.MainInsertion

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u
open CosetGeometry

def HasInsertionFamily {A G : Type u} [Group G] {P : MeetOrder A}
    (a : OrderAction G P) (Label : Type u) (C E D : A) (F : A → Prop) : Prop :=
  ∃ (caps : Label → A) (actors : Label → G),
    (∀ l z, P.le z C → (a.iso (actors l)).toFun z = z) ∧
    (∀ l, P.le ((a.iso (actors l)).toFun D) (caps l)) ∧
    (∀ l, P.le C (caps l) ∧ ¬ P.le (caps l) C) ∧
    (∀ l, ¬ P.le E (caps l)) ∧
    (∀ i j, i ≠ j → P.meet (caps i) (caps j) = C) ∧
    (∀ l x, P.le E x → (F x → P.le (caps l) x) ∧ (¬ F x → P.meet (caps l) x = C))

namespace MainStage.OrdinalRun
open CountableColumns
variable (Label : Type 1)

theorem stage_successor_inserts (a : Column) (C E D : (stage Label a).Point)
    (F : MeetFilter (stage Label a).order)
    (ce : (stage Label a).order.le C E) (strict : ¬ (stage Label a).order.le E C)
    (above : ∀ x, F.mem x → (stage Label a).order.le E x) :
    (transition Label (lt_start a).le).Inserts Label C E D F := by
  apply (Transition.inserts_transport _ (stage_successor Label a) Label C E D F).mp
  rw [transition_successor]
  exact (stage Label a).next_inserts Label C E D F ce strict above

theorem final_inserts_at (a : Column) (C E D : (stage Label a).Point)
    (F : MeetFilter (stage Label a).order)
    (ce : (stage Label a).order.le C E) (strict : ¬ (stage Label a).order.le E C)
    (above : ∀ x, F.mem x → (stage Label a).order.le E x) :
    HasInsertionFamily (finalAction Label) Label
      ((finalInclusion Label a).toFun C) ((finalInclusion Label a).toFun E)
      ((finalInclusion Label a).toFun D) (pushFilter (finalInclusion Label a) F).mem := by
  rcases stage_successor_inserts Label a C E D F ce strict above with
    ⟨caps, actors, fixes, bounds, strictCaps, separators, pairs, profiles⟩
  let tr := transition Label (lt_start a).le
  let inc := finalInclusion Label (start a)
  refine ⟨(fun l => inc.toFun (caps l)), (fun l => finalGroupInclusion Label (start a) (actors l)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l z lower
    have hz : (finalOrder Label).le z (inc.toFun (tr.points.toFun C)) := by
      rw [final_points_coherent Label (lt_start a).le C]
      exact lower
    have agree := final_agreement Label (start a) (actors l) 1 (tr.points.toFun C)
      (fun x hx => (fixes l x hx).trans ((stage Label (start a)).action.one x).symm) z hz
    simpa only [map_one, (finalAction Label).one] using agree
  · intro l
    rw [← final_points_coherent Label (lt_start a).le D, final_action_stage]
    exact (inc.le_iff _ _).mpr (bounds l)
  · intro l
    rw [← final_points_coherent Label (lt_start a).le C]
    exact ⟨(inc.le_iff _ _).mpr (strictCaps l).1,
      fun h => (strictCaps l).2 ((inc.le_iff _ _).mp h)⟩
  · intro l lower
    rw [← final_points_coherent Label (lt_start a).le E] at lower
    exact separators l ((inc.le_iff _ _).mp lower)
  · intro i j different
    rw [← inc.map_meet, pairs i j different]
    exact final_points_coherent Label (lt_start a).le C
  · intro l
    have old : Profile (stage Label (start a)).order (tr.points.toFun C) (tr.points.toFun E)
        (caps l) (imageFamily tr.points F.mem) := by
      intro x hx
      exact ⟨fun hp => (profiles l x hx).1 ((positive_imageFamily tr.points F.mem x).mp hp),
        fun hn => (profiles l x hx).2 (fun hp => hn ((positive_imageFamily tr.points F.mem x).mpr hp))⟩
    have nonempty : ∃ x, imageFamily tr.points F.mem x := by
      rcases F.nonempty with ⟨x, hx⟩
      exact ⟨tr.points.toFun x, x, hx, rfl⟩
    have persists := final_preservesProfiles Label (start a) (tr.points.toFun C) (tr.points.toFun E)
      (caps l) (imageFamily tr.points F.mem) nonempty (separators l) old
    have coherent : compose tr.points inc = finalInclusion Label a :=
      meetEmbedding_ext _ _ (final_points_coherent Label (lt_start a).le)
    intro x lower
    have hx : (finalOrder Label).le (inc.toFun (tr.points.toFun E)) x := by
      rw [final_points_coherent Label (lt_start a).le E]
      exact lower
    have positive := positiveOver_imageFamily tr.points inc F.mem x
    rw [coherent] at positive
    have result := persists x hx
    constructor
    · intro hp
      exact result.1 (positive.mpr hp)
    · intro hn
      exact (result.2 (fun hp => hn (positive.mp hp))).trans (final_points_coherent Label (lt_start a).le C)

end MainStage.OrdinalRun

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
