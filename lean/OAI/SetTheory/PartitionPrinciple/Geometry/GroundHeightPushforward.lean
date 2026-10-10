import OAI.SetTheory.PartitionPrinciple.Definability.FlatCopyGraphRealization
import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyPresentation
import OAI.SetTheory.PartitionPrinciple.Geometry.SeparationTileCodes

namespace OAI

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)
variable {P : MeetOrder A} {Q : MeetOrder B} (embedding : MeetEmbedding P Q)
variable {r μ v ν : ZFSet.{u}}
variable (source : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)
variable (target : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ v ↔ Q.le x y)
variable (sourceMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode z) ∈ μ ↔ P.meet x y = z)
variable (targetMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y)) (t.encode z) ∈ ν ↔ Q.meet x y = z)

include source target sourceMeet targetMeet in
theorem meetEmbeddingCode : MeetEmbeddingCode s.carrier t.carrier r v μ ν (s.graph t embedding.toFun) := by
  have injective : Function.Injective embedding.toFun := by
    intro x y equal
    apply P.antisymm
    · apply (embedding.le_iff x y).1
      rw [equal]
      exact Q.refl _
    · apply (embedding.le_iff y x).1
      rw [equal]
      exact Q.refl _
  refine ⟨s.graph_injection t _ injective, ?_, ?_⟩
  · intro x y a b lower first second
    have hx := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 first)).1
    have hy := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 second)).1
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    have ha := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 first)).2
    have hb := (ZFSet.pair_mem_prod.1 ((s.graph_isFunc t embedding.toFun).1 second)).2
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    have ea := (s.pair_mem_graph t embedding.toFun x a).1 first
    have eb := (s.pair_mem_graph t embedding.toFun y b).1 second
    apply (target a b).2
    rw [← ea, ← eb]
    exact (embedding.le_iff x y).2 ((source x y).1 lower)
  · intro x y z a b c meet first second third
    have graph := s.graph_isFunc t embedding.toFun
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (graph.1 first)).1
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (graph.1 second)).1
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 (ZFSet.pair_mem_prod.1 (graph.1 third)).1
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 (ZFSet.pair_mem_prod.1 (graph.1 first)).2
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 (ZFSet.pair_mem_prod.1 (graph.1 second)).2
    obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 (ZFSet.pair_mem_prod.1 (graph.1 third)).2
    have ea := (s.pair_mem_graph t embedding.toFun x a).1 first
    have eb := (s.pair_mem_graph t embedding.toFun y b).1 second
    have ec := (s.pair_mem_graph t embedding.toFun z c).1 third
    apply (targetMeet a b c).2
    rw [← ea, ← eb, ← ec, ← (sourceMeet x y z).1 meet]
    exact (embedding.map_meet x y).symm

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) {steps : ZFSet.{u}}
variable (edges : ∀ x y, ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈ steps ↔ f.FlatStep a x y)
variable (hE : s.carrier ∈ M.sets) (hU : t.carrier ∈ M.sets)

theorem flatCopyClassifier_entry_iff (w : External J f.Letters) (x : A) (z : f.Node a) :
    ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x))
      ((M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU).encode z) ∈
      equivalenceClassifier (ZFSet.prod s.carrier t.carrier)
        (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) ↔ (f.copy a w).toFun x = z := by
  rw [M.flatCopyClassifier_eq_graph pairing unions powers separation infinite f a s t edges hE hU]
  exact (s.product t).pair_mem_graph _ _ (w, x) z

theorem flatCopyGeometry_spec {r : ZFSet.{u}}
    (related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ r ↔ P.le x y)
    (hSteps : steps ∈ M.sets) (hr : r ∈ M.sets)
    (hm : (s.product s).graph s (fun gh => gh.1 * gh.2) ∈ M.sets) :
    let q := M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU
    let classifier := equivalenceClassifier (ZFSet.prod s.carrier t.carrier)
      (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps)
    let order := flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r
    let meet := canonicalMeetGraph q.carrier order
    let action := flatCopyActionGraph s.carrier t.carrier q.carrier classifier
      ((s.product s).graph s (fun gh => gh.1 * gh.2))
    q.carrier ∈ M.sets ∧ classifier ∈ M.sets ∧ order ∈ M.sets ∧ meet ∈ M.sets ∧ action ∈ M.sets ∧
      MeetOrderCode q.carrier order meet ∧
      PosetActionCode s.carrier q.carrier ((s.product s).graph s (fun gh => gh.1 * gh.2))
        (s.encode 1) order action ∧
      (∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ order ↔ (f.gluedOrder a).le x y) ∧
      (∀ x y z, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y)) (q.encode z) ∈ meet ↔
        (f.gluedOrder a).meet x y = z) ∧
      (∀ g x y, ZFSet.pair (ZFSet.pair (s.encode g) (q.encode x)) (q.encode y) ∈ action ↔
        f.translate a g x = y) := by
  dsimp only
  let q := M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU
  have ground := M.flatCopyPresentation_ground pairing unions powers separation infinite f a s t edges hE hU hSteps
  have classed := M.flatCopyClassifier_entry_iff pairing unions powers separation infinite f a s t edges hE hU
  have order := flatCopy_order_iff f a s t q classed related
  have hOrder := M.flatCopyOrderGraph_mem pairing unions powers separation hE hU ground.1 ground.2 hr
  exact ⟨ground.1, ground.2, hOrder,
    M.canonicalMeetGraph_mem pairing unions powers separation ground.1 hOrder,
    M.flatCopyActionGraph_mem pairing unions powers separation hE hU ground.1 ground.2 hm,
    flatCopy_meetOrder f a s t q classed related,
    flatCopy_actionCode f a s t q classed related,
    order, q.canonicalMeetGraph_iff (f.gluedOrder a) order,
    flatCopy_action_iff f a s t q classed⟩

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing
universe u

structure IdealEmbeddingCode (P Q rP rQ μP μQ e : ZFSet.{u}) : Prop
    extends MeetEmbeddingCode P Q rP rQ μP μQ e where
  reflect : ∀ x y x' y', ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
    ZFSet.pair x' y' ∈ rQ → ZFSet.pair x y ∈ rP
  ideal : ∀ v v' z, ZFSet.pair v v' ∈ e → z ∈ Q → ZFSet.pair z v' ∈ rQ →
    ∃ x ∈ P, ZFSet.pair x v ∈ rP ∧ ZFSet.pair x z ∈ e

namespace IdealEmbeddingCode
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
include code

theorem order_iff {x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair x x' ∈ e) (second : ZFSet.pair y y' ∈ e) :
    ZFSet.pair x' y' ∈ rQ ↔ ZFSet.pair x y ∈ rP :=
  ⟨code.reflect x y x' y' first second,
    fun lower => code.monotone x y x' y' lower first second⟩

theorem principal_iff {v v' z : ZFSet.{u}}
    (image : ZFSet.pair v v' ∈ e) (hz : z ∈ Q) :
    ZFSet.pair z v' ∈ rQ ↔ ∃ x ∈ P, ZFSet.pair x v ∈ rP ∧ ZFSet.pair x z ∈ e := by
  constructor
  · exact code.ideal v v' z image hz
  · rintro ⟨x, _, lower, entry⟩
    exact code.monotone x v z v' lower entry image

theorem principal_range {top top' z : ZFSet.{u}}
    (greatest : ∀ x ∈ P, ZFSet.pair x top ∈ rP)
    (image : ZFSet.pair top top' ∈ e) (hz : z ∈ Q) :
    ZFSet.pair z top' ∈ rQ ↔ ∃ x ∈ P, ZFSet.pair x z ∈ e := by
  rw [code.principal_iff image hz]
  exact ⟨fun ⟨x, hx, _, entry⟩ => ⟨x, hx, entry⟩,
    fun ⟨x, hx, entry⟩ => ⟨x, hx, greatest x hx, entry⟩⟩

end IdealEmbeddingCode
end PartitionPilot.Forcing

namespace PartitionPilot.SetRealization.Presentation
open Forcing Compression.RecursiveMaps
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)
variable {P : MeetOrder A} {Q : MeetOrder B} (embedding : IdealEmbedding P Q)
variable {r μ v ν : ZFSet.{u}}
variable (source : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)
variable (target : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ v ↔ Q.le x y)
variable (sourceMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode z) ∈ μ ↔ P.meet x y = z)
variable (targetMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y)) (t.encode z) ∈ ν ↔ Q.meet x y = z)

include source target sourceMeet targetMeet in
theorem idealEmbeddingCode : IdealEmbeddingCode s.carrier t.carrier r v μ ν (s.graph t embedding.toFun) := by
  have function := s.graph_isFunc t embedding.toFun
  refine ⟨s.meetEmbeddingCode t embedding.toMeetEmbedding source target sourceMeet targetMeet, ?_, ?_⟩
  · intro x y x' y' first second lower
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (function.1 first)).1
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (function.1 second)).1
    obtain ⟨x', rfl⟩ := (t.mem_carrier x').1 (ZFSet.pair_mem_prod.1 (function.1 first)).2
    obtain ⟨y', rfl⟩ := (t.mem_carrier y').1 (ZFSet.pair_mem_prod.1 (function.1 second)).2
    have firstEq := (s.pair_mem_graph t embedding.toFun x x').1 first
    have secondEq := (s.pair_mem_graph t embedding.toFun y y').1 second
    apply (source x y).2
    apply (embedding.le_iff x y).1
    rw [firstEq, secondEq]
    exact (target x' y').1 lower
  · intro x x' z image hz lower
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (function.1 image)).1
    obtain ⟨x', rfl⟩ := (t.mem_carrier x').1 (ZFSet.pair_mem_prod.1 (function.1 image)).2
    obtain ⟨z, rfl⟩ := (t.mem_carrier z).1 hz
    have imageEq := (s.pair_mem_graph t embedding.toFun x x').1 image
    have below : Q.le z (embedding.toFun x) := imageEq.symm ▸ (target z x').1 lower
    obtain ⟨y, rfl⟩ := embedding.ideal x z below
    exact ⟨s.encode y, s.encode_mem y, (source y x).2 ((embedding.le_iff y x).1 below),
      (s.pair_mem_graph t embedding.toFun y _).2 rfl⟩

end PartitionPilot.SetRealization.Presentation

end

namespace PartitionPilot.Forcing
open SetFormula SetRealization
open Compression.RecursiveMaps Attachment CosetGeometry
universe u

noncomputable def flatCopyEmbeddingGraph (U Q classifier w : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ U, ∃ y ∈ Q, z = ZFSet.pair x y ∧
    ZFSet.pair (ZFSet.pair w x) y ∈ classifier) (ZFSet.prod U Q)

theorem pair_mem_flatCopyEmbeddingGraph (U Q classifier w x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ flatCopyEmbeddingGraph U Q classifier w ↔
      x ∈ U ∧ y ∈ Q ∧ ZFSet.pair (ZFSet.pair w x) y ∈ classifier := by
  rw [flatCopyEmbeddingGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, entry⟩
  · rintro ⟨hx, hy, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, entry⟩

namespace BoundedFormula

def flatCopyEmbeddingEntryFormula {n} (z U Q classifier w : Fin n) : BoundedFormula n :=
  exMem U (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tripleMembershipFormula w.succ.succ 1 0 classifier.succ.succ)))

theorem truth_flatCopyEmbeddingEntryFormula {n}
    (z U Q classifier w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (flatCopyEmbeddingEntryFormula z U Q classifier w) env ↔
      ∃ x ∈ env U, ∃ y ∈ env Q, env z = ZFSet.pair x y ∧
        ZFSet.pair (ZFSet.pair (env w) x) y ∈ env classifier := by
  simp only [flatCopyEmbeddingEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem flatCopyEmbeddingGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U Q classifier w : ZFSet.{u}}
    (hU : U ∈ M.sets) (hQ : Q ∈ M.sets) (hClassifier : classifier ∈ M.sets) (hw : w ∈ M.sets) :
    flatCopyEmbeddingGraph U Q classifier w ∈ M.sets := by
  let params := extend U (extend Q (extend classifier (extend w Fin.elim0)))
  have selected := M.bounded_separation_mem separation (BoundedFormula.flatCopyEmbeddingEntryFormula 0 1 2 3 4)
    params (Fin.cases hU (Fin.cases hQ (Fin.cases hClassifier (Fin.cases hw (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hU hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.flatCopyEmbeddingEntryFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod U Q) = flatCopyEmbeddingGraph U Q classifier w := by
    apply ZFSet.ext
    intro z
    rw [flatCopyEmbeddingGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_flatCopyEmbeddingEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (q : Presentation (f.Node a))
variable {classifier r μ : ZFSet.{u}}
variable (classed : ∀ w x z, ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x)) (q.encode z) ∈ classifier ↔
  (f.copy a w).toFun x = z)

include classed in
theorem flatCopyEmbeddingGraph_eq_graph (w : External J f.Letters) :
    flatCopyEmbeddingGraph t.carrier q.carrier classifier (s.encode w) = t.graph q (f.copy a w).toFun := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨x, rfl⟩ := (t.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (q.mem_carrier y).1 hy
    exact (t.pair_mem_graph q _ x y).2 ((classed w x y).1
      ((pair_mem_flatCopyEmbeddingGraph _ _ _ _ _ _).1 entry).2.2)
  · intro entry
    obtain ⟨x, equal⟩ := (t.mem_graph q (f.copy a w).toFun z).1 entry
    rw [← equal]
    exact (pair_mem_flatCopyEmbeddingGraph _ _ _ _ _ _).2
      ⟨t.encode_mem _, q.encode_mem _, (classed w x _).2 rfl⟩

include classed in
theorem flatCopyEmbeddingGraph_code
    (related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ r ↔ P.le x y)
    (sourceMeet : ∀ x y z, ZFSet.pair (ZFSet.pair (t.encode x) (t.encode y)) (t.encode z) ∈ μ ↔ P.meet x y = z)
    (w : External J f.Letters) :
    let order := flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r
    MeetEmbeddingCode t.carrier q.carrier r order μ (canonicalMeetGraph q.carrier order)
      (flatCopyEmbeddingGraph t.carrier q.carrier classifier (s.encode w)) := by
  dsimp only
  rw [flatCopyEmbeddingGraph_eq_graph f a s t q classed w]
  have order := flatCopy_order_iff f a s t q classed related
  exact t.meetEmbeddingCode q (f.copy a w).toMeetEmbedding related order sourceMeet
    (q.canonicalMeetGraph_iff (f.gluedOrder a) order)

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def pushedHeightGraph (A B H e h : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (relationImage A B e) A H (relationConverse A B e) h

theorem pushedHeightGraph_entry {A B H e h x y z : ZFSet.{u}}
    (embedding : InjectionCode A B e) (height : ZFSet.IsFunc A H h)
    (copy : ZFSet.pair x y ∈ e) :
    ZFSet.pair y z ∈ pushedHeightGraph A B H e h ↔ ZFSet.pair x z ∈ h := by
  have bounds := ZFSet.pair_mem_prod.1 (embedding.function.1 copy)
  rw [pushedHeightGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, a, _, inverse, entry⟩
    have copied := (pair_mem_relationConverse _ _ _ _ _).1 inverse
    have same := embedding.injective a x y copied.2.2 copy
    exact same ▸ entry
  · intro entry
    exact ⟨(mem_relationImage A B e y).2 ⟨bounds.2, x, bounds.1, copy⟩,
      (ZFSet.pair_mem_prod.1 (height.1 entry)).2, x, bounds.1,
      (pair_mem_relationConverse A B e x y).2 ⟨bounds.1, bounds.2, copy⟩, entry⟩

theorem pushedHeightGraph_function {A B H e h : ZFSet.{u}}
    (embedding : InjectionCode A B e) (height : ZFSet.IsFunc A H h) :
    ZFSet.IsFunc (relationImage A B e) H (pushedHeightGraph A B H e h) :=
  relationCompose_function_of_subset embedding.converse_image.function height (fun _ hx => hx)

theorem pushedHeightGraph_range {A B H e h : ZFSet.{u}}
    (embedding : InjectionCode A B e) (height : ZFSet.IsFunc A H h) :
    relationImage (relationImage A B e) H (pushedHeightGraph A B H e h) = relationImage A H h := by
  apply ZFSet.ext
  intro z
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hz, y, hy, entry⟩
    obtain ⟨_, x, hx, copy⟩ := (mem_relationImage A B e y).1 hy
    exact ⟨hz, x, hx, (pushedHeightGraph_entry embedding height copy).1 entry⟩
  · rintro ⟨hz, x, hx, entry⟩
    obtain ⟨y, copy, _⟩ := embedding.function.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (embedding.function.1 copy)).2
    exact ⟨hz, y, (mem_relationImage A B e y).2 ⟨hy, x, hx, copy⟩,
      (pushedHeightGraph_entry embedding height copy).2 entry⟩

theorem pushedHeightGraph_strictLex {A B C D rA rB μA μB e h rD : ZFSet.{u}}
    (embedding : IdealEmbeddingCode A B rA rB μA μB e)
    (height : StrictLexHeightCode A C D rA h rD) :
    StrictLexHeightCode (relationImage A B e) C D rB (pushedHeightGraph A B (ZFSet.prod C D) e h) rD := by
  refine ⟨pushedHeightGraph_function embedding.injection height.function, ?_⟩
  intro x hx y hy c q d v lower different first second
  obtain ⟨_, a, ha, ax⟩ := (mem_relationImage A B e x).1 hx
  obtain ⟨_, b, hb, by'⟩ := (mem_relationImage A B e y).1 hy
  have distinct : a ≠ b := by
    intro same
    subst b
    obtain ⟨_, _, unique⟩ := embedding.injection.function.2 a ha
    exact different ((unique x ax).trans (unique y by').symm)
  exact height.strict a ha b hb c q d v (embedding.reflect a b x y ax by' lower) distinct
    ((pushedHeightGraph_entry embedding.injection height.function ax).1 first)
    ((pushedHeightGraph_entry embedding.injection height.function by').1 second)

namespace TransitiveGround
theorem pushedHeightGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B H e h : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hH : H ∈ M.sets)
    (he : e ∈ M.sets) (hh : h ∈ M.sets) : pushedHeightGraph A B H e h ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation
    (M.relationImage_mem separation hA hB he) hA hH
    (M.relationConverse_mem pairing unions powers separation hA hB he) hh
end TransitiveGround

end PartitionPilot.Forcing

end OAI
