import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMeetGeneratorSteps
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundOrdinarySubmodelReflection

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundMeetFilters (P r μ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (MeetFilterCode P r μ) (M.groundPower P)

theorem mem_groundMeetFilters (P r μ F : ZFSet.{u}) :
    F ∈ M.groundMeetFilters P r μ ↔ F ∈ M.sets ∧ MeetFilterCode P r μ F := by
  rw [groundMeetFilters, ZFSet.mem_sep, M.mem_groundPower]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.subset⟩, h.2⟩⟩

theorem groundMeetFilters_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {P r μ : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundMeetFilters P r μ ∈ M.sets := by
  let params := extend P (extend r (extend μ Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.meetFilterFormula 1 2 3 0) params
    (Fin.cases hP (Fin.cases hr (Fin.cases hμ (fun i => Fin.elim0 i))))
    (M.groundPower_mem powers hP)
  have equal : ZFSet.sep (fun F => BoundedFormula.Truth
      (BoundedFormula.meetFilterFormula 1 2 3 0) (extend F params)) (M.groundPower P) =
      M.groundMeetFilters P r μ := by
    apply ZFSet.ext
    intro F
    rw [ZFSet.mem_sep, groundMeetFilters, ZFSet.mem_sep]
    exact and_congr_right (fun _ =>
      BoundedFormula.truth_meetFilterFormula 1 2 3 0 (extend F params) meet)
  exact equal ▸ selected

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def generatedMeetFilter (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (relationImage A P (M.finitePathClosure P (meetGeneratorSteps P μ A))) P r

theorem mem_generatedMeetFilter {P r μ A : ZFSet.{u}} (subset : A ⊆ P) (x : ZFSet.{u}) :
    x ∈ M.generatedMeetFilter P r μ A ↔
      x ∈ P ∧ ∃ a ∈ A, ∃ b ∈ P, ∃ t ∈ M.finiteWords P,
        FiniteRelationPathCode ZFSet.omega P (meetGeneratorSteps P μ A) a b t ∧
          ZFSet.pair b x ∈ r := by
  rw [generatedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨hx, b, hb, lower⟩
    obtain ⟨hbP, a, ha, path⟩ := (mem_relationImage _ _ _ b).1 hb
    obtain ⟨_, _, t, ht, code⟩ := (M.pair_mem_finitePathClosure_iff _ _ a b).1 path
    exact ⟨hx, a, ha, b, hbP, t, ht, code, lower⟩
  · rintro ⟨hx, a, ha, b, hb, t, ht, code, lower⟩
    exact ⟨hx, b, (mem_relationImage _ _ _ b).2 ⟨hb, a, ha,
      (M.pair_mem_finitePathClosure_iff _ _ a b).2 ⟨subset ha, hb, t, ht, code⟩⟩, lower⟩

theorem generatedMeetFilter_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r μ A : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) : M.generatedMeetFilter P r μ A ∈ M.sets :=
  M.relationImage_mem separation
    (M.relationImage_mem separation hA hP
      (M.finitePathClosure_mem pairing unions powers separation infinite hP
        (M.meetGeneratorSteps_mem pairing unions powers separation hP hμ hA))) hP hr

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions separation infinite

theorem generatedMeetFilter_small_iff {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x : SetMembers P) :
    SetMembers.raw x ∈ M.generatedMeetFilter P r μ A ↔
      generatedMeetPredicate code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x := by
  have paths := M.pair_mem_finitePathClosure pairing unions separation infinite
    (SetMembers.presentation P) (meetGeneratorStep code.toSmallMeetOrder
      (fun a => SetMembers.raw a ∈ A)) (code.meetGeneratorSteps_iff subset) hP
  rw [generatedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨_, b, hb, lower⟩
    obtain ⟨hbP, a, ha, path⟩ := (mem_relationImage _ _ _ b).1 hb
    let a' := SetMembers.ofMem a (subset ha)
    let b' := SetMembers.ofMem b hbP
    have path' : ZFSet.pair (SetMembers.raw a') (SetMembers.raw b') ∈
        M.finitePathClosure P (meetGeneratorSteps P μ A) := by
      simpa only [a', b', SetMembers.raw_ofMem] using path
    refine ⟨a', ?_, b', (paths a' b').1 path', ?_⟩
    · simpa only [a', SetMembers.raw_ofMem] using ha
    · change ZFSet.pair (SetMembers.raw b') (SetMembers.raw x) ∈ r
      simpa only [b', SetMembers.raw_ofMem] using lower
  · rintro ⟨a, ha, b, path, lower⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw b,
      (mem_relationImage _ _ _ _).2 ⟨SetMembers.raw_mem b, SetMembers.raw a, ha,
        (paths a b).2 path⟩, lower⟩

theorem generatedMeetFilter_contains {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) :
    A ⊆ M.generatedMeetFilter P r μ A := by
  intro x hx
  have member := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
    (SetMembers.ofMem x (subset hx))).2
      (generatedMeetPredicate_contains code.toSmallMeetOrder _
        (by simpa only [SetMembers.raw_ofMem] using hx))
  simpa only [SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_filter {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (nonempty : A.Nonempty) :
    MeetFilterCode P r μ (M.generatedMeetFilter P r μ A) := by
  have exactMem := M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
  have typedNonempty : ∃ a : SetMembers P, SetMembers.raw a ∈ A := by
    obtain ⟨a, ha⟩ := nonempty
    exact ⟨SetMembers.ofMem a (subset ha), by
      simpa only [SetMembers.raw_ofMem] using (show a ∈ A from ha)⟩
  let typed := PartitionPilot.generatedMeetFilter code.toSmallMeetOrder
    (fun a => SetMembers.raw a ∈ A) typedNonempty
  have bounded : M.generatedMeetFilter P r μ A ⊆ P :=
    fun x hx => ((mem_relationImage _ _ _ x).1 hx).1
  refine ⟨bounded, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty
    exact ⟨a, M.generatedMeetFilter_contains pairing unions separation infinite hP code subset ha⟩
  · intro x hx y hy lower
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y hy
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have lower' : code.toSmallMeetOrder.le x' y' := by
      change ZFSet.pair (SetMembers.raw x') (SetMembers.raw y') ∈ r
      simpa only [x', y', SetMembers.raw_ofMem] using lower
    have member := (exactMem y').2 (typed.upward hx' lower')
    simpa only [y', SetMembers.raw_ofMem] using member
  · intro x hx y hy z entry
    have hz := (ZFSet.pair_mem_prod.1 (code.operation.1 entry)).2
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y (bounded hy)
    let z' := SetMembers.ofMem z hz
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have hy' : typed.mem y' := (exactMem y').1 (by simpa only [y', SetMembers.raw_ofMem] using hy)
    have equal : code.toSmallMeetOrder.meet x' y' = z' :=
      (code.toSmallMeetOrder_meet_eq_iff x' y' z').2
        (by simpa only [x', y', z', SetMembers.raw_ofMem] using entry)
    have member := (exactMem z').2 (equal ▸ typed.closed_meet hx' hy')
    simpa only [z', SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_least {P r μ A F : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P)
    (filter : MeetFilterCode P r μ F) (contains : A ⊆ F) :
    M.generatedMeetFilter P r μ A ⊆ F := by
  let typed : Compression.MeetFilter code.toSmallMeetOrder := {
    mem := fun x => SetMembers.raw x ∈ F
    nonempty := by
      obtain ⟨x, hx⟩ := filter.nonempty
      exact ⟨SetMembers.ofMem x (filter.subset hx), by
        simpa only [SetMembers.raw_ofMem] using (show x ∈ F from hx)⟩
    upward := fun {x y} hx lower => filter.upward _ hx _ (SetMembers.raw_mem y) lower
    closed_meet := fun {x y} hx hy => filter.closed_meet _ hx _ hy _ (code.smallMeet_entry x y) }
  intro x hx
  have hxP := ((mem_relationImage _ _ _ x).1 hx).1
  let x' := SetMembers.ofMem x hxP
  have predicate := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset x').1
    (by simpa only [x', SetMembers.raw_ofMem] using hx)
  have member := generatedMeetPredicate_least code.toSmallMeetOrder _ typed
    (fun a ha => contains ha) predicate
  simpa only [typed, x', SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_lower_bound {P r μ A e : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P)
    (he : e ∈ P) (above : ∀ a ∈ A, ZFSet.pair e a ∈ r) :
    ∀ x ∈ M.generatedMeetFilter P r μ A, ZFSet.pair e x ∈ r := by
  intro x hx
  have hxP := ((mem_relationImage _ _ _ x).1 hx).1
  let x' := SetMembers.ofMem x hxP
  let e' := SetMembers.ofMem e he
  have predicate := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset x').1
    (by simpa only [x', SetMembers.raw_ofMem] using hx)
  have lower := generatedMeetPredicate_lower_bound code.toSmallMeetOrder _ e'
    (fun a ha => by
      change ZFSet.pair (SetMembers.raw e') (SetMembers.raw a) ∈ r
      simpa only [e', SetMembers.raw_ofMem] using above _ ha) predicate
  change ZFSet.pair (SetMembers.raw e') (SetMembers.raw x') ∈ r at lower
  simpa only [e', x', SetMembers.raw_ofMem] using lower

end TransitiveGround

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem generatedMeetFilter_eq_of_coinitial
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r μ B F : ZFSet.{u}} (hP : P ∈ M.sets) (meet : MeetOrderCode P r μ)
    (filter : MeetFilterCode P r μ F) (subset : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r) :
    M.generatedMeetFilter P r μ B = F := by
  have bounded : B ⊆ P := fun _ hx => filter.subset (subset hx)
  have nonempty : B.Nonempty := by
    obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨b, hb, _⟩ := coinitial x hx
    exact ⟨b, hb⟩
  have generated := M.generatedMeetFilter_filter pairing unions separation infinite hP meet bounded nonempty
  have contains := M.generatedMeetFilter_contains pairing unions separation infinite hP meet bounded
  have least := M.generatedMeetFilter_least pairing unions separation infinite hP meet bounded filter subset
  apply ZFSet.ext
  intro x
  refine ⟨fun hx => least hx, ?_⟩
  intro hx
  obtain ⟨b, hb, lower⟩ := coinitial x hx
  exact generated.upward b (contains hb) x (filter.subset hx) lower

end TransitiveGround

namespace GroundSequenceReflection
variable {M N : TransitiveGround.{u}} {P : ZFSet.{u}}
variable (reflection : GroundSequenceReflection M N P)
include reflection

theorem coinitial_filter
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    {r μ B F : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (meet : MeetOrderCode P r μ) (hB : B ∈ N.sets)
    (small : N.groundEmbeddable B ZFSet.omega)
    (filter : MeetFilterCode P r μ F) (subset : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r) :
    B ∈ M.sets ∧ M.groundEmbeddable B ZFSet.omega ∧
      M.generatedMeetFilter P r μ B = F ∧ F ∈ M.sets := by
  obtain ⟨ground, countable⟩ := reflection.countable_subset pairing unions powers separation infinite choice
    pairingN unionsN powersN separationN infiniteN hP hB
    (fun _ hb => filter.subset (subset hb)) small
  have equal := M.generatedMeetFilter_eq_of_coinitial pairing unions separation infinite
    hP meet filter subset coinitial
  have generatedGround := M.generatedMeetFilter_mem pairing unions powers separation infinite hP hr hμ ground
  exact ⟨ground, countable, equal, equal ▸ generatedGround⟩

end GroundSequenceReflection
end

universe u

noncomputable def testedMeetFilter (F r e : ZFSet.{u}) : ZFSet.{u} :=
  relationImage {e} F r

theorem mem_testedMeetFilter (F r e x : ZFSet.{u}) :
    x ∈ testedMeetFilter F r e ↔ x ∈ F ∧ ZFSet.pair e x ∈ r := by
  rw [testedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨hx, a, ha, edge⟩
    exact ⟨hx, (ZFSet.mem_singleton.1 ha) ▸ edge⟩
  · rintro ⟨hx, edge⟩
    exact ⟨hx, e, ZFSet.mem_singleton.2 rfl, edge⟩

theorem testedMeetFilter_filter {L r meet F e : ZFSet.{u}}
    (code : MeetOrderCode L r meet) (filter : MeetFilterCode L r meet F)
    (he : e ∈ L)
    (directed : ∀ x ∈ L, ∀ y ∈ L, ∃ z ∈ L, ZFSet.pair x z ∈ r ∧ ZFSet.pair y z ∈ r) :
    MeetFilterCode L r meet (testedMeetFilter F r e) := by
  refine ⟨fun x hx => filter.subset ((mem_testedMeetFilter F r e x).1 hx).1, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨z, hz, xz, ez⟩ := directed x (filter.subset hx) e he
    exact ⟨z, (mem_testedMeetFilter F r e z).2 ⟨filter.upward x hx z hz xz, ez⟩⟩
  · intro x hx y hy xy
    have parts := (mem_testedMeetFilter F r e x).1 hx
    exact (mem_testedMeetFilter F r e y).2
      ⟨filter.upward x parts.1 y hy xy, code.order.trans e he x (filter.subset parts.1) y hy parts.2 xy⟩
  · intro x hx y hy z entry
    have px := (mem_testedMeetFilter F r e x).1 hx
    have py := (mem_testedMeetFilter F r e y).1 hy
    exact (mem_testedMeetFilter F r e z).2
      ⟨filter.closed_meet x px.1 y py.1 z entry, code.greatest x y z e he entry px.2 py.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem testedMeetFilter_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (separation : SeparationSchema M.sets)
    {F r e : ZFSet.{u}} (hF : F ∈ M.sets) (hr : r ∈ M.sets) (he : e ∈ M.sets) :
    testedMeetFilter F r e ∈ M.sets :=
  M.relationImage_mem separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing he he) hF hr

end TransitiveGround

end PartitionPilot.Forcing

end OAI
