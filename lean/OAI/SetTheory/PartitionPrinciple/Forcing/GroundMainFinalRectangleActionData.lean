import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalFulfillmentConstruction

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)
include fulfilled

theorem decoded_rectangle_action_data :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let a := geometry.decodedAction
    ∀ (V W d X : SetMembers geometry.carrier) (g₁ g₂ : SetMembers geometry.actors),
      ExternalRectangleCode geometry.carrier geometry.actors geometry.order
        geometry.meetGraph geometry.action (SetMembers.raw V) (SetMembers.raw W)
        (SetMembers.raw d) (SetMembers.raw g₁) (SetMembers.raw g₂) →
      a.iso g₁ d ≤ X → a.iso g₂ d ≤ X →
      ∃ h₁ h₂ : SetMembers geometry.actors,
        RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph geometry.action
          (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw d)
          (SetMembers.raw g₁) (SetMembers.raw g₂) (SetMembers.raw X)
          (SetMembers.raw h₁) (SetMembers.raw h₂) ∧
        g₁⁻¹ * h₁ ∈ a.principalFix V ∧
        g₂⁻¹ * h₂ ∈ a.principalFix V ∧
        h₁⁻¹ * h₂ ∈ a.principalFix W ∧
        geometry.meet.smallMeet (a.iso h₁ d) X = a.iso h₁ V ∧
        geometry.meet.smallMeet (a.iso h₂ d) X = a.iso h₂ V ∧
        geometry.meet.smallMeet (a.iso h₁ d) (a.iso h₂ d) = a.iso h₁ W := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let a := geometry.decodedAction
  dsimp only
  intro V W d X g₁ g₂ request bound₁ bound₂
  have upper (g : SetMembers geometry.actors) (bound : a.iso g d ≤ X) :
      ∀ y ∈ geometry.carrier,
        ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw d)) y ∈ geometry.action →
        ZFSet.pair y (SetMembers.raw X) ∈ geometry.order := by
    intro y hy entry
    have acted := (geometry.action_code.act_eq_iff g d (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entry)
    change ZFSet.pair (SetMembers.raw (geometry.action_code.act g d)) (SetMembers.raw X)
      ∈ geometry.order at bound
    simpa only [acted, SetMembers.raw_ofMem] using bound
  obtain ⟨k, hk, l, hl, rectangle⟩ := fulfilled.rectangles
    _ _ _ _ _ _ request (SetMembers.raw_mem X) (upper g₁ bound₁) (upper g₂ bound₂)
  let h₁ := SetMembers.ofMem k hk
  let h₂ := SetMembers.ofMem l hl
  have code : RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph
      geometry.action (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw d)
      (SetMembers.raw g₁) (SetMembers.raw g₂) (SetMembers.raw X)
      (SetMembers.raw h₁) (SetMembers.raw h₂) := by
    simpa only [h₁, h₂, SetMembers.raw_ofMem] using rectangle
  have agree (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (rawAgree : ActionAgreementBelow geometry.carrier geometry.order geometry.action
        (SetMembers.raw g) (SetMembers.raw h) (SetMembers.raw v)) :
      ∀ i, i ≤ v → a.iso g i = a.iso h i := by
    intro i lower
    apply SetMembers.raw_injective
    exact rawAgree.entry_eq geometry.action_code (SetMembers.raw_mem h) (SetMembers.raw_mem i)
      lower (geometry.action_code.act_mem g i) (geometry.action_code.act_mem h i)
  have agree₁ := agree h₁ g₁ V code.first_agreement
  have agree₂ := agree h₂ g₂ V code.second_agreement
  have agreeW := agree h₁ h₂ W code.common_agreement
  obtain ⟨v, hv, w, hw, y, hy, z, hz, t, ht,
    gv, hwv, ky, lz, kt, _, meet₁, meet₂, meetW⟩ := code.values
  have value (g : SetMembers geometry.actors) (x : SetMembers geometry.carrier)
      (y : ZFSet.{u}) (hy : y ∈ geometry.carrier)
      (entry : ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw x)) y ∈ geometry.action) :
      SetMembers.raw (a.iso g x) = y := by
    have acted := (geometry.action_code.act_eq_iff g x (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entry)
    exact (congrArg SetMembers.raw acted).trans (SetMembers.raw_ofMem y hy)
  have eqv := value g₁ V v hv gv
  have eqw := value g₂ V w hw hwv
  have eqy := value h₁ d y hy ky
  have eqz := value h₂ d z hz lz
  have eqt := value h₁ W t ht kt
  have relative (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (agreement : ∀ i, i ≤ v → a.iso h i = a.iso g i) :
      g⁻¹ * h ∈ a.principalFix v := by
    intro i lower
    rw [a.mul, agreement i lower, a.point_inv_left]
  refine ⟨h₁, h₂, code, relative g₁ h₁ V agree₁, relative g₂ h₂ V agree₂,
    relative h₁ h₂ W (fun i lower => (agreeW i lower).symm), ?_, ?_, ?_⟩
  · rw [agree₁ V le_rfl]
    apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (a.iso h₁ d)) (SetMembers.raw X))
      (SetMembers.raw (a.iso g₁ V)) ∈ geometry.meetGraph
    rw [eqy, eqv]
    exact meet₁
  · rw [agree₂ V le_rfl]
    apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (a.iso h₂ d)) (SetMembers.raw X))
      (SetMembers.raw (a.iso g₂ V)) ∈ geometry.meetGraph
    rw [eqz, eqw]
    exact meet₂
  · apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (a.iso h₁ d))
      (SetMembers.raw (a.iso h₂ d))) (SetMembers.raw (a.iso h₁ W)) ∈ geometry.meetGraph
    rw [eqy, eqz, eqt]
    exact meetW

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end

end OAI
