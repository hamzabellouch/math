import OAI.SetTheory.PartitionPrinciple.Definability.TaskCapFamilyCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem relationImage_identity_on {P F : ZFSet.{u}} (subset : F ⊆ P) :
    relationImage F P (identityFunctionGraph P) = F := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage]
  constructor
  · rintro ⟨_, x, hx, entry⟩
    exact ((pair_mem_identityFunctionGraph P x y).1 entry).1 ▸ hx
  · intro hy
    exact ⟨subset hy, y, hy, (pair_mem_identityFunctionGraph P y y).2 ⟨rfl, subset hy⟩⟩

theorem relationImage_composition_on {P Q V F e f : ZFSet.{u}} (subset : F ⊆ P) :
    relationImage (relationImage F Q e) V f = relationImage F V (relationCompose P Q V e f) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hz, y, hy, yz⟩
    obtain ⟨hy, x, hx, xy⟩ := (mem_relationImage F Q e y).1 hy
    exact ⟨hz, x, hx, (pair_mem_relationCompose P Q V e f x z).2
      ⟨subset hx, hz, y, hy, xy, yz⟩⟩
  · rintro ⟨hz, x, hx, entry⟩
    obtain ⟨_, _, y, hy, xy, yz⟩ := (pair_mem_relationCompose P Q V e f x z).1 entry
    exact ⟨hz, y, (mem_relationImage F Q e y).2 ⟨hy, x, hx, xy⟩, yz⟩

namespace OldProfilePreservationCode

theorem identity (P r μ Filters : ZFSet.{u}) :
    OldProfilePreservationCode P r μ P r μ (identityFunctionGraph P) Filters := by
  intro F _ c _ E _ K _ profile c' _ E' _ K' _ first second third
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P c c').1 first
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P E E').1 second
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P K K').1 third
  rw [relationImage_identity_on profile.filter_subset]
  exact profile

theorem comp_ground (M : TransitiveGround.{u}) (separation : SeparationSchema M.sets)
    {P r μ Q R ν V S ξ e f : ZFSet.{u}}
    (first : OldProfilePreservationCode P r μ Q R ν e (M.groundPower P))
    (second : OldProfilePreservationCode Q R ν V S ξ f (M.groundPower Q))
    (hQ : Q ∈ M.sets) (he : e ∈ M.sets) :
    OldProfilePreservationCode P r μ V S ξ (relationCompose P Q V e f) (M.groundPower P) := by
  intro F hF c hc E hE K hK profile c' hc' E' hE' K' hK' imageC imageE imageK
  obtain ⟨_, _, a, ha, ca, ac⟩ := (pair_mem_relationCompose P Q V e f c c').1 imageC
  obtain ⟨_, _, b, hb, Eb, bE⟩ := (pair_mem_relationCompose P Q V e f E E').1 imageE
  obtain ⟨_, _, d, hd, Kd, dK⟩ := (pair_mem_relationCompose P Q V e f K K').1 imageK
  have intermediate := first F hF c hc E hE K hK profile a ha b hb d hd ca Eb Kd
  have imageGround := M.relationImage_mem separation ((M.mem_groundPower P F).1 hF).1 hQ he
  have imageMember := (M.mem_groundPower Q (relationImage F Q e)).2
    ⟨imageGround, fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1⟩
  have result := second _ imageMember a ha b hb d hd intermediate
    c' hc' E' hE' K' hK' ac bE dK
  rw [relationImage_composition_on profile.filter_subset] at result
  exact result

end OldProfilePreservationCode

theorem TransitiveGround.realize_groundOldProfilePreservation (M : TransitiveGround.{u})
    (powers : SetFormula.Realize M.sets SetFormula.powerSet Fin.elim0)
    {P r μ Q R ν e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hQ : Q ∈ M.sets) (hR : R ∈ M.sets) (hν : ν ∈ M.sets) (he : e ∈ M.sets) :
    SetFormula.Realize M.sets (BoundedFormula.oldProfilePreservationFormula 0 1 2 3 4 5 6 7).toFormula
      (SetFormula.extend P (SetFormula.extend r (SetFormula.extend μ (SetFormula.extend Q
        (SetFormula.extend R (SetFormula.extend ν (SetFormula.extend e
          (SetFormula.extend (M.groundPower P) Fin.elim0)))))))) ↔
      OldProfilePreservationCode P r μ Q R ν e (M.groundPower P) := by
  apply BoundedFormula.realize_oldProfilePreservationFormula
  exact Fin.cases hP (Fin.cases hr (Fin.cases hμ (Fin.cases hQ (Fin.cases hR
    (Fin.cases hν (Fin.cases he (Fin.cases (M.groundPower_mem powers hP)
      (fun j => Fin.elim0 j))))))))

end PartitionPilot.Forcing

end

end OAI
