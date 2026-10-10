import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.RestrictionHomRange

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def IsParabolicLongest (T:Set S) (z:M.Group) : Prop :=
  z∈coxeterParabolic M T ∧ ∀w∈coxeterParabolic M T,
    M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z

lemma exists_parabolic_longest (T:Set S) (hT:IsSpherical M T) :
    ∃z:M.Group,IsParabolicLongest M T z := by
  let : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M T).toCoxeterSystem
  refine ⟨restrictionHom M T z,Geometric.restrictionHom_mem_parabolic M T z,?_⟩
  intro w hw
  have hr:w∈(restrictionHom M T).range:=by rw [restrictionHom_range_eq];exact hw
  obtain ⟨v,rfl⟩:=hr
  simpa only [restriction_length] using hz v

lemma parabolic_longest_length_mul (T:Set S) (z:M.Group) (hz:IsParabolicLongest M T z)
    (w:M.Group) (hw:w∈coxeterParabolic M T) :
    M.toCoxeterSystem.length (z*w)+M.toCoxeterSystem.length w=M.toCoxeterSystem.length z := by
  have hr:∀x∈coxeterParabolic M T,∃q:(restrictedMatrix M T).Group,restrictionHom M T q=x:=by
    intro x hx
    exact (show x∈(restrictionHom M T).range by rw [restrictionHom_range_eq];exact hx)
  obtain ⟨q,rfl⟩:=hr z hz.1
  obtain ⟨r,rfl⟩:=hr w hw
  have hq:∀v:(restrictedMatrix M T).Group,(restrictedMatrix M T).toCoxeterSystem.length v≤
      (restrictedMatrix M T).toCoxeterSystem.length q:=by
    intro v
    simpa only [restriction_length] using hz.2 _ (Geometric.restrictionHom_mem_parabolic M T v)
  rw [←map_mul,restriction_length,restriction_length,restriction_length]
  exact length_mul_of_all_descents (restrictedMatrix M T).toCoxeterSystem q
    (all_descents_of_longest (restrictedMatrix M T).toCoxeterSystem q hq) r

lemma parabolic_longest_inverse (T:Set S) (z:M.Group) (hz:IsParabolicLongest M T z) : z⁻¹=z := by
  have hh:=parabolic_longest_length_mul M T z hz z hz.1
  have hz2:z*z=1:=M.toCoxeterSystem.length_eq_zero_iff.mp (by omega)
  calc z⁻¹=z⁻¹*(z*z):=by rw [hz2,mul_one]
       _=z:=by group

lemma parabolic_longest_complement_minimum (R T:Set S) (hRT:R⊆T)
    (zR zT:M.Group) (hR:IsParabolicLongest M R zR) (hT:IsParabolicLongest M T zT) :
    ∀v:coxeterParabolic M R,
      M.toCoxeterSystem.length (zT*zR⁻¹)≤M.toCoxeterSystem.length (zT*zR⁻¹*v) := by
  intro v
  have hRm: zR⁻¹∈coxeterParabolic M R:=(coxeterParabolic M R).inv_mem hR.1
  have hTm: zR⁻¹∈coxeterParabolic M T:=coxeterParabolic_mono M hRT hRm
  have hl:=parabolic_longest_length_mul M T zT hT zR⁻¹ hTm
  have hm: zR⁻¹*v∈coxeterParabolic M R:=(coxeterParabolic M R).mul_mem hRm v.property
  have hl':=parabolic_longest_length_mul M T zT hT (zR⁻¹*v) (coxeterParabolic_mono M hRT hm)
  have hb:=hR.2 _ hm
  rw [M.toCoxeterSystem.length_inv] at hl
  rw [←mul_assoc] at hl'
  omega

theorem lifted_top_face (R T:Set S) (hRs:IsSpherical M R) (hTs:IsSpherical M T) (hRT:R⊆T)
    (zR zT:M.Group) (hR:IsParabolicLongest M R zR) (hT:IsParabolicLongest M T zT)
    (a:Artin M) :
    LiftedFace M (a*positiveLift M zT*(positiveLift M zR)⁻¹,⟨R,hRs⟩) (a,⟨T,hTs⟩) := by
  let p:=zT*zR⁻¹
  have hp:p∈coxeterParabolic M T:=(coxeterParabolic M T).mul_mem hT.1
    (coxeterParabolic_mono M hRT ((coxeterParabolic M R).inv_mem hR.1))
  obtain ⟨u,hu,hr,he⟩:=(mem_parabolic_iff_reduced_word M.toCoxeterSystem T p).mp hp
  change wordCoxeter M u=p at he
  have hlen:M.toCoxeterSystem.length (p*zR)=M.toCoxeterSystem.length p+M.toCoxeterSystem.length zR:=by
    have hh:=parabolic_longest_length_mul M T zT hT zR⁻¹
      (coxeterParabolic_mono M hRT ((coxeterParabolic M R).inv_mem hR.1))
    simp only [M.toCoxeterSystem.length_inv] at hh
    dsimp [p]
    rw [inv_mul_cancel_right]
    exact hh.symm
  have hpos:positiveLift M zT=positiveLift M p*positiveLift M zR:=by
    simpa only [p,inv_mul_cancel_right] using positiveLift_mul M p zR hlen
  refine ⟨hRT,u,hu,hr.eq,?_,?_⟩
  · rw [he]
    exact parabolic_longest_complement_minimum M R T hRT zR zT hR hT
  · change a*positiveLift M zT*(positiveLift M zR)⁻¹=a*wordArtin M u
    rw [hpos,←he,positiveLift_word M u hr]
    group

theorem lifted_same_top_le (R T:Set S) (hRs:IsSpherical M R) (hTs:IsSpherical M T) (hRT:R⊆T)
    (zR zT:M.Group) (hR:IsParabolicLongest M R zR) (hT:IsParabolicLongest M T zT)
    (b:Artin M) :
    (b*(positiveLift M zR)⁻¹,⟨R,hRs⟩)≤
      ((b*(positiveLift M zT)⁻¹,⟨T,hTs⟩):LiftedCell M) := by
  apply (lifted_le_iff_face M _ _).mpr
  have h:=lifted_top_face M R T hRs hTs hRT zR zT hR hT (b*(positiveLift M zT)⁻¹)
  simpa only [mul_assoc,inv_mul_cancel_left] using h

end HarmonicArtin

end OAI
