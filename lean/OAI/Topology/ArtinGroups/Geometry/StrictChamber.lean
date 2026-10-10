import Mathlib
import OAI.Topology.ArtinGroups.Geometry.InvariantForm

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

include cs in

lemma exists_strict_chamber : ∃ p:S → ℝ,∀ i,(cartan M *ᵥ p) i=1 := by
  have hu := (cartan_posDef cs).isUnit
  have hs := (Matrix.mulVec_surjective_iff_isUnit (A:=cartan M)).mpr hu
  obtain ⟨p,hp⟩:=hs (fun _=>1)
  exact ⟨p,fun i=>congrFun hp i⟩

theorem dual_chamber_cover (f:(S → ℝ) →ₗ[ℝ] ℝ) :
    ∃ w:W,∃ a:S → ℝ,(∀ i,0 ≤ a i) ∧
      ∀ v:S → ℝ,f v=∑ i,a i*(representation cs w v) i := by
  obtain ⟨p,hp⟩:=exists_strict_chamber cs
  obtain ⟨w,_,hw⟩:=Finset.exists_max_image (Finset.univ:Finset W)
    (fun w=>f (representation cs w p)) Finset.univ_nonempty
  let a:S → ℝ := fun i=>f (representation cs w (Pi.single i 1))
  have ha : ∀ i,0 ≤ a i := by
    intro i
    have h:=hw (w*cs.simple i) (Finset.mem_univ _)
    simp only [map_mul,LinearEquiv.mul_apply,representation_simple,simpleReflection_apply,
      hp,one_smul,map_sub] at h
    dsimp [a]
    linarith
  refine ⟨w⁻¹,a,ha,?_⟩
  intro v
  have hv : representation cs w (representation cs w⁻¹ v)=v := by
    rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  have hv' : representation cs w⁻¹ v=∑ i,(representation cs w⁻¹ v) i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    f v=f (representation cs w (representation cs w⁻¹ v)) := congrArg f hv.symm
    _ = _ := by
      conv_lhs => rw [hv']
      simp only [map_sum,map_smul,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a]
      rw [mul_comm]

end HarmonicArtin.Geometric

end OAI
