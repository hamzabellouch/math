import Mathlib
import OAI.Topology.ArtinGroups.Geometry.SphericalCartanPos

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

lemma parabolic_exterior (M:CoxeterMatrix S) (J:Set S) (w:coxeterParabolic M J)
    (v:S → ℝ) (i:S) (hi:i∉J) : representation M.toCoxeterSystem w v i=v i := by
  have hh : ∀ (g:M.Group),g∈coxeterParabolic M J →
      ∀ (v:S → ℝ) (i:S),i∉J → representation M.toCoxeterSystem g v i=v i := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨j,hj,rfl⟩:=hg
      intro v i hi
      have hij:i≠j:=fun h=>hi (h.symm ▸ hj)
      have hr : representation M.toCoxeterSystem (M.simple j)=simpleReflection M j :=
        representation_simple M.toCoxeterSystem j
      rw [hr]
      simp [simpleReflection_apply,hij]
    | one =>
      intro v i hi
      simp only [map_one]
      rfl
    | mul a b ha hb ia ib =>
      intro v i hi
      simp only [map_mul,LinearEquiv.mul_apply]
      rw [ia _ _ hi,ib _ _ hi]
    | inv a ha ia =>
      intro v i hi
      have h:=ia (representation M.toCoxeterSystem a⁻¹ v) i hi
      have hmul : representation M.toCoxeterSystem a
          (representation M.toCoxeterSystem a⁻¹ v)=v := by
        rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
        rfl
      rw [hmul] at h
      exact h.symm
  exact hh w w.property v i hi

noncomputable def coordinateExtension (J:Set S) (v:J → ℝ) : S → ℝ :=
  ∑ j:J,v j • Pi.single (j:S) 1

lemma coordinateExtension_apply (J:Set S) (v:J → ℝ) (j:J) :
    coordinateExtension J v j=v j := by
  simp only [coordinateExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  have he : ∀ x:J,(j:S)=x ↔ j=x := fun x=>Subtype.val_injective.eq_iff
  simp_rw [he]
  simp

lemma coordinateExtension_outside (J:Set S) (v:J → ℝ) (i:S) (hi:i∉J) :
    coordinateExtension J v i=0 := by
  unfold coordinateExtension
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have h:i≠(j:S):=fun h=>hi (h.symm ▸ j.property)
  simp [h]

lemma coordinateExtension_restrict (J:Set S) (v:S → ℝ) (hv:∀ i,i∉J → v i=0) :
    coordinateExtension J (fun i:J=>v i)=v := by
  ext i
  by_cases hi:i∈J
  · exact coordinateExtension_apply J _ ⟨i,hi⟩
  · rw [coordinateExtension_outside J _ i hi,hv i hi]

theorem spherical_dual_chamber_cover (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J)
    (f:(J → ℝ) →ₗ[ℝ] ℝ) :
    ∃ w:coxeterParabolic M J,∃ a:J → ℝ,(∀ i,0 ≤ a i) ∧
      ∀ v:J → ℝ,f v=∑ i,a i*(representation M.toCoxeterSystem w
        (coordinateExtension J v)) i := by
  let : Finite (coxeterParabolic M J):=hJ
  let : Fintype (coxeterParabolic M J):=Fintype.ofFinite _
  let C:=((cartan M).submatrix ((↑):J → S) ((↑):J → S))
  obtain ⟨p,hp⟩:∃ p:J → ℝ,C *ᵥ p=(fun _=>1) := by
    exact (Matrix.mulVec_surjective_iff_isUnit (A:=C)).mpr
      (spherical_cartan_posDef M J hJ).isUnit (fun _=>1)
  let ρ := (representation M.toCoxeterSystem).comp (coxeterParabolic M J).subtype
  let R : (S → ℝ) →ₗ[ℝ] (J → ℝ):=
    { toFun:=fun v i=>v i
      map_add':=by intros; rfl
      map_smul':=by intros; rfl }
  let F : (S → ℝ) →ₗ[ℝ] ℝ:=f.comp R
  obtain ⟨w,_,hw⟩:=Finset.exists_max_image (Finset.univ:Finset (coxeterParabolic M J))
    (fun w=>F (ρ w (coordinateExtension J p))) Finset.univ_nonempty
  let a:J → ℝ:=fun i=>F (ρ w (Pi.single (i:S) 1))
  have ha:∀ i,0 ≤ a i := by
    intro i
    let g:coxeterParabolic M J:=⟨M.simple i,
      Subgroup.subset_closure (Set.mem_image_of_mem _ i.property)⟩
    have hgen:ρ g=simpleReflection M i := representation_simple M.toCoxeterSystem i
    have hrow:(cartan M *ᵥ coordinateExtension J p) i=1 := by
      have hp':(C *ᵥ p) i=1:=congrFun hp i
      unfold coordinateExtension
      rw [Matrix.mulVec_sum,Finset.sum_apply]
      simp only [Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,
        smul_eq_mul,Matrix.col,Matrix.transpose_apply]
      simpa [Matrix.mulVec,dotProduct,C,mul_comm] using hp'
    have h:=hw (w*g) (Finset.mem_univ _)
    simp only [map_mul,LinearEquiv.mul_apply,hgen,simpleReflection_apply,
      hrow,one_smul,map_sub] at h
    dsimp [a]
    linarith
  refine ⟨w⁻¹,a,ha,?_⟩
  intro v
  have hv:ρ w (ρ w⁻¹ (coordinateExtension J v))=coordinateExtension J v := by
    rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  have hv' : ρ w⁻¹ (coordinateExtension J v)=
      ∑ i:J,(ρ w⁻¹ (coordinateExtension J v)) i • Pi.single (i:S) 1 := by
    symm
    apply coordinateExtension_restrict
    intro i hi
    rw [show (ρ w⁻¹ (coordinateExtension J v)) i=
      (coordinateExtension J v) i from parabolic_exterior M J w⁻¹ _ i hi]
    exact coordinateExtension_outside J v i hi
  have hF:F (coordinateExtension J v)=f v := by
    change f (fun i:J=>coordinateExtension J v i)=f v
    congr 1
    funext i
    exact coordinateExtension_apply J v i
  calc
    f v=F (ρ w (ρ w⁻¹ (coordinateExtension J v))) := by rw [hv,hF]
    _ = _ := by
      conv_lhs => rw [hv']
      simp only [map_sum,map_smul,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a,ρ]
      rw [mul_comm]

end HarmonicArtin.Geometric

end OAI
