import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicRetractionAction
import OAI.Topology.ArtinGroups.Coxeter.ArtinCoxeter

namespace OAI

/-! Injectivity of every finite-rank standard Artin parabolic. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

omit [Fintype S] in
private lemma component_of_parabolic (w : M.Group) (hw : w ∈ parabolic cs J) :
    parabolicComponent cs J w=w := by
  have hmin : IsParabolicMinimum cs J (1 : M.Group) := by
    intro a _
    simp only [(cs).length_one,mul_one]
    exact Nat.zero_le _
  have hr : parabolicRep cs J w=1 :=
    parabolicRep_eq_of_decomposition cs J w w 1 hw hmin (mul_one w).symm
  simp only [parabolicComponent,hr,inv_one,mul_one]

lemma parabolicStepLetter_standard (w : M.Group) (hw : w ∈ parabolic cs J) (s : J) :
    parabolicStepLetter cs J w s=some s := by
  have hws : w*(cs).simple s ∈ parabolic cs J :=
    (parabolic cs J).mul_mem hw (simple_mem_parabolic cs J s.property)
  have hv := parabolicStepLetter_value cs J w s
  unfold parabolicStepRatio at hv
  rw [component_of_parabolic M J w hw,component_of_parabolic M J _ hws,inv_mul_cancel_left] at hv
  cases hl : parabolicStepLetter cs J w s with
  | none =>
    rw [hl] at hv
    change 1=(cs).simple s at hv
    have hh := congrArg (cs).length hv
    rw [(cs).length_one,(cs).length_simple] at hh
    omega
  | some t =>
    rw [hl] at hv
    have he : t=s := Subtype.ext (simple_injective cs hv)
    exact congrArg some he

noncomputable def parabolicState (a : Artin R) : M.Group × Artin R :=
  (restrictionHom M J (artinCoxeter R a),a)

/-- On the standard parabolic, the gallery action is its right regular action. -/
theorem parabolicRetractionAction_standard (g a : Artin R) :
    MulOpposite.unop (parabolicRetractionAction M J (restrictedArtinHom M J g))
      (parabolicState M J a)=parabolicState M J (a*g) := by
  let f := (parabolicRetractionAction M J).comp (restrictedArtinHom M J)
  have hg : g ∈ Subgroup.closure (Set.range (generator R)) := by
    rw [show Subgroup.closure (Set.range (generator R))=⊤ from
      PresentedGroup.closure_range_of (braidRelators R)]
    trivial
  change MulOpposite.unop (f g) (parabolicState M J a)=_
  induction hg using Subgroup.closure_induction generalizing a with
  | mem x hx =>
    obtain ⟨s,rfl⟩ := hx
    have hw : restrictionHom M J (artinCoxeter R a) ∈ parabolic cs J :=
      restrictionHom_mem_parabolic M J _
    simp only [f,MonoidHom.comp_apply,restrictedArtinHom_generator,
      parabolicRetractionAction_generator]
    change (restrictionHom M J (artinCoxeter R a)*(cs).simple s,
      a*parabolicStepArtin M J (restrictionHom M J (artinCoxeter R a)) s)=_
    rw [parabolicStepArtin,parabolicStepLetter_standard M J _ hw]
    simp only [Option.toList_some,wordArtin,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      parabolicState,map_mul,artinCoxeter_generator,restrictionHom_simple]
  | one => simp only [map_one,MulOpposite.unop_one,Equiv.Perm.one_apply,mul_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul,MulOpposite.unop_mul]
    change MulOpposite.unop (f y) (MulOpposite.unop (f x) (parabolicState M J a))=_
    rw [ihx,ihy,mul_assoc]
  | inv x hx ih =>
    rw [map_inv,MulOpposite.unop_inv]
    change (MulOpposite.unop (f x)).symm (parabolicState M J a)=_
    apply (MulOpposite.unop (f x)).injective
    simp only [Equiv.apply_symm_apply,ih,inv_mul_cancel_right]

/-- Van der Lek's standard-parabolic injectivity theorem in finite rank,
proved from the Coxeter retraction and the Artin braid presentation. -/
theorem standardArtinEmbedding : Function.Injective (restrictedArtinHom M J) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have ha := parabolicRetractionAction_standard M J g 1
  rw [hg,map_one,MulOpposite.unop_one,Equiv.Perm.one_apply,one_mul] at ha
  exact (congrArg Prod.snd ha).symm

end HarmonicArtin.ParabolicIntersections

end OAI
