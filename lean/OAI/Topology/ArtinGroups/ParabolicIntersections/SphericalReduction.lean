import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalProperSupport
import OAI.Topology.ArtinGroups.ParabolicIntersections.AcyclicTwistInput
import OAI.Topology.ArtinGroups.ParabolicIntersections.StabilizerDescent

namespace OAI

/-! The spherical stabilizer containment, Proposition 7.7 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointed_testUpper_exists (Y : Set S) (x : Artin M) :
    ∃ t : ℤ, ∀ L, ClassTestUpper Q (pointedFamily M f x L)
      (Set.range (unfoldedInclusion M Y)) t := by
  have heach (L : PointedLabel M) : ∃ t : ℤ,
      ClassTestUpper Q (pointedFamily M f x L) (Set.range (unfoldedInclusion M Y)) t := by
    obtain ⟨b,hb⟩ := Finite.bddAbove_range (fun i : (minimalClassModel Q (pointedFamily M f x L)).Index =>
      ((minimalClassModel Q (pointedFamily M f x L)).complex.placement i).level)
    exact ⟨b+2, classTestUpper_of_generator_cap Q _ b
      (fun i => hb (Set.mem_range_self i)) _⟩
  choose b hb using heach
  obtain ⟨t,ht⟩ := Finite.bddAbove_range b
  refine ⟨t,?_⟩
  intro L α hα l hl c
  exact hb L α hα l (lt_of_le_of_lt (ht (Set.mem_range_self L)) hl) c

omit [Fintype S] [LinearOrder S] in
/-- Support in a subtype becomes the corresponding ambient standard subgroup. -/
lemma positiveSupport_ambient_mem (Y : Set S) (J : Set Y)
    (a : PositiveArtin (restrictedMatrix M Y))
    (ha : positiveSupport _ a ⊆ J) :
    restrictedArtinHom M Y (positiveToArtin _ a) ∈
      artinParabolic M (Subtype.val '' J) := by
  obtain ⟨w,rfl,hw⟩ := positiveSupport_word_exists _ a J ha
  rw [positiveToArtin_word, restrictedArtinHom_word]
  apply wordArtin_mem_parabolic
  intro s hs
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  exact ⟨i,hw i hi,rfl⟩

/-- The spherical case of the local rank reduction. The positive-height
argument, including its proper-support and containment steps, is proved
here. Only the indicated published categorical and monoid inputs remain. -/
theorem spherical_reduction (Y : Set S) (hY : IsSpherical M Y)
    (hf : f ∉ Y) (hGcd : PublishedFoldingGcd M Y hY)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (hAcyclic : PublishedAcyclicTwist Q)
    (x : Artin M) (hx : x ∈ artinParabolic M {f}ᶜ) :
    ReductionAt M (pointedInitial M f) Y x := by
  rcases Classical.em (∀ L : PointedLabel M, ∀ α ∈ Set.range (unfoldedInclusion M Y),
      ∀ l c : ℤ, ClassTestExact Q α l c (pointedFamily M f x L)) with hExact | hExact
  · apply ReductionAt.fixed
    apply le_antisymm inf_le_left
    intro g hg
    have hfix := pointed_standard_fixes_of_acyclic_tests M f hAcyclic Y x hExact g hg
    change pointedFamily M f (g*x) = pointedFamily M f x at hfix
    refine ⟨hg,?_⟩
    change (fun L => pointedAction M g (pointedAction M x (pointedInitial M f L))) =
      (fun L => pointedAction M x (pointedInitial M f L))
    funext L
    simpa only [pointedFamily,map_mul,Equiv.Perm.mul_apply] using congrFun hfix L
  have hnonzero : ∃ L, ¬ ∀ α ∈ Set.range (unfoldedInclusion M Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f x L) := by
    exact not_forall.mp hExact
  obtain ⟨t,ht⟩ := pointed_testUpper_exists M f Y x
  obtain ⟨p,hp,J,hJ,hcont⟩ :=
    spherical_proper_positive_support M f Y hY hf hGcd hmesh x hx t ht hnonzero
  let N := restrictedMatrix M Y
  let fp := positiveToArtin N
  let F := restrictedArtinHom M Y
  let D : Set S := Subtype.val '' J
  let bp := F (fp p)
  have hDY : D ⊂ Y := by
    refine lt_of_le_of_ne (by rintro s ⟨i,_,rfl⟩; exact i.property) ?_
    intro he
    apply hJ.ne
    apply Set.eq_univ_of_forall
    intro i
    have hi : (i:S) ∈ D := he.symm ▸ i.property
    obtain ⟨j,hj,hji⟩ := hi
    exact Subtype.val_injective hji ▸ hj
  have hbp : bp ∈ artinParabolic M Y := by
    rw [← restrictedArtinHom_range M Y]
    exact ⟨fp p,rfl⟩
  apply ReductionAt.smaller D bp hDY hbp
  intro g hg
  have hfix : pointedFamily M f (g*x)=pointedFamily M f x := by
    have hh := hg.2
    change (fun L => pointedAction M g (pointedAction M x (pointedInitial M f L))) =
      (fun L => pointedAction M x (pointedInitial M f L)) at hh
    funext L
    simpa only [pointedFamily,map_mul,Equiv.Perm.mul_apply] using congrFun hh L
  have hgY := hg.1
  rw [← restrictedArtinHom_range M Y] at hgY
  obtain ⟨a,ha⟩ := hgY
  have hright (z : Artin N) :
      restrictedPointedFamily M f Y x (z*a)=restrictedPointedFamily M f Y x z := by
    funext L
    unfold restrictedPointedFamily pointedFamily
    rw [map_mul F,ha,_root_.mul_assoc,map_mul (pointedAction M),Equiv.Perm.mul_apply,
      map_mul (pointedAction M),Equiv.Perm.mul_apply]
    simpa only [pointedFamily,map_mul,Equiv.Perm.mul_apply] using
      congrArg (pointedAction M (F z)) (congrFun hfix L)
  obtain ⟨r,s,he,hcap⟩ := spherical_common_extension M f Y hY hGcd x (fp p) (fp p*a) t hp
    (by simpa only [hright] using hp)
  have hrJ : positiveSupport N r ⊆ J := hcont r (by simpa only [map_mul] using hcap)
  have hsJ : positiveSupport N s ⊆ J := by
    apply hcont s
    intro L
    have hh := hcap L
    rw [he, ← _root_.mul_assoc, hright] at hh
    simpa only [map_mul] using hh
  have hr := positiveSupport_ambient_mem M Y J r hrJ
  have hs := positiveSupport_ambient_mem M Y J s hsJ
  have heG := congrArg F he
  simp only [map_mul] at heG
  have ha' : F a=g := ha
  rw [ha'] at heG
  rw [mem_conjugate,inv_inv]
  have hrewrite : bp*g*bp⁻¹=(F (fp s))⁻¹*F (fp r) := by
    dsimp only [bp]
    apply (mul_left_cancel_iff (a := F (fp s))).mp
    calc
      F (fp s) * (F (fp p)*g*(F (fp p))⁻¹) =
          (F (fp s)*(F (fp p)*g))*(F (fp p))⁻¹ := by group
      _ = (F (fp r)*F (fp p))*(F (fp p))⁻¹ := by rw [← heG]
      _ = F (fp s)*((F (fp s))⁻¹*F (fp r)) := by group
  rw [hrewrite]
  exact (artinParabolic M D).mul_mem ((artinParabolic M D).inv_mem hs) hr

end HarmonicArtin.ParabolicIntersections

end OAI
