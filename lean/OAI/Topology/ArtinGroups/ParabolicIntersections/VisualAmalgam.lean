import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom
import Mathlib.GroupTheory.PushoutI
import OAI.Topology.ArtinGroups.Coxeter.AlternatingLiftProd

namespace OAI

/-! The actual amalgamated-product presentation of a visual splitting.
The factors and edge group are the standard subgroups of the given Artin
group, and the inverse homomorphism is constructed from its braid relators. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)

def visualSide : Bool → Set S
  | false => Y
  | true => Z

noncomputable def visualEdgeInclusion (b : Bool) :
    artinParabolic M (Y∩Z) →* artinParabolic M (visualSide Y Z b) :=
  Subgroup.inclusion (standard_mono M (by cases b <;> simp [visualSide]))

abbrev VisualAmalgam := Monoid.PushoutI (visualEdgeInclusion M Y Z)

noncomputable def visualToArtin : VisualAmalgam M Y Z →* Artin M :=
  Monoid.PushoutI.lift (fun b => (artinParabolic M (visualSide Y Z b)).subtype)
    (artinParabolic M (Y∩Z)).subtype (by intro b; rfl)

lemma visualSplit_cover (hsplit : IsVisualSplit M Y Z) (s : S) : s∈Y ∨ s∈Z := by
  change s∈Y∪Z
  rw [hsplit.1]
  trivial

lemma visualSplit_finite_edge (hsplit : IsVisualSplit M Y Z) (s t : S)
    (hm : M s t≠0) : ∃ b, s∈visualSide Y Z b ∧ t∈visualSide Y Z b := by
  by_cases hsY : s∈Y
  · by_cases htY : t∈Y
    · exact ⟨false,hsY,htY⟩
    · have htZ := (visualSplit_cover M Y Z hsplit t).resolve_left htY
      by_cases hsZ : s∈Z
      · exact ⟨true,hsZ,htZ⟩
      · exact False.elim (hm (hsplit.2.2.2 s ⟨hsY,hsZ⟩ t ⟨htZ,htY⟩))
  · have hsZ := (visualSplit_cover M Y Z hsplit s).resolve_left hsY
    by_cases htZ : t∈Z
    · exact ⟨true,hsZ,htZ⟩
    · have htY := (visualSplit_cover M Y Z hsplit t).resolve_right htZ
      exact False.elim (hm ((M.symmetric s t).trans
        (hsplit.2.2.2 t ⟨htY,htZ⟩ s ⟨hsZ,hsY⟩)))

noncomputable def visualGenerator (hsplit : IsVisualSplit M Y Z) (s : S) : VisualAmalgam M Y Z :=
  if hs : s∈Y then Monoid.PushoutI.of false
    ⟨generator M s,Subgroup.subset_closure ⟨s,hs,rfl⟩⟩
  else Monoid.PushoutI.of true
    ⟨generator M s,Subgroup.subset_closure
      ⟨s,(visualSplit_cover M Y Z hsplit s).resolve_left hs,rfl⟩⟩

lemma visualGenerator_eq (hsplit : IsVisualSplit M Y Z) (b : Bool) (s : S)
    (hs : s∈visualSide Y Z b) :
    visualGenerator M Y Z hsplit s=Monoid.PushoutI.of b
      ⟨generator M s,Subgroup.subset_closure ⟨s,hs,rfl⟩⟩ := by
  cases b with
  | false => simp [visualGenerator,show s∈Y from hs]
  | true =>
    by_cases hy : s∈Y
    · let x : artinParabolic M (Y∩Z) :=
        ⟨generator M s,Subgroup.subset_closure ⟨s,⟨hy,hs⟩,rfl⟩⟩
      rw [visualGenerator,dite_eq_left hy]
      exact (Monoid.PushoutI.of_apply_eq_base (visualEdgeInclusion M Y Z) false x).trans
        (Monoid.PushoutI.of_apply_eq_base (visualEdgeInclusion M Y Z) true x).symm
    · simp [visualGenerator,hy]

lemma visualWord (hsplit : IsVisualSplit M Y Z) (b : Bool) (w : List S)
    (hw : ∀ s∈w, s∈visualSide Y Z b) :
    (w.map (visualGenerator M Y Z hsplit)).prod=Monoid.PushoutI.of b
      ⟨wordArtin M w,wordArtin_mem_parabolic M _ w hw⟩ := by
  induction w with
  | nil => exact (MonoidHom.map_one _).symm
  | cons s w ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [visualGenerator_eq M Y Z hsplit b s (hw s (by simp)),
      ih (fun t ht => hw t (List.mem_cons_of_mem s ht)),←map_mul]
    congr 1

lemma visual_relators (hsplit : IsVisualSplit M Y Z) : ∀ r∈braidRelators M,
    FreeGroup.lift (visualGenerator M Y Z hsplit) r=1 := by
  rintro r ⟨⟨s,t⟩,rfl⟩
  by_cases hm : M s t=0
  · simp [hm,alternating]
  · obtain ⟨b,hs,ht⟩ := visualSplit_finite_edge M Y Z hsplit s t hm
    have hw : ∀ i∈altList s t (M s t), i∈visualSide Y Z b := by
      intro i hi
      rcases (show i=s ∨ i=t by simpa using mem_altList s t _ i hi) with rfl|rfl
      · exact hs
      · exact ht
    have hw' : ∀ i∈altList t s (M s t), i∈visualSide Y Z b := by
      intro i hi
      rcases (show i=t ∨ i=s by simpa using mem_altList t s _ i hi) with rfl|rfl
      · exact ht
      · exact hs
    rw [map_mul,map_inv,alternating_lift_prod,alternating_lift_prod,
      visualWord M Y Z hsplit b _ hw,visualWord M Y Z hsplit b _ hw']
    apply mul_inv_eq_one.mpr
    congr 1
    apply Subtype.ext
    exact wordArtin_braid M s t

noncomputable def visualFromArtin (hsplit : IsVisualSplit M Y Z) : Artin M →* VisualAmalgam M Y Z :=
  PresentedGroup.toGroup (visual_relators M Y Z hsplit)

@[simp] lemma visualFromArtin_generator (hsplit : IsVisualSplit M Y Z) (s : S) :
    visualFromArtin M Y Z hsplit (generator M s)=visualGenerator M Y Z hsplit s :=
  PresentedGroup.toGroup.of _

@[simp] lemma visualToArtin_generator (hsplit : IsVisualSplit M Y Z) (s : S) :
    visualToArtin M Y Z (visualGenerator M Y Z hsplit s)=generator M s := by
  unfold visualGenerator
  split <;> exact Monoid.PushoutI.lift_of _ _ _ _

lemma visualToArtin_from (hsplit : IsVisualSplit M Y Z) (a : Artin M) :
    visualToArtin M Y Z (visualFromArtin M Y Z hsplit a)=a := by
  have h : (visualToArtin M Y Z).comp (visualFromArtin M Y Z hsplit)=MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro s
    simp only [MonoidHom.comp_apply,MonoidHom.id_apply]
    exact (congrArg (visualToArtin M Y Z) (visualFromArtin_generator M Y Z hsplit s)).trans
      (visualToArtin_generator M Y Z hsplit s)
  exact DFunLike.congr_fun h a

lemma visualFromArtin_factor (hsplit : IsVisualSplit M Y Z) (b : Bool)
    (a : artinParabolic M (visualSide Y Z b)) :
    visualFromArtin M Y Z hsplit a=Monoid.PushoutI.of b a := by
  obtain ⟨a,ha⟩ := a
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    rw [visualFromArtin_generator]
    exact visualGenerator_eq M Y Z hsplit b s hs
  | one =>
    change visualFromArtin M Y Z hsplit 1=Monoid.PushoutI.of b (1 : artinParabolic M (visualSide Y Z b))
    rw [map_one,map_one]
  | mul x y hx hy ihx ihy =>
    change visualFromArtin M Y Z hsplit (x*y)=_
    rw [map_mul,ihx,ihy,←map_mul]
    rfl
  | inv x hx ih =>
    change visualFromArtin M Y Z hsplit x⁻¹=_
    rw [map_inv,ih,←map_inv]
    rfl

lemma visualFromArtin_to (hsplit : IsVisualSplit M Y Z) (a : VisualAmalgam M Y Z) :
    visualFromArtin M Y Z hsplit (visualToArtin M Y Z a)=a := by
  have h : (visualFromArtin M Y Z hsplit).comp (visualToArtin M Y Z)=MonoidHom.id _ := by
    apply Monoid.PushoutI.hom_ext_nonempty
    intro b
    ext a
    simp only [MonoidHom.comp_apply,MonoidHom.id_apply,visualToArtin]
    exact visualFromArtin_factor M Y Z hsplit b a
  exact DFunLike.congr_fun h a

/-- The visual splitting is an isomorphism with the genuine injective
amalgamated free product of the two standard subgroups. -/
noncomputable def visualArtinEquiv (hsplit : IsVisualSplit M Y Z) :
    Artin M ≃* VisualAmalgam M Y Z where
  toFun := visualFromArtin M Y Z hsplit
  invFun := visualToArtin M Y Z
  left_inv := visualToArtin_from M Y Z hsplit
  right_inv := visualFromArtin_to M Y Z hsplit
  map_mul' := map_mul _

end HarmonicArtin.ParabolicIntersections

end OAI
