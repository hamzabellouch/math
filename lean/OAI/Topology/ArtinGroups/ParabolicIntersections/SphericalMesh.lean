import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshQuiverAlgebra
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusionRange
import OAI.Topology.ArtinGroups.Harmonic.SphericalFoldedMatrix

namespace OAI

/-! Discharging the finite spherical mesh input for the actual fusion quiver. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => (fun Y : Set S => fusionColorRegion (V := S⊕Unit) m (Sum.inl '' Y))

noncomputable def sphericalRegionEquiv (Y : Set S) :
    (Y × FusionLabel m) ≃ U Y :=
  (Equiv.ofInjective (unfoldedInclusion M Y) (unfoldedInclusion_injective M Y)).trans
    (Set.equivOfEq (unfoldedInclusion_range M Y))

omit [Fintype S] in
lemma sphericalRegionEquiv_val (Y : Set S) (a : Y × FusionLabel m) :
    (sphericalRegionEquiv M Y a).val=unfoldedInclusion M Y a := rfl

omit [Fintype S] in
lemma sphericalRegionEquiv_symm_val (Y : Set S) (u : U Y) :
    unfoldedInclusion M Y ((sphericalRegionEquiv M Y).symm u)=u.val := by
  exact congrArg Subtype.val ((sphericalRegionEquiv M Y).apply_symm_apply u)

lemma spherical_mesh_simple (Y : Set S) (hY : IsSpherical M Y) : QuiverSimpleOn Q (U Y) := by
  rintro ⟨⟨s,t⟩,i⟩ ⟨⟨s',t'⟩,j⟩ hs ht he₁ he₂
  change s=s' at he₁
  change t=t' at he₂
  subst s'
  subst t'
  change s∈U Y at hs
  change t∈U Y at ht
  obtain ⟨a,ha⟩ : ∃ a : Y × FusionLabel m, unfoldedInclusion M Y a=s := by
    change s∈Set.range (unfoldedInclusion M Y)
    rw [unfoldedInclusion_range M Y]
    exact hs
  obtain ⟨b,hb⟩ : ∃ b : Y × FusionLabel m, unfoldedInclusion M Y b=t := by
    change t∈Set.range (unfoldedInclusion M Y)
    rw [unfoldedInclusion_range M Y]
    exact ht
  have hmult : (coxeterFusionEdge M s.1 t.1).multiplicity m s.2 t.2≤1 := by
    rw [←ha,←hb]
    exact spherical_fusion_multiplicity_le_one M Y hY a.1 b.1 a.2 b.2
  have hi := i.isLt
  have hj := j.isLt
  change i.val<(coxeterFusionEdge M s.1 t.1).multiplicity m s.2 t.2 at hi
  change j.val<(coxeterFusionEdge M s.1 t.1).multiplicity m s.2 t.2 at hj
  congr 1
  apply Fin.ext
  omega

lemma fusion_mesh_arrow_exists (u v : FusionVertex (V := S⊕Unit) m) :
    (∃ a, (Q).source a=u ∧ (Q).target a=v) ↔
      0<(coxeterFusionEdge M u.1 v.1).multiplicity m u.2 v.2 := by
  constructor
  · rintro ⟨⟨⟨s,t⟩,i⟩,hs,ht⟩
    change s=u at hs
    change t=v at ht
    subst s
    subst t
    exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  · intro h
    exact ⟨⟨(u,v),⟨0,h⟩⟩,rfl,rfl⟩

theorem spherical_mesh_cartan (Y : Set S) (hY : IsSpherical M Y) :
    let _ : DecidableEq (U Y) := Classical.decEq _
    ((2 : ℝ) • (1 : Matrix (U Y) (U Y) ℝ)-
      (meshQuiverGraph Q (U Y) (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).adjMatrix ℝ).PosDef := by
  let : DecidableEq (U Y) := Classical.decEq _
  let e := sphericalRegionEquiv M Y
  have hp := (spherical_unfolded_posDef M Y hY).submatrix e.symm.injective
  convert hp using 1
  ext u v
  let a := e.symm u
  let b := e.symm v
  have hu : unfoldedInclusion M Y a=u.val := sphericalRegionEquiv_symm_val M Y u
  have hv : unfoldedInclusion M Y b=v.val := sphericalRegionEquiv_symm_val M Y v
  have hadj : (meshQuiverGraph Q (U Y)
      (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).Adj u v ↔
      0<(coxeterFusionEdge M (.inl a.1) (.inl b.1)).multiplicity m a.2 b.2 := by
    change (∃ c, (Q).source c=u.val ∧ (Q).target c=v.val) ↔ _
    rw [←hu,←hv,fusion_mesh_arrow_exists]
  have hn := spherical_fusion_multiplicity_le_one M Y hY a.1 b.1 a.2 b.2
  change ((2 : ℝ) • (1 : Matrix (U Y) (U Y) ℝ)-
      (meshQuiverGraph Q (U Y) (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).adjMatrix ℝ) u v=
    fusionUnfoldedCartan m (fun i j : Y => coxeterFusionEdge M (.inl i) (.inl j)) a b
  by_cases huv : u=v
  · subst v
    change ((2 : ℝ) • (1 : Matrix (U Y) (U Y) ℝ)-
      (meshQuiverGraph Q (U Y) (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).adjMatrix ℝ) u u=
      fusionUnfoldedCartan m (fun i j : Y => coxeterFusionEdge M (.inl i) (.inl j)) a a
    simp [fusionUnfoldedCartan,coxeterFusionEdge_diag,FusionEdge.multiplicity]
  · have hab : a≠b := fun h => huv (e.symm.injective h)
    have hm : (coxeterFusionEdge M (.inl a.1) (.inl b.1)).multiplicity m a.2 b.2=0 ∨
        (coxeterFusionEdge M (.inl a.1) (.inl b.1)).multiplicity m a.2 b.2=1 := by omega
    rcases hm with hm|hm <;>
      simp [SimpleGraph.adjMatrix_apply,hadj,hm,huv,
        fusionUnfoldedCartan,hab]

/-- The finite-Dynkin mesh nilpotence input for every spherical set of
colors, proved for the precise ambient fusion-quiver relations. -/
theorem spherical_mesh_nilpotent (Y : Set S) (hY : IsSpherical M Y) : MeshNilpotent Q (U Y) := by
  apply meshNilpotent_of_positive_cartan Q (U Y)
    (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M)) (spherical_mesh_simple M Y hY)
  exact spherical_mesh_cartan M Y hY

end HarmonicArtin.ParabolicIntersections

end OAI
