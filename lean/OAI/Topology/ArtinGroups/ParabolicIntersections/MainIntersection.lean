import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalReduction
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeInvisibleFactor
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeInitialStabilizer
import OAI.Topology.ArtinGroups.ParabolicIntersections.RankReduction

namespace OAI

/-!
# The main intersection theorems of paper 082-03

The hypotheses are exactly the published inputs documented in
`MeshNilpotence`, `FoldingGcdInput`, `AcyclicTwistInput`, and
`RelativeInitialStabilizer`. All relative-height, positive-height,
stabilizer-containment and rank-induction arguments are proved in this
local development; none of those new assertions is a hypothesis here.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- Only the published general mesh-algebra, admissible-folding and
acyclic-evaluation facts; see the individual definitions for exact sources. -/
structure PublishedSphericalInputs : Prop where
  mesh : ∀ Y : Set S, IsSpherical M Y →
    MeshNilpotent (fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M)
      (coxeterFusionEdge_symm M)) (fusionColorRegion (fusionLabelSize M) (Sum.inl '' Y))
  folding : ∀ (Y : Set S) (hY : IsSpherical M Y), PublishedFoldingGcd M Y hY
  acyclic : PublishedAcyclicTwist (fusionQuiver (fusionLabelSize M)
    (coxeterFusionEdge M) (coxeterFusionEdge_symm M))

/-- Theorem 8.2 on the actual pointed family with an unoperated frame. -/
theorem pointed_relative_stabilizers (hPub : PublishedSphericalInputs M)
    (f : S) (Y : Set S) (hf : f ∉ Y) (x : Artin M)
    (hx : x ∈ artinParabolic M {f}ᶜ) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      relativeStabilizer M (pointedInitial M f) Y x = conjugate c⁻¹ (artinParabolic M R) := by
  apply relativeStabilizers_of_reductions_on M (pointedInitial M f) {f}ᶜ _ Y
    (by intro s hs hsf; exact hf (hsf ▸ hs)) x hx
  intro D hD z hz
  have hfD : f ∉ D := fun h => hD h rfl
  by_cases hDs : IsSpherical M D
  · exact spherical_reduction M f D hDs hfD (hPub.folding D hDs)
      (hPub.mesh D hDs) hPub.acyclic z hz
  · exact relative_nonspherical_reduction M f hfD hz hDs

section Relative
local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder
variable (X : Set S)
local notation "N" => relativeMatrix M X

omit [Fintype S] [LinearOrder S] in
private lemma relative_comap_standard (hEmb : VanDerLekRelativeEmbedding M X) (Y : Set S) :
    (artinParabolic N (Sum.inl '' Y)).comap (relativeArtinHom M X) = artinParabolic M Y := by
  rw [← relativeArtinHom_parabolic]
  exact Subgroup.comap_map_eq_self_of_injective hEmb.injective _

omit [Fintype S] [LinearOrder S] in
private lemma relative_comap_conjugate (c : Artin M) (P : Subgroup (Artin N)) :
    (conjugate (relativeArtinHom M X c) P).comap (relativeArtinHom M X) =
      conjugate c (P.comap (relativeArtinHom M X)) := by
  ext a
  simp only [Subgroup.mem_comap,mem_conjugate,map_mul,map_inv]

/-- The stronger inside-parabolic form, with its conjugator inside the
acting parabolic. This is the result used by the arbitrary-family theorem. -/
theorem inside_intersection_at
    (hEmb : VanDerLekRelativeEmbedding M X) (hPub : PublishedSphericalInputs N)
    (Y : Set S) (g : Artin M) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      artinParabolic M Y ⊓ conjugate g (artinParabolic M X) =
        conjugate c (artinParabolic M R) := by
  let F := relativeArtinHom M X
  have hg : F g ∈ artinParabolic N {(.inr () : S⊕Unit)}ᶜ := by
    apply standard_mono N (X := Set.range (Sum.inl : S → S⊕Unit))
      (by rintro a ⟨s,rfl⟩; simp)
    rw [← Set.image_univ, ← relativeArtinHom_parabolic]
    exact ⟨g,by rw [standard_univ]; trivial,rfl⟩
  obtain ⟨R,c,hR,hc,he⟩ := pointed_relative_stabilizers N hPub (.inr ()) (Sum.inl '' Y)
    (by simp) (F g) hg
  rw [← relativeArtinHom_parabolic M X Y] at hc
  obtain ⟨b,hb,hbc⟩ := hc
  let D : Set S := Sum.inl ⁻¹' R
  have hD : D ⊆ Y := by
    intro s hs
    obtain ⟨t,ht,hte⟩ := hR hs
    exact Sum.inl.inj hte ▸ ht
  have hRD : R = Sum.inl '' D := by
    ext a
    constructor
    · intro ha
      obtain ⟨s,hs,rfl⟩ := hR ha
      exact ⟨s,ha,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      exact hs
  have hleft : (relativeStabilizer N (pointedInitial N (.inr ())) (Sum.inl '' Y) (F g)).comap F =
      relativeStabilizer M (relativeInitial M X) Y g := by
    unfold relativeStabilizer
    rw [Subgroup.comap_inf,relative_comap_standard M X hEmb Y]
    rfl
  have he' := congrArg (Subgroup.comap F) he
  rw [hleft,hRD,←hbc,←map_inv,relative_comap_conjugate,
    relative_comap_standard M X hEmb D] at he'
  refine ⟨D,b⁻¹,hD,(artinParabolic M Y).inv_mem hb,?_⟩
  have hinit := relative_initial_stabilizer M X hEmb
  have hconj := conjugate_stabilizer M (relativeInitial M X) g 1
  simp only [one_smul,_root_.mul_one,hinit] at hconj
  simpa only [relativeStabilizer,←hconj] using he'
end Relative

local instance : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

/-- The entire inside-parabolic statement, conditional solely on published inputs. -/
theorem inside_intersection
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X)) :
    InsideIntersectionProperty M := fun X Y g => inside_intersection_at M X (hEmb X) (hPub X) Y g

/-- Theorem 1.1, including arbitrary nonspherical types and infinite labels. -/
theorem parabolic_intersections
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X))
    (X Y : Set S) (g h : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) :=
  pairwise_of_inside M (inside_intersection M hEmb hPub) X Y g h

/-- Corollary 1.2: arbitrary intersections and the sharp rank subfamily bound. -/
theorem arbitrary_parabolic_intersections
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X))
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F) :=
  arbitrary_intersections_of_inside M (inside_intersection M hEmb hPub) F hF

/-- Corollary 1.2: every subset has a unique smallest parabolic closure. -/
theorem parabolic_closure
    (hEmb : ∀ X : Set S, VanDerLekRelativeEmbedding M X)
    (hPub : ∀ X : Set S, PublishedSphericalInputs (relativeMatrix M X))
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q :=
  parabolic_closure_of_inside M (inside_intersection M hEmb hPub) E

end HarmonicArtin.ParabolicIntersections

end OAI
