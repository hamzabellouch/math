import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalCommonExtension
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedSphericalNoChain
import OAI.Topology.ArtinGroups.ParabolicIntersections.ProperPositiveSupport
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusionRange

namespace OAI

/-! One proper support controls every bounded-height positive continuation. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

/-- Lemma 7.6 for the actual pointed family. Both conditional inputs
concern published positive-monoid or mesh-algebra results. -/
theorem spherical_proper_positive_support (Y : Set S) (hY : IsSpherical M Y)
    (hf : f ∉ Y) (hGcd : PublishedFoldingGcd M Y hY)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (x : Artin M) (hx : x ∈ artinParabolic M {f}ᶜ) (t : ℤ)
    (ht : ∀ L, ClassTestUpper Q (pointedFamily M f x L)
      (Set.range (unfoldedInclusion M Y)) t)
    (hnonzero : ∃ L, ¬ ∀ α ∈ Set.range (unfoldedInclusion M Y), ∀ l c,
      ClassTestExact Q α l c (pointedFamily M f x L)) :
    ∃ p : PositiveArtin (restrictedMatrix M Y),
      (∀ L, ClassTestUpper Q (restrictedPointedFamily M f Y x (positiveToArtin _ p) L)
        (Set.range (unfoldedInclusion M Y)) t) ∧
      ∃ J : Set Y, J ⊂ Set.univ ∧ ∀ b : PositiveArtin (restrictedMatrix M Y),
        (∀ L, ClassTestUpper Q
          (restrictedPointedFamily M f Y x (positiveToArtin _ (b*p)) L)
          (Set.range (unfoldedInclusion M Y)) t) → positiveSupport _ b ⊆ J := by
  let N := restrictedMatrix M Y
  let fpos := positiveToArtin N
  let P : PositiveArtin N → Prop := fun p => ∀ L,
    ClassTestUpper Q (restrictedPointedFamily M f Y x (fpos p) L)
      (Set.range (unfoldedInclusion M Y)) t
  have hOne : P 1 := by
    simpa only [P, fpos, map_one, restrictedPointedFamily, _root_.one_mul] using ht
  have hpair (a b : PositiveArtin N) (ha : P a) (hb : P b) :
      ∃ c, P c ∧ (∃ p, c=p*a) ∧ ∃ q, c=q*b := by
    obtain ⟨p,q,he,hcap⟩ := spherical_common_extension M f Y hY hGcd x (fpos a) (fpos b) t ha hb
    refine ⟨p*a, ?_, ⟨p,rfl⟩, q, ?_⟩
    · simpa only [P, fpos, map_mul] using hcap
    · apply spherical_positiveToArtin_injective M Y hY
      simpa only [fpos,map_mul] using he
  have hcommon (F : Finset (PositiveArtin N)) (hF : ∀ a ∈ F, P a) :
      ∃ c, P c ∧ ∀ a ∈ F, ∃ q, c=q*a := by
    induction F using Finset.induction_on with
    | empty => exact ⟨1,hOne,by simp⟩
    | @insert a F ha ih =>
      obtain ⟨c,hc,hca⟩ := ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      obtain ⟨d,hd,⟨r,hr⟩,s,hs⟩ := hpair c a hc (hF a (Finset.mem_insert_self _ _))
      refine ⟨d,hd,?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨s,hs⟩
      · obtain ⟨q,hq⟩ := hca b hb
        exact ⟨r*q,by rw [hr,hq,_root_.mul_assoc]⟩
  apply proper_positive_support N
    (fun a b c h => spherical_positiveToArtin_injective M Y hY (by
      apply mul_right_cancel (b := fpos c)
      simpa only [map_mul] using congrArg fpos h)) P hOne hcommon
  intro a b ha hPa hab hsupp
  let u (n : ℕ) : List Y := (positive_word_surjective N (b n)).choose
  have hu (n : ℕ) : wordPositive N (u n)=b n := (positive_word_surjective N (b n)).choose_spec
  let z (n : ℕ) := restrictedArtinHom M Y (fpos (a n))*x
  have hz0 : z 0=x := by simp only [z,ha,map_one,_root_.one_mul]
  obtain ⟨L,hL⟩ := hnonzero
  apply pointed_no_bounded_complete_positive_chain M f Y hf hmesh z
    (fun n => (u n).map Subtype.val) (hz0.symm ▸ hx)
  · intro n
    dsimp only [z]
    rw [hab n,map_mul,map_mul,←hu n,positiveToArtin_word,restrictedArtinHom_word,_root_.mul_assoc]
  · intro n s
    constructor
    · intro hs
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact i.property
    · intro hs
      refine List.mem_map.mpr ⟨⟨s,hs⟩,?_,rfl⟩
      have hi : (⟨s,hs⟩ : Y) ∈ positiveSupport N (b n) := by rw [hsupp n]; trivial
      rwa [←hu n,positiveSupport_word] at hi
  · simpa only [hz0,←unfoldedInclusion_range M Y] using hL
  · intro n
    simpa only [z,restrictedPointedFamily,unfoldedInclusion_range M Y] using hPa n L

end HarmonicArtin.ParabolicIntersections

end OAI
